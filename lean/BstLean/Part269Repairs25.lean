import BstLean.Part269Rows25
import BstLean.Part269RepairCommon
namespace BstLean.Part269
open Real Set BstLean.Part255 BstLean.Part263 BstLean.Part264
theorem repair12975Cells (j : Fin 43) :
    0 ≤ (scalarRow12975.table (sourceIndex j)).upper ∧
    (scalarRow12975.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12975.table (sourceIndex j)).centre) /
      (scalarRow12975.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12975.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12975,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12975,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12975,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12975,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12975,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12975,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12975,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12975,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12975,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12975,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12975,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12975,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12975,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12975,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12975,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12975,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12975,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12975,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12975,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12975,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12975,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12975,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12975,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12975,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12975,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12975,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12975,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12975,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12975,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12975,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12975,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12975,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12975,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12975,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12975,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12975,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12975,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12975,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12975,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12975,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12975,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12975,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12975,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12975,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12975,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12975,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12975,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12975,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12975,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12975,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12975,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12975,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12975,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12975,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12975,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12975,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12975,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12975,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12975,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12975,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12975,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12975,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12975,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12975,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12975,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12975,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12975,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12975,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12975,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12975,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12975,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12975,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12975,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12975,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12975,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12975,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12975,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12975,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12975,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12975,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12975,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12975,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12975,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12975,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12975,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12975,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12975 : FrameRepair 12975 scalarRow12975 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12975Cells j).1 (repair12975Cells j).2.1
  endpoint_upper := fun j => ((repair12975Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12975Cells j).2.2

theorem repair12976Cells (j : Fin 43) :
    0 ≤ (scalarRow12976.table (sourceIndex j)).upper ∧
    (scalarRow12976.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12976.table (sourceIndex j)).centre) /
      (scalarRow12976.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12976.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12976,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12976,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12976,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12976,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12976,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12976,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12976,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12976,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12976,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12976,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12976,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12976,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12976,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12976,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12976,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12976,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12976,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12976,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12976,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12976,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12976,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12976,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12976,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12976,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12976,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12976,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12976,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12976,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12976,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12976,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12976,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12976,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12976,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12976,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12976,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12976,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12976,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12976,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12976,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12976,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12976,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12976,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12976,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12976,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12976,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12976,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12976,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12976,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12976,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12976,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12976,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12976,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12976,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12976,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12976,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12976,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12976,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12976,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12976,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12976,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12976,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12976,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12976,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12976,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12976,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12976,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12976,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12976,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12976,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12976,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12976,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12976,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12976,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12976,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12976,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12976,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12976,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12976,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12976,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12976,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12976,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12976,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12976,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12976,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12976,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12976,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12976 : FrameRepair 12976 scalarRow12976 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12976Cells j).1 (repair12976Cells j).2.1
  endpoint_upper := fun j => ((repair12976Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12976Cells j).2.2

theorem repair12977Cells (j : Fin 43) :
    0 ≤ (scalarRow12977.table (sourceIndex j)).upper ∧
    (scalarRow12977.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12977.table (sourceIndex j)).centre) /
      (scalarRow12977.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12977.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12977,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12977,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12977,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12977,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12977,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12977,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12977,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12977,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12977,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12977,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12977,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12977,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12977,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12977,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12977,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12977,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12977,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12977,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12977,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12977,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12977,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12977,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12977,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12977,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12977,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12977,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12977,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12977,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12977,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12977,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12977,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12977,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12977,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12977,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12977,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12977,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12977,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12977,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12977,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12977,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12977,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12977,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12977,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12977,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12977,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12977,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12977,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12977,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12977,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12977,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12977,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12977,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12977,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12977,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12977,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12977,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12977,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12977,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12977,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12977,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12977,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12977,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12977,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12977,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12977,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12977,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12977,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12977,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12977,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12977,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12977,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12977,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12977,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12977,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12977,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12977,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12977,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12977,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12977,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12977,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12977,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12977,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12977,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12977,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12977,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12977,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12977 : FrameRepair 12977 scalarRow12977 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12977Cells j).1 (repair12977Cells j).2.1
  endpoint_upper := fun j => ((repair12977Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12977Cells j).2.2

theorem repair12978Cells (j : Fin 43) :
    0 ≤ (scalarRow12978.table (sourceIndex j)).upper ∧
    (scalarRow12978.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12978.table (sourceIndex j)).centre) /
      (scalarRow12978.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12978.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12978,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12978,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12978,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12978,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12978,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12978,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12978,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12978,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12978,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12978,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12978,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12978,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12978,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12978,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12978,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12978,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12978,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12978,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12978,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12978,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12978,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12978,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12978,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12978,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12978,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12978,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12978,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12978,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12978,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12978,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12978,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12978,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12978,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12978,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12978,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12978,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12978,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12978,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12978,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12978,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12978,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12978,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12978,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12978,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12978,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12978,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12978,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12978,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12978,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12978,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12978,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12978,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12978,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12978,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12978,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12978,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12978,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12978,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12978,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12978,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12978,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12978,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12978,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12978,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12978,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12978,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12978,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12978,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12978,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12978,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12978,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12978,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12978,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12978,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12978,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12978,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12978,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12978,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12978,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12978,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12978,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12978,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12978,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12978,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12978,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12978,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12978 : FrameRepair 12978 scalarRow12978 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12978Cells j).1 (repair12978Cells j).2.1
  endpoint_upper := fun j => ((repair12978Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12978Cells j).2.2

theorem repair12979Cells (j : Fin 43) :
    0 ≤ (scalarRow12979.table (sourceIndex j)).upper ∧
    (scalarRow12979.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12979.table (sourceIndex j)).centre) /
      (scalarRow12979.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12979.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12979,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12979,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12979,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12979,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12979,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12979,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12979,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12979,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12979,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12979,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12979,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12979,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12979,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12979,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12979,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12979,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12979,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12979,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12979,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12979,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12979,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12979,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12979,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12979,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12979,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12979,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12979,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12979,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12979,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12979,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12979,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12979,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12979,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12979,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12979,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12979,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12979,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12979,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12979,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12979,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12979,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12979,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12979,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12979,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12979,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12979,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12979,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12979,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12979,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12979,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12979,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12979,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12979,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12979,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12979,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12979,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12979,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12979,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12979,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12979,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12979,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12979,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12979,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12979,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12979,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12979,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12979,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12979,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12979,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12979,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12979,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12979,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12979,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12979,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12979,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12979,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12979,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12979,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12979,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12979,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12979,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12979,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12979,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12979,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12979,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12979,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12979 : FrameRepair 12979 scalarRow12979 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12979Cells j).1 (repair12979Cells j).2.1
  endpoint_upper := fun j => ((repair12979Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12979Cells j).2.2

theorem repair12980Cells (j : Fin 43) :
    0 ≤ (scalarRow12980.table (sourceIndex j)).upper ∧
    (scalarRow12980.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12980.table (sourceIndex j)).centre) /
      (scalarRow12980.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12980.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12980,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12980,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12980,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12980,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12980,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12980,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12980,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12980,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12980,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12980,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12980,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12980,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12980,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12980,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12980,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12980,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12980,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12980,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12980,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12980,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12980,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12980,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12980,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12980,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12980,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12980,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12980,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12980,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12980,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12980,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12980,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12980,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12980,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12980,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12980,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12980,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12980,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12980,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12980,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12980,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12980,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12980,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12980,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12980,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12980,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12980,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12980,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12980,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12980,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12980,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12980,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12980,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12980,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12980,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12980,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12980,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12980,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12980,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12980,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12980,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12980,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12980,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12980,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12980,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12980,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12980,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12980,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12980,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12980,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12980,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12980,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12980,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12980,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12980,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12980,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12980,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12980,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12980,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12980,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12980,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12980,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12980,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12980,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12980,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12980,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12980,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12980 : FrameRepair 12980 scalarRow12980 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12980Cells j).1 (repair12980Cells j).2.1
  endpoint_upper := fun j => ((repair12980Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12980Cells j).2.2

theorem repair12981Cells (j : Fin 43) :
    0 ≤ (scalarRow12981.table (sourceIndex j)).upper ∧
    (scalarRow12981.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12981.table (sourceIndex j)).centre) /
      (scalarRow12981.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12981.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12981,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12981,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12981,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12981,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12981,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12981,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12981,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12981,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12981,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12981,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12981,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12981,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12981,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12981,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12981,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12981,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12981,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12981,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12981,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12981,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12981,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12981,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12981,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12981,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12981,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12981,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12981,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12981,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12981,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12981,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12981,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12981,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12981,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12981,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12981,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12981,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12981,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12981,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12981,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12981,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12981,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12981,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12981,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12981,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12981,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12981,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12981,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12981,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12981,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12981,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12981,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12981,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12981,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12981,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12981,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12981,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12981,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12981,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12981,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12981,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12981,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12981,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12981,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12981,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12981,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12981,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12981,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12981,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12981,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12981,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12981,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12981,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12981,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12981,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12981,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12981,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12981,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12981,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12981,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12981,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12981,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12981,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12981,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12981,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12981,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12981,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12981 : FrameRepair 12981 scalarRow12981 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12981Cells j).1 (repair12981Cells j).2.1
  endpoint_upper := fun j => ((repair12981Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12981Cells j).2.2

theorem repair12982Cells (j : Fin 43) :
    0 ≤ (scalarRow12982.table (sourceIndex j)).upper ∧
    (scalarRow12982.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12982.table (sourceIndex j)).centre) /
      (scalarRow12982.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12982.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12982,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12982,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12982,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12982,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12982,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12982,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12982,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12982,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12982,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12982,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12982,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12982,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12982,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12982,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12982,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12982,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12982,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12982,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12982,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12982,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12982,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12982,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12982,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12982,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12982,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12982,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12982,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12982,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12982,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12982,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12982,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12982,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12982,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12982,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12982,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12982,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12982,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12982,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12982,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12982,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12982,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12982,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12982,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12982,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12982,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12982,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12982,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12982,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12982,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12982,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12982,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12982,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12982,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12982,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12982,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12982,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12982,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12982,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12982,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12982,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12982,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12982,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12982,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12982,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12982,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12982,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12982,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12982,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12982,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12982,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12982,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12982,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12982,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12982,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12982,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12982,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12982,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12982,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12982,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12982,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12982,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12982,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12982,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12982,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12982,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12982,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12982 : FrameRepair 12982 scalarRow12982 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12982Cells j).1 (repair12982Cells j).2.1
  endpoint_upper := fun j => ((repair12982Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12982Cells j).2.2

theorem repair12983Cells (j : Fin 43) :
    0 ≤ (scalarRow12983.table (sourceIndex j)).upper ∧
    (scalarRow12983.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12983.table (sourceIndex j)).centre) /
      (scalarRow12983.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12983.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12983,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12983,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12983,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12983,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12983,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12983,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12983,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12983,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12983,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12983,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12983,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12983,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12983,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12983,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12983,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12983,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12983,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12983,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12983,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12983,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12983,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12983,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12983,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12983,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12983,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12983,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12983,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12983,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12983,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12983,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12983,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12983,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12983,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12983,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12983,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12983,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12983,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12983,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12983,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12983,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12983,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12983,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12983,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12983,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12983,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12983,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12983,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12983,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12983,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12983,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12983,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12983,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12983,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12983,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12983,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12983,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12983,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12983,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12983,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12983,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12983,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12983,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12983,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12983,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12983,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12983,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12983,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12983,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12983,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12983,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12983,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12983,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12983,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12983,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12983,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12983,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12983,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12983,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12983,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12983,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12983,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12983,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12983,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12983,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12983,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12983,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12983 : FrameRepair 12983 scalarRow12983 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12983Cells j).1 (repair12983Cells j).2.1
  endpoint_upper := fun j => ((repair12983Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12983Cells j).2.2

theorem repair12984Cells (j : Fin 43) :
    0 ≤ (scalarRow12984.table (sourceIndex j)).upper ∧
    (scalarRow12984.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12984.table (sourceIndex j)).centre) /
      (scalarRow12984.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12984.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12984,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12984,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12984,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12984,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12984,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12984,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12984,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12984,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12984,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12984,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12984,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12984,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12984,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12984,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12984,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12984,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12984,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12984,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12984,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12984,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12984,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12984,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12984,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12984,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12984,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12984,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12984,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12984,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12984,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12984,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12984,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12984,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12984,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12984,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12984,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12984,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12984,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12984,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12984,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12984,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12984,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12984,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12984,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12984,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12984,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12984,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12984,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12984,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12984,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12984,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12984,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12984,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12984,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12984,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12984,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12984,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12984,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12984,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12984,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12984,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12984,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12984,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12984,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12984,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12984,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12984,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12984,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12984,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12984,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12984,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12984,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12984,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12984,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12984,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12984,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12984,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12984,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12984,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12984,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12984,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12984,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12984,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12984,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12984,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12984,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12984,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12984 : FrameRepair 12984 scalarRow12984 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12984Cells j).1 (repair12984Cells j).2.1
  endpoint_upper := fun j => ((repair12984Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12984Cells j).2.2

theorem repair12985Cells (j : Fin 43) :
    0 ≤ (scalarRow12985.table (sourceIndex j)).upper ∧
    (scalarRow12985.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12985.table (sourceIndex j)).centre) /
      (scalarRow12985.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12985.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12985,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12985,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12985,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12985,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12985,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12985,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12985,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12985,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12985,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12985,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12985,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12985,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12985,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12985,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12985,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12985,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12985,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12985,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12985,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12985,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12985,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12985,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12985,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12985,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12985,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12985,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12985,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12985,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12985,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12985,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12985,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12985,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12985,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12985,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12985,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12985,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12985,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12985,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12985,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12985,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12985,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12985,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12985,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12985,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12985,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12985,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12985,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12985,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12985,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12985,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12985,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12985,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12985,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12985,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12985,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12985,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12985,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12985,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12985,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12985,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12985,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12985,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12985,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12985,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12985,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12985,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12985,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12985,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12985,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12985,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12985,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12985,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12985,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12985,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12985,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12985,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12985,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12985,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12985,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12985,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12985,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12985,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12985,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12985,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12985,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12985,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12985 : FrameRepair 12985 scalarRow12985 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12985Cells j).1 (repair12985Cells j).2.1
  endpoint_upper := fun j => ((repair12985Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12985Cells j).2.2

theorem repair12986Cells (j : Fin 43) :
    0 ≤ (scalarRow12986.table (sourceIndex j)).upper ∧
    (scalarRow12986.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12986.table (sourceIndex j)).centre) /
      (scalarRow12986.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12986.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12986,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12986,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12986,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12986,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12986,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12986,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12986,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12986,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12986,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12986,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12986,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12986,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12986,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12986,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12986,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12986,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12986,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12986,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12986,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12986,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12986,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12986,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12986,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12986,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12986,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12986,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12986,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12986,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12986,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12986,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12986,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12986,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12986,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12986,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12986,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12986,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12986,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12986,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12986,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12986,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12986,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12986,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12986,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12986,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12986,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12986,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12986,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12986,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12986,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12986,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12986,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12986,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12986,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12986,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12986,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12986,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12986,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12986,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12986,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12986,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12986,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12986,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12986,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12986,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12986,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12986,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12986,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12986,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12986,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12986,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12986,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12986,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12986,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12986,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12986,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12986,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12986,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12986,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12986,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12986,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12986,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12986,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12986,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12986,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12986,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12986,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12986 : FrameRepair 12986 scalarRow12986 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12986Cells j).1 (repair12986Cells j).2.1
  endpoint_upper := fun j => ((repair12986Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12986Cells j).2.2

theorem repair12987Cells (j : Fin 43) :
    0 ≤ (scalarRow12987.table (sourceIndex j)).upper ∧
    (scalarRow12987.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12987.table (sourceIndex j)).centre) /
      (scalarRow12987.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12987.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12987,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12987,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12987,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12987,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12987,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12987,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12987,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12987,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12987,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12987,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12987,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12987,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12987,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12987,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12987,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12987,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12987,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12987,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12987,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12987,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12987,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12987,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12987,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12987,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12987,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12987,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12987,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12987,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12987,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12987,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12987,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12987,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12987,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12987,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12987,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12987,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12987,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12987,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12987,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12987,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12987,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12987,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12987,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12987,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12987,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12987,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12987,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12987,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12987,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12987,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12987,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12987,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12987,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12987,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12987,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12987,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12987,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12987,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12987,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12987,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12987,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12987,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12987,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12987,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12987,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12987,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12987,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12987,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12987,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12987,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12987,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12987,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12987,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12987,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12987,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12987,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12987,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12987,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12987,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12987,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12987,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12987,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12987,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12987,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12987,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12987,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12987 : FrameRepair 12987 scalarRow12987 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12987Cells j).1 (repair12987Cells j).2.1
  endpoint_upper := fun j => ((repair12987Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12987Cells j).2.2

theorem repair12988Cells (j : Fin 43) :
    0 ≤ (scalarRow12988.table (sourceIndex j)).upper ∧
    (scalarRow12988.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12988.table (sourceIndex j)).centre) /
      (scalarRow12988.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12988.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12988,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12988,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12988,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12988,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12988,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12988,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12988,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12988,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12988,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12988,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12988,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12988,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12988,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12988,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12988,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12988,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12988,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12988,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12988,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12988,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12988,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12988,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12988,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12988,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12988,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12988,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12988,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12988,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12988,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12988,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12988,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12988,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12988,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12988,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12988,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12988,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12988,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12988,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12988,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12988,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12988,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12988,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12988,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12988,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12988,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12988,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12988,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12988,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12988,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12988,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12988,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12988,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12988,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12988,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12988,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12988,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12988,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12988,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12988,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12988,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12988,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12988,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12988,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12988,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12988,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12988,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12988,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12988,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12988,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12988,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12988,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12988,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12988,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12988,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12988,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12988,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12988,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12988,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12988,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12988,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12988,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12988,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12988,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12988,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12988,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12988,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12988 : FrameRepair 12988 scalarRow12988 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12988Cells j).1 (repair12988Cells j).2.1
  endpoint_upper := fun j => ((repair12988Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12988Cells j).2.2

theorem repair12989Cells (j : Fin 43) :
    0 ≤ (scalarRow12989.table (sourceIndex j)).upper ∧
    (scalarRow12989.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12989.table (sourceIndex j)).centre) /
      (scalarRow12989.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12989.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12989,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12989,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12989,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12989,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12989,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12989,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12989,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12989,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12989,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12989,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12989,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12989,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12989,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12989,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12989,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12989,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12989,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12989,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12989,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12989,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12989,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12989,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12989,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12989,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12989,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12989,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12989,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12989,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12989,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12989,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12989,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12989,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12989,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12989,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12989,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12989,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12989,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12989,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12989,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12989,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12989,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12989,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12989,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12989,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12989,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12989,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12989,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12989,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12989,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12989,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12989,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12989,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12989,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12989,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12989,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12989,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12989,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12989,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12989,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12989,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12989,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12989,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12989,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12989,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12989,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12989,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12989,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12989,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12989,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12989,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12989,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12989,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12989,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12989,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12989,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12989,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12989,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12989,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12989,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12989,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12989,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12989,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12989,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12989,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12989,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12989,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12989 : FrameRepair 12989 scalarRow12989 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12989Cells j).1 (repair12989Cells j).2.1
  endpoint_upper := fun j => ((repair12989Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12989Cells j).2.2

theorem repair12990Cells (j : Fin 43) :
    0 ≤ (scalarRow12990.table (sourceIndex j)).upper ∧
    (scalarRow12990.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12990.table (sourceIndex j)).centre) /
      (scalarRow12990.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12990.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12990,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12990,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12990,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12990,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12990,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12990,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12990,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12990,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12990,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12990,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12990,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12990,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12990,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12990,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12990,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12990,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12990,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12990,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12990,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12990,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12990,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12990,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12990,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12990,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12990,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12990,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12990,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12990,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12990,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12990,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12990,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12990,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12990,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12990,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12990,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12990,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12990,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12990,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12990,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12990,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12990,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12990,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12990,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12990,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12990,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12990,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12990,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12990,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12990,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12990,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12990,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12990,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12990,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12990,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12990,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12990,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12990,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12990,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12990,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12990,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12990,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12990,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12990,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12990,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12990,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12990,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12990,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12990,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12990,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12990,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12990,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12990,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12990,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12990,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12990,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12990,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12990,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12990,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12990,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12990,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12990,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12990,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12990,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12990,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12990,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12990,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12990 : FrameRepair 12990 scalarRow12990 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12990Cells j).1 (repair12990Cells j).2.1
  endpoint_upper := fun j => ((repair12990Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12990Cells j).2.2

theorem repair12991Cells (j : Fin 43) :
    0 ≤ (scalarRow12991.table (sourceIndex j)).upper ∧
    (scalarRow12991.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12991.table (sourceIndex j)).centre) /
      (scalarRow12991.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12991.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12991,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12991,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12991,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12991,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12991,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12991,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12991,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12991,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12991,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12991,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12991,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12991,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12991,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12991,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12991,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12991,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12991,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12991,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12991,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12991,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12991,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12991,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12991,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12991,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12991,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12991,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12991,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12991,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12991,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12991,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12991,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12991,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12991,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12991,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12991,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12991,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12991,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12991,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12991,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12991,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12991,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12991,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12991,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12991,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12991,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12991,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12991,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12991,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12991,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12991,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12991,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12991,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12991,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12991,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12991,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12991,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12991,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12991,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12991,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12991,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12991,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12991,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12991,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12991,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12991,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12991,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12991,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12991,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12991,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12991,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12991,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12991,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12991,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12991,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12991,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12991,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12991,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12991,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12991,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12991,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12991,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12991,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12991,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12991,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12991,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12991,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12991 : FrameRepair 12991 scalarRow12991 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12991Cells j).1 (repair12991Cells j).2.1
  endpoint_upper := fun j => ((repair12991Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12991Cells j).2.2

theorem repair12992Cells (j : Fin 43) :
    0 ≤ (scalarRow12992.table (sourceIndex j)).upper ∧
    (scalarRow12992.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12992.table (sourceIndex j)).centre) /
      (scalarRow12992.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12992.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12992,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12992,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12992,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12992,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12992,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12992,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12992,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12992,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12992,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12992,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12992,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12992,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12992,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12992,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12992,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12992,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12992,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12992,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12992,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12992,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12992,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12992,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12992,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12992,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12992,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12992,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12992,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12992,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12992,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12992,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12992,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12992,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12992,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12992,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12992,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12992,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12992,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12992,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12992,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12992,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12992,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12992,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12992,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12992,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12992,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12992,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12992,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12992,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12992,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12992,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12992,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12992,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12992,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12992,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12992,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12992,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12992,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12992,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12992,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12992,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12992,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12992,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12992,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12992,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12992,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12992,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12992,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12992,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12992,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12992,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12992,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12992,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12992,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12992,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12992,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12992,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12992,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12992,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12992,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12992,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12992,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12992,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12992,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12992,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12992,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12992,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12992 : FrameRepair 12992 scalarRow12992 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12992Cells j).1 (repair12992Cells j).2.1
  endpoint_upper := fun j => ((repair12992Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12992Cells j).2.2

theorem repair12993Cells (j : Fin 43) :
    0 ≤ (scalarRow12993.table (sourceIndex j)).upper ∧
    (scalarRow12993.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12993.table (sourceIndex j)).centre) /
      (scalarRow12993.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12993.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12993,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12993,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12993,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12993,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12993,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12993,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12993,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12993,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12993,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12993,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12993,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12993,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12993,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12993,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12993,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12993,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12993,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12993,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12993,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12993,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12993,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12993,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12993,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12993,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12993,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12993,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12993,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12993,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12993,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12993,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12993,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12993,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12993,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12993,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12993,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12993,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12993,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12993,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12993,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12993,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12993,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12993,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12993,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12993,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12993,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12993,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12993,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12993,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12993,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12993,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12993,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12993,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12993,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12993,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12993,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12993,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12993,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12993,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12993,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12993,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12993,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12993,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12993,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12993,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12993,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12993,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12993,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12993,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12993,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12993,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12993,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12993,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12993,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12993,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12993,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12993,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12993,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12993,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12993,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12993,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12993,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12993,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12993,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12993,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12993,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12993,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12993 : FrameRepair 12993 scalarRow12993 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12993Cells j).1 (repair12993Cells j).2.1
  endpoint_upper := fun j => ((repair12993Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12993Cells j).2.2

theorem repair12994Cells (j : Fin 43) :
    0 ≤ (scalarRow12994.table (sourceIndex j)).upper ∧
    (scalarRow12994.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12994.table (sourceIndex j)).centre) /
      (scalarRow12994.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12994.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12994,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12994,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12994,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12994,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12994,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12994,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12994,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12994,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12994,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12994,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12994,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12994,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12994,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12994,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12994,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12994,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12994,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12994,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12994,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12994,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12994,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12994,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12994,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12994,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12994,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12994,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12994,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12994,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12994,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12994,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12994,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12994,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12994,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12994,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12994,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12994,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12994,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12994,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12994,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12994,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12994,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12994,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12994,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12994,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12994,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12994,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12994,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12994,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12994,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12994,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12994,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12994,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12994,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12994,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12994,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12994,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12994,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12994,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12994,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12994,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12994,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12994,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12994,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12994,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12994,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12994,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12994,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12994,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12994,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12994,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12994,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12994,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12994,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12994,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12994,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12994,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12994,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12994,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12994,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12994,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12994,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12994,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12994,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12994,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12994,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12994,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12994 : FrameRepair 12994 scalarRow12994 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12994Cells j).1 (repair12994Cells j).2.1
  endpoint_upper := fun j => ((repair12994Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12994Cells j).2.2

theorem repair12995Cells (j : Fin 43) :
    0 ≤ (scalarRow12995.table (sourceIndex j)).upper ∧
    (scalarRow12995.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12995.table (sourceIndex j)).centre) /
      (scalarRow12995.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12995.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12995,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12995,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12995,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12995,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12995,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12995,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12995,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12995,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12995,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12995,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12995,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12995,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12995,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12995,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12995,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12995,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12995,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12995,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12995,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12995,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12995,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12995,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12995,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12995,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12995,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12995,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12995,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12995,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12995,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12995,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12995,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12995,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12995,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12995,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12995,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12995,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12995,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12995,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12995,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12995,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12995,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12995,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12995,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12995,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12995,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12995,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12995,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12995,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12995,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12995,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12995,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12995,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12995,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12995,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12995,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12995,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12995,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12995,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12995,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12995,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12995,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12995,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12995,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12995,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12995,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12995,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12995,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12995,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12995,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12995,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12995,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12995,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12995,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12995,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12995,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12995,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12995,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12995,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12995,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12995,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12995,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12995,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12995,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12995,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12995,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12995,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12995 : FrameRepair 12995 scalarRow12995 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12995Cells j).1 (repair12995Cells j).2.1
  endpoint_upper := fun j => ((repair12995Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12995Cells j).2.2

theorem repair12996Cells (j : Fin 43) :
    0 ≤ (scalarRow12996.table (sourceIndex j)).upper ∧
    (scalarRow12996.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12996.table (sourceIndex j)).centre) /
      (scalarRow12996.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12996.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12996,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12996,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12996,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12996,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12996,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12996,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12996,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12996,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12996,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12996,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12996,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12996,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12996,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12996,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12996,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12996,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12996,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12996,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12996,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12996,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12996,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12996,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12996,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12996,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12996,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12996,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12996,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12996,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12996,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12996,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12996,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12996,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12996,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12996,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12996,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12996,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12996,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12996,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12996,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12996,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12996,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12996,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12996,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12996,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12996,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12996,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12996,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12996,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12996,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12996,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12996,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12996,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12996,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12996,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12996,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12996,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12996,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12996,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12996,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12996,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12996,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12996,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12996,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12996,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12996,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12996,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12996,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12996,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12996,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12996,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12996,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12996,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12996,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12996,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12996,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12996,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12996,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12996,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12996,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12996,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12996,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12996,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12996,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12996,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12996,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12996,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12996 : FrameRepair 12996 scalarRow12996 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12996Cells j).1 (repair12996Cells j).2.1
  endpoint_upper := fun j => ((repair12996Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12996Cells j).2.2

theorem repair12997Cells (j : Fin 43) :
    0 ≤ (scalarRow12997.table (sourceIndex j)).upper ∧
    (scalarRow12997.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12997.table (sourceIndex j)).centre) /
      (scalarRow12997.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12997.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12997,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12997,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12997,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12997,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12997,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12997,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12997,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12997,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12997,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12997,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12997,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12997,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12997,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12997,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12997,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12997,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12997,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12997,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12997,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12997,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12997,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12997,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12997,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12997,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12997,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12997,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12997,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12997,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12997,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12997,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12997,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12997,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12997,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12997,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12997,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12997,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12997,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12997,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12997,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12997,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12997,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12997,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12997,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12997,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12997,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12997,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12997,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12997,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12997,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12997,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12997,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12997,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12997,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12997,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12997,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12997,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12997,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12997,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12997,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12997,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12997,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12997,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12997,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12997,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12997,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12997,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12997,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12997,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12997,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12997,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12997,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12997,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12997,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12997,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12997,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12997,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12997,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12997,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12997,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12997,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12997,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12997,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12997,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12997,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12997,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12997,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12997 : FrameRepair 12997 scalarRow12997 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12997Cells j).1 (repair12997Cells j).2.1
  endpoint_upper := fun j => ((repair12997Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12997Cells j).2.2

theorem repair12998Cells (j : Fin 43) :
    0 ≤ (scalarRow12998.table (sourceIndex j)).upper ∧
    (scalarRow12998.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12998.table (sourceIndex j)).centre) /
      (scalarRow12998.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12998.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12998,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12998,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12998,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12998,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12998,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12998,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12998,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12998,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12998,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12998,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12998,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12998,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12998,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12998,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12998,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12998,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12998,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12998,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12998,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12998,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12998,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12998,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12998,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12998,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12998,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12998,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12998,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12998,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12998,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12998,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12998,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12998,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12998,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12998,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12998,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12998,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12998,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12998,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12998,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12998,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12998,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12998,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12998,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12998,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12998,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12998,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12998,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12998,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12998,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12998,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12998,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12998,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12998,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12998,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12998,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12998,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12998,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12998,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12998,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12998,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12998,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12998,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12998,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12998,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12998,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12998,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12998,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12998,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12998,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12998,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12998,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12998,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12998,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12998,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12998,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12998,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12998,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12998,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12998,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12998,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12998,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12998,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12998,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12998,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12998,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12998,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12998 : FrameRepair 12998 scalarRow12998 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12998Cells j).1 (repair12998Cells j).2.1
  endpoint_upper := fun j => ((repair12998Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12998Cells j).2.2

theorem repair12999Cells (j : Fin 43) :
    0 ≤ (scalarRow12999.table (sourceIndex j)).upper ∧
    (scalarRow12999.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12999.table (sourceIndex j)).centre) /
      (scalarRow12999.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12999.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12999,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12999,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12999,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12999,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12999,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12999,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12999,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12999,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12999,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12999,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12999,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12999,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12999,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12999,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12999,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12999,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12999,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12999,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12999,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12999,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12999,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12999,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12999,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12999,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12999,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12999,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12999,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12999,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12999,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12999,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12999,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12999,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12999,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12999,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12999,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12999,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12999,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12999,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12999,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12999,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12999,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12999,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12999,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12999,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12999,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12999,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12999,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12999,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12999,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12999,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12999,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12999,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12999,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12999,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12999,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12999,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12999,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12999,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12999,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12999,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12999,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12999,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12999,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12999,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12999,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12999,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12999,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12999,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12999,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12999,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12999,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12999,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12999,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12999,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12999,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12999,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12999,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12999,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12999,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12999,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12999,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12999,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12999,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12999,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12999,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12999,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12999 : FrameRepair 12999 scalarRow12999 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12999Cells j).1 (repair12999Cells j).2.1
  endpoint_upper := fun j => ((repair12999Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12999Cells j).2.2

end BstLean.Part269
