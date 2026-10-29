import BstLean.Part269Rows20
import BstLean.Part269RepairCommon
namespace BstLean.Part269
open Real Set BstLean.Part255 BstLean.Part263 BstLean.Part264
theorem repair12850Cells (j : Fin 43) :
    0 ≤ (scalarRow12850.table (sourceIndex j)).upper ∧
    (scalarRow12850.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12850.table (sourceIndex j)).centre) /
      (scalarRow12850.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12850.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12850,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12850,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12850,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12850,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12850,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12850,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12850,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12850,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12850,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12850,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12850,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12850,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12850,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12850,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12850,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12850,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12850,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12850,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12850,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12850,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12850,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12850,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12850,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12850,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12850,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12850,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12850,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12850,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12850,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12850,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12850,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12850,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12850,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12850,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12850,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12850,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12850,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12850,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12850,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12850,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12850,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12850,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12850,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12850,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12850,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12850,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12850,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12850,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12850,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12850,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12850,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12850,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12850,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12850,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12850,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12850,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12850,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12850,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12850,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12850,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12850,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12850,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12850,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12850,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12850,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12850,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12850,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12850,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12850,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12850,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12850,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12850,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12850,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12850,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12850,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12850,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12850,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12850,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12850,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12850,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12850,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12850,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12850,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12850,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12850,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12850,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12850 : FrameRepair 12850 scalarRow12850 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12850Cells j).1 (repair12850Cells j).2.1
  endpoint_upper := fun j => ((repair12850Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12850Cells j).2.2

theorem repair12851Cells (j : Fin 43) :
    0 ≤ (scalarRow12851.table (sourceIndex j)).upper ∧
    (scalarRow12851.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12851.table (sourceIndex j)).centre) /
      (scalarRow12851.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12851.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12851,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12851,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12851,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12851,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12851,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12851,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12851,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12851,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12851,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12851,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12851,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12851,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12851,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12851,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12851,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12851,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12851,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12851,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12851,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12851,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12851,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12851,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12851,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12851,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12851,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12851,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12851,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12851,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12851,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12851,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12851,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12851,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12851,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12851,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12851,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12851,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12851,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12851,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12851,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12851,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12851,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12851,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12851,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12851,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12851,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12851,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12851,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12851,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12851,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12851,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12851,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12851,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12851,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12851,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12851,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12851,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12851,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12851,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12851,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12851,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12851,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12851,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12851,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12851,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12851,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12851,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12851,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12851,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12851,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12851,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12851,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12851,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12851,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12851,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12851,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12851,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12851,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12851,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12851,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12851,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12851,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12851,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12851,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12851,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12851,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12851,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12851 : FrameRepair 12851 scalarRow12851 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12851Cells j).1 (repair12851Cells j).2.1
  endpoint_upper := fun j => ((repair12851Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12851Cells j).2.2

theorem repair12852Cells (j : Fin 43) :
    0 ≤ (scalarRow12852.table (sourceIndex j)).upper ∧
    (scalarRow12852.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12852.table (sourceIndex j)).centre) /
      (scalarRow12852.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12852.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12852,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12852,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12852,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12852,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12852,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12852,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12852,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12852,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12852,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12852,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12852,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12852,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12852,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12852,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12852,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12852,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12852,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12852,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12852,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12852,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12852,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12852,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12852,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12852,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12852,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12852,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12852,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12852,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12852,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12852,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12852,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12852,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12852,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12852,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12852,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12852,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12852,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12852,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12852,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12852,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12852,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12852,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12852,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12852,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12852,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12852,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12852,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12852,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12852,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12852,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12852,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12852,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12852,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12852,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12852,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12852,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12852,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12852,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12852,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12852,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12852,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12852,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12852,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12852,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12852,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12852,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12852,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12852,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12852,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12852,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12852,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12852,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12852,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12852,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12852,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12852,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12852,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12852,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12852,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12852,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12852,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12852,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12852,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12852,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12852,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12852,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12852 : FrameRepair 12852 scalarRow12852 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12852Cells j).1 (repair12852Cells j).2.1
  endpoint_upper := fun j => ((repair12852Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12852Cells j).2.2

theorem repair12853Cells (j : Fin 43) :
    0 ≤ (scalarRow12853.table (sourceIndex j)).upper ∧
    (scalarRow12853.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12853.table (sourceIndex j)).centre) /
      (scalarRow12853.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12853.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12853,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12853,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12853,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12853,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12853,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12853,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12853,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12853,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12853,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12853,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12853,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12853,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12853,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12853,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12853,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12853,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12853,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12853,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12853,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12853,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12853,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12853,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12853,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12853,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12853,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12853,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12853,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12853,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12853,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12853,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12853,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12853,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12853,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12853,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12853,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12853,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12853,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12853,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12853,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12853,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12853,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12853,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12853,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12853,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12853,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12853,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12853,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12853,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12853,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12853,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12853,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12853,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12853,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12853,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12853,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12853,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12853,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12853,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12853,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12853,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12853,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12853,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12853,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12853,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12853,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12853,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12853,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12853,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12853,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12853,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12853,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12853,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12853,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12853,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12853,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12853,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12853,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12853,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12853,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12853,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12853,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12853,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12853,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12853,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12853,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12853,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12853 : FrameRepair 12853 scalarRow12853 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12853Cells j).1 (repair12853Cells j).2.1
  endpoint_upper := fun j => ((repair12853Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12853Cells j).2.2

theorem repair12854Cells (j : Fin 43) :
    0 ≤ (scalarRow12854.table (sourceIndex j)).upper ∧
    (scalarRow12854.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12854.table (sourceIndex j)).centre) /
      (scalarRow12854.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12854.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12854,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12854,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12854,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12854,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12854,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12854,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12854,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12854,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12854,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12854,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12854,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12854,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12854,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12854,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12854,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12854,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12854,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12854,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12854,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12854,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12854,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12854,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12854,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12854,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12854,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12854,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12854,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12854,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12854,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12854,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12854,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12854,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12854,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12854,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12854,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12854,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12854,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12854,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12854,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12854,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12854,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12854,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12854,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12854,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12854,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12854,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12854,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12854,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12854,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12854,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12854,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12854,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12854,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12854,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12854,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12854,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12854,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12854,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12854,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12854,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12854,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12854,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12854,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12854,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12854,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12854,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12854,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12854,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12854,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12854,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12854,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12854,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12854,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12854,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12854,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12854,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12854,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12854,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12854,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12854,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12854,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12854,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12854,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12854,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12854,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12854,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12854 : FrameRepair 12854 scalarRow12854 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12854Cells j).1 (repair12854Cells j).2.1
  endpoint_upper := fun j => ((repair12854Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12854Cells j).2.2

theorem repair12855Cells (j : Fin 43) :
    0 ≤ (scalarRow12855.table (sourceIndex j)).upper ∧
    (scalarRow12855.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12855.table (sourceIndex j)).centre) /
      (scalarRow12855.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12855.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12855,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12855,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12855,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12855,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12855,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12855,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12855,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12855,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12855,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12855,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12855,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12855,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12855,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12855,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12855,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12855,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12855,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12855,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12855,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12855,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12855,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12855,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12855,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12855,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12855,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12855,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12855,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12855,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12855,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12855,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12855,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12855,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12855,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12855,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12855,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12855,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12855,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12855,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12855,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12855,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12855,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12855,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12855,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12855,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12855,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12855,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12855,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12855,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12855,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12855,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12855,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12855,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12855,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12855,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12855,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12855,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12855,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12855,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12855,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12855,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12855,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12855,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12855,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12855,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12855,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12855,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12855,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12855,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12855,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12855,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12855,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12855,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12855,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12855,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12855,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12855,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12855,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12855,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12855,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12855,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12855,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12855,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12855,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12855,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12855,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12855,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12855 : FrameRepair 12855 scalarRow12855 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12855Cells j).1 (repair12855Cells j).2.1
  endpoint_upper := fun j => ((repair12855Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12855Cells j).2.2

theorem repair12856Cells (j : Fin 43) :
    0 ≤ (scalarRow12856.table (sourceIndex j)).upper ∧
    (scalarRow12856.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12856.table (sourceIndex j)).centre) /
      (scalarRow12856.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12856.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12856,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12856,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12856,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12856,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12856,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12856,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12856,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12856,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12856,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12856,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12856,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12856,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12856,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12856,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12856,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12856,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12856,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12856,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12856,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12856,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12856,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12856,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12856,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12856,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12856,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12856,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12856,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12856,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12856,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12856,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12856,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12856,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12856,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12856,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12856,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12856,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12856,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12856,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12856,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12856,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12856,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12856,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12856,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12856,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12856,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12856,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12856,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12856,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12856,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12856,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12856,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12856,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12856,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12856,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12856,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12856,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12856,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12856,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12856,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12856,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12856,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12856,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12856,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12856,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12856,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12856,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12856,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12856,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12856,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12856,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12856,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12856,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12856,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12856,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12856,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12856,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12856,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12856,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12856,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12856,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12856,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12856,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12856,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12856,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12856,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12856,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12856 : FrameRepair 12856 scalarRow12856 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12856Cells j).1 (repair12856Cells j).2.1
  endpoint_upper := fun j => ((repair12856Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12856Cells j).2.2

theorem repair12857Cells (j : Fin 43) :
    0 ≤ (scalarRow12857.table (sourceIndex j)).upper ∧
    (scalarRow12857.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12857.table (sourceIndex j)).centre) /
      (scalarRow12857.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12857.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12857,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12857,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12857,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12857,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12857,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12857,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12857,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12857,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12857,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12857,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12857,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12857,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12857,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12857,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12857,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12857,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12857,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12857,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12857,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12857,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12857,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12857,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12857,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12857,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12857,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12857,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12857,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12857,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12857,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12857,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12857,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12857,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12857,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12857,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12857,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12857,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12857,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12857,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12857,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12857,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12857,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12857,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12857,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12857,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12857,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12857,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12857,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12857,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12857,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12857,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12857,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12857,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12857,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12857,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12857,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12857,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12857,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12857,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12857,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12857,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12857,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12857,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12857,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12857,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12857,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12857,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12857,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12857,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12857,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12857,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12857,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12857,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12857,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12857,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12857,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12857,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12857,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12857,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12857,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12857,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12857,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12857,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12857,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12857,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12857,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12857,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12857 : FrameRepair 12857 scalarRow12857 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12857Cells j).1 (repair12857Cells j).2.1
  endpoint_upper := fun j => ((repair12857Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12857Cells j).2.2

theorem repair12858Cells (j : Fin 43) :
    0 ≤ (scalarRow12858.table (sourceIndex j)).upper ∧
    (scalarRow12858.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12858.table (sourceIndex j)).centre) /
      (scalarRow12858.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12858.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12858,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12858,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12858,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12858,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12858,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12858,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12858,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12858,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12858,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12858,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12858,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12858,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12858,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12858,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12858,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12858,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12858,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12858,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12858,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12858,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12858,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12858,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12858,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12858,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12858,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12858,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12858,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12858,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12858,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12858,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12858,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12858,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12858,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12858,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12858,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12858,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12858,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12858,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12858,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12858,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12858,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12858,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12858,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12858,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12858,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12858,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12858,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12858,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12858,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12858,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12858,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12858,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12858,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12858,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12858,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12858,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12858,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12858,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12858,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12858,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12858,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12858,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12858,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12858,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12858,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12858,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12858,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12858,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12858,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12858,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12858,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12858,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12858,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12858,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12858,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12858,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12858,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12858,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12858,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12858,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12858,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12858,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12858,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12858,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12858,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12858,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12858 : FrameRepair 12858 scalarRow12858 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12858Cells j).1 (repair12858Cells j).2.1
  endpoint_upper := fun j => ((repair12858Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12858Cells j).2.2

theorem repair12859Cells (j : Fin 43) :
    0 ≤ (scalarRow12859.table (sourceIndex j)).upper ∧
    (scalarRow12859.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12859.table (sourceIndex j)).centre) /
      (scalarRow12859.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12859.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12859,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12859,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12859,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12859,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12859,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12859,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12859,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12859,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12859,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12859,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12859,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12859,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12859,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12859,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12859,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12859,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12859,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12859,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12859,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12859,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12859,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12859,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12859,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12859,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12859,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12859,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12859,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12859,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12859,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12859,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12859,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12859,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12859,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12859,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12859,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12859,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12859,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12859,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12859,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12859,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12859,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12859,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12859,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12859,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12859,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12859,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12859,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12859,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12859,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12859,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12859,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12859,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12859,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12859,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12859,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12859,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12859,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12859,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12859,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12859,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12859,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12859,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12859,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12859,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12859,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12859,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12859,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12859,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12859,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12859,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12859,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12859,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12859,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12859,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12859,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12859,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12859,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12859,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12859,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12859,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12859,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12859,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12859,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12859,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12859,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12859,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12859 : FrameRepair 12859 scalarRow12859 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12859Cells j).1 (repair12859Cells j).2.1
  endpoint_upper := fun j => ((repair12859Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12859Cells j).2.2

theorem repair12860Cells (j : Fin 43) :
    0 ≤ (scalarRow12860.table (sourceIndex j)).upper ∧
    (scalarRow12860.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12860.table (sourceIndex j)).centre) /
      (scalarRow12860.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12860.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12860,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12860,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12860,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12860,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12860,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12860,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12860,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12860,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12860,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12860,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12860,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12860,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12860,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12860,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12860,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12860,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12860,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12860,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12860,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12860,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12860,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12860,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12860,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12860,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12860,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12860,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12860,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12860,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12860,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12860,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12860,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12860,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12860,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12860,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12860,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12860,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12860,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12860,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12860,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12860,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12860,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12860,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12860,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12860,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12860,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12860,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12860,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12860,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12860,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12860,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12860,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12860,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12860,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12860,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12860,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12860,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12860,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12860,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12860,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12860,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12860,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12860,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12860,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12860,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12860,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12860,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12860,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12860,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12860,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12860,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12860,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12860,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12860,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12860,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12860,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12860,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12860,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12860,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12860,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12860,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12860,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12860,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12860,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12860,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12860,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12860,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12860 : FrameRepair 12860 scalarRow12860 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12860Cells j).1 (repair12860Cells j).2.1
  endpoint_upper := fun j => ((repair12860Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12860Cells j).2.2

theorem repair12861Cells (j : Fin 43) :
    0 ≤ (scalarRow12861.table (sourceIndex j)).upper ∧
    (scalarRow12861.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12861.table (sourceIndex j)).centre) /
      (scalarRow12861.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12861.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12861,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12861,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12861,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12861,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12861,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12861,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12861,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12861,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12861,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12861,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12861,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12861,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12861,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12861,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12861,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12861,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12861,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12861,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12861,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12861,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12861,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12861,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12861,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12861,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12861,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12861,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12861,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12861,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12861,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12861,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12861,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12861,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12861,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12861,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12861,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12861,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12861,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12861,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12861,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12861,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12861,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12861,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12861,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12861,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12861,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12861,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12861,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12861,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12861,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12861,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12861,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12861,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12861,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12861,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12861,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12861,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12861,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12861,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12861,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12861,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12861,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12861,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12861,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12861,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12861,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12861,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12861,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12861,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12861,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12861,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12861,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12861,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12861,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12861,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12861,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12861,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12861,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12861,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12861,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12861,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12861,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12861,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12861,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12861,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12861,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12861,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12861 : FrameRepair 12861 scalarRow12861 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12861Cells j).1 (repair12861Cells j).2.1
  endpoint_upper := fun j => ((repair12861Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12861Cells j).2.2

theorem repair12862Cells (j : Fin 43) :
    0 ≤ (scalarRow12862.table (sourceIndex j)).upper ∧
    (scalarRow12862.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12862.table (sourceIndex j)).centre) /
      (scalarRow12862.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12862.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12862,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12862,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12862,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12862,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12862,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12862,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12862,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12862,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12862,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12862,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12862,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12862,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12862,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12862,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12862,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12862,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12862,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12862,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12862,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12862,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12862,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12862,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12862,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12862,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12862,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12862,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12862,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12862,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12862,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12862,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12862,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12862,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12862,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12862,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12862,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12862,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12862,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12862,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12862,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12862,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12862,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12862,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12862,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12862,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12862,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12862,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12862,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12862,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12862,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12862,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12862,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12862,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12862,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12862,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12862,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12862,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12862,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12862,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12862,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12862,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12862,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12862,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12862,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12862,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12862,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12862,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12862,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12862,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12862,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12862,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12862,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12862,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12862,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12862,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12862,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12862,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12862,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12862,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12862,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12862,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12862,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12862,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12862,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12862,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12862,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12862,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12862 : FrameRepair 12862 scalarRow12862 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12862Cells j).1 (repair12862Cells j).2.1
  endpoint_upper := fun j => ((repair12862Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12862Cells j).2.2

theorem repair12863Cells (j : Fin 43) :
    0 ≤ (scalarRow12863.table (sourceIndex j)).upper ∧
    (scalarRow12863.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12863.table (sourceIndex j)).centre) /
      (scalarRow12863.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12863.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12863,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12863,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12863,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12863,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12863,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12863,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12863,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12863,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12863,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12863,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12863,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12863,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12863,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12863,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12863,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12863,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12863,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12863,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12863,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12863,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12863,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12863,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12863,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12863,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12863,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12863,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12863,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12863,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12863,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12863,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12863,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12863,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12863,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12863,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12863,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12863,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12863,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12863,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12863,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12863,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12863,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12863,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12863,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12863,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12863,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12863,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12863,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12863,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12863,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12863,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12863,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12863,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12863,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12863,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12863,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12863,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12863,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12863,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12863,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12863,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12863,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12863,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12863,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12863,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12863,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12863,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12863,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12863,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12863,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12863,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12863,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12863,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12863,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12863,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12863,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12863,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12863,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12863,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12863,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12863,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12863,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12863,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12863,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12863,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12863,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12863,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12863 : FrameRepair 12863 scalarRow12863 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12863Cells j).1 (repair12863Cells j).2.1
  endpoint_upper := fun j => ((repair12863Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12863Cells j).2.2

theorem repair12864Cells (j : Fin 43) :
    0 ≤ (scalarRow12864.table (sourceIndex j)).upper ∧
    (scalarRow12864.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12864.table (sourceIndex j)).centre) /
      (scalarRow12864.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12864.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12864,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12864,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12864,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12864,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12864,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12864,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12864,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12864,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12864,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12864,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12864,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12864,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12864,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12864,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12864,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12864,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12864,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12864,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12864,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12864,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12864,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12864,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12864,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12864,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12864,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12864,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12864,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12864,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12864,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12864,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12864,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12864,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12864,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12864,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12864,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12864,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12864,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12864,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12864,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12864,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12864,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12864,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12864,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12864,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12864,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12864,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12864,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12864,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12864,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12864,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12864,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12864,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12864,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12864,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12864,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12864,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12864,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12864,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12864,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12864,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12864,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12864,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12864,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12864,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12864,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12864,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12864,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12864,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12864,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12864,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12864,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12864,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12864,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12864,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12864,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12864,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12864,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12864,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12864,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12864,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12864,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12864,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12864,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12864,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12864,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12864,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12864 : FrameRepair 12864 scalarRow12864 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12864Cells j).1 (repair12864Cells j).2.1
  endpoint_upper := fun j => ((repair12864Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12864Cells j).2.2

theorem repair12865Cells (j : Fin 43) :
    0 ≤ (scalarRow12865.table (sourceIndex j)).upper ∧
    (scalarRow12865.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12865.table (sourceIndex j)).centre) /
      (scalarRow12865.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12865.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12865,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12865,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12865,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12865,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12865,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12865,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12865,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12865,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12865,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12865,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12865,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12865,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12865,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12865,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12865,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12865,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12865,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12865,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12865,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12865,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12865,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12865,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12865,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12865,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12865,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12865,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12865,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12865,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12865,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12865,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12865,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12865,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12865,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12865,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12865,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12865,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12865,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12865,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12865,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12865,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12865,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12865,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12865,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12865,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12865,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12865,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12865,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12865,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12865,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12865,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12865,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12865,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12865,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12865,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12865,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12865,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12865,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12865,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12865,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12865,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12865,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12865,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12865,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12865,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12865,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12865,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12865,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12865,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12865,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12865,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12865,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12865,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12865,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12865,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12865,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12865,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12865,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12865,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12865,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12865,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12865,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12865,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12865,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12865,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12865,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12865,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12865 : FrameRepair 12865 scalarRow12865 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12865Cells j).1 (repair12865Cells j).2.1
  endpoint_upper := fun j => ((repair12865Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12865Cells j).2.2

theorem repair12866Cells (j : Fin 43) :
    0 ≤ (scalarRow12866.table (sourceIndex j)).upper ∧
    (scalarRow12866.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12866.table (sourceIndex j)).centre) /
      (scalarRow12866.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12866.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12866,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12866,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12866,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12866,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12866,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12866,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12866,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12866,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12866,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12866,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12866,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12866,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12866,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12866,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12866,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12866,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12866,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12866,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12866,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12866,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12866,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12866,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12866,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12866,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12866,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12866,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12866,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12866,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12866,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12866,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12866,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12866,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12866,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12866,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12866,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12866,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12866,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12866,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12866,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12866,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12866,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12866,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12866,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12866,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12866,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12866,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12866,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12866,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12866,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12866,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12866,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12866,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12866,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12866,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12866,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12866,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12866,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12866,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12866,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12866,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12866,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12866,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12866,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12866,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12866,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12866,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12866,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12866,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12866,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12866,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12866,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12866,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12866,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12866,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12866,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12866,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12866,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12866,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12866,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12866,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12866,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12866,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12866,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12866,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12866,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12866,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12866 : FrameRepair 12866 scalarRow12866 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12866Cells j).1 (repair12866Cells j).2.1
  endpoint_upper := fun j => ((repair12866Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12866Cells j).2.2

theorem repair12867Cells (j : Fin 43) :
    0 ≤ (scalarRow12867.table (sourceIndex j)).upper ∧
    (scalarRow12867.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12867.table (sourceIndex j)).centre) /
      (scalarRow12867.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12867.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12867,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12867,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12867,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12867,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12867,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12867,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12867,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12867,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12867,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12867,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12867,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12867,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12867,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12867,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12867,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12867,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12867,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12867,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12867,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12867,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12867,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12867,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12867,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12867,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12867,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12867,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12867,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12867,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12867,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12867,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12867,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12867,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12867,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12867,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12867,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12867,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12867,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12867,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12867,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12867,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12867,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12867,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12867,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12867,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12867,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12867,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12867,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12867,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12867,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12867,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12867,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12867,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12867,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12867,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12867,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12867,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12867,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12867,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12867,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12867,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12867,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12867,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12867,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12867,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12867,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12867,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12867,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12867,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12867,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12867,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12867,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12867,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12867,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12867,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12867,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12867,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12867,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12867,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12867,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12867,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12867,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12867,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12867,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12867,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12867,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12867,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12867 : FrameRepair 12867 scalarRow12867 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12867Cells j).1 (repair12867Cells j).2.1
  endpoint_upper := fun j => ((repair12867Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12867Cells j).2.2

theorem repair12868Cells (j : Fin 43) :
    0 ≤ (scalarRow12868.table (sourceIndex j)).upper ∧
    (scalarRow12868.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12868.table (sourceIndex j)).centre) /
      (scalarRow12868.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12868.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12868,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12868,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12868,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12868,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12868,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12868,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12868,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12868,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12868,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12868,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12868,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12868,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12868,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12868,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12868,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12868,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12868,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12868,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12868,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12868,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12868,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12868,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12868,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12868,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12868,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12868,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12868,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12868,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12868,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12868,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12868,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12868,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12868,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12868,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12868,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12868,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12868,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12868,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12868,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12868,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12868,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12868,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12868,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12868,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12868,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12868,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12868,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12868,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12868,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12868,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12868,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12868,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12868,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12868,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12868,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12868,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12868,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12868,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12868,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12868,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12868,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12868,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12868,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12868,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12868,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12868,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12868,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12868,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12868,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12868,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12868,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12868,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12868,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12868,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12868,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12868,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12868,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12868,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12868,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12868,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12868,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12868,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12868,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12868,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12868,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12868,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12868 : FrameRepair 12868 scalarRow12868 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12868Cells j).1 (repair12868Cells j).2.1
  endpoint_upper := fun j => ((repair12868Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12868Cells j).2.2

theorem repair12869Cells (j : Fin 43) :
    0 ≤ (scalarRow12869.table (sourceIndex j)).upper ∧
    (scalarRow12869.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12869.table (sourceIndex j)).centre) /
      (scalarRow12869.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12869.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12869,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12869,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12869,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12869,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12869,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12869,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12869,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12869,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12869,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12869,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12869,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12869,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12869,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12869,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12869,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12869,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12869,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12869,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12869,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12869,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12869,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12869,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12869,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12869,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12869,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12869,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12869,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12869,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12869,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12869,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12869,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12869,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12869,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12869,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12869,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12869,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12869,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12869,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12869,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12869,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12869,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12869,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12869,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12869,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12869,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12869,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12869,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12869,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12869,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12869,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12869,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12869,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12869,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12869,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12869,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12869,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12869,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12869,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12869,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12869,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12869,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12869,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12869,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12869,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12869,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12869,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12869,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12869,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12869,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12869,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12869,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12869,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12869,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12869,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12869,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12869,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12869,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12869,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12869,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12869,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12869,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12869,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12869,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12869,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12869,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12869,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12869 : FrameRepair 12869 scalarRow12869 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12869Cells j).1 (repair12869Cells j).2.1
  endpoint_upper := fun j => ((repair12869Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12869Cells j).2.2

theorem repair12870Cells (j : Fin 43) :
    0 ≤ (scalarRow12870.table (sourceIndex j)).upper ∧
    (scalarRow12870.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12870.table (sourceIndex j)).centre) /
      (scalarRow12870.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12870.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12870,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12870,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12870,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12870,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12870,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12870,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12870,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12870,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12870,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12870,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12870,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12870,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12870,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12870,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12870,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12870,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12870,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12870,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12870,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12870,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12870,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12870,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12870,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12870,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12870,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12870,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12870,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12870,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12870,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12870,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12870,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12870,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12870,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12870,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12870,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12870,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12870,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12870,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12870,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12870,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12870,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12870,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12870,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12870,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12870,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12870,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12870,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12870,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12870,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12870,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12870,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12870,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12870,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12870,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12870,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12870,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12870,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12870,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12870,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12870,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12870,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12870,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12870,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12870,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12870,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12870,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12870,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12870,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12870,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12870,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12870,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12870,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12870,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12870,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12870,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12870,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12870,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12870,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12870,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12870,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12870,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12870,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12870,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12870,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12870,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12870,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12870 : FrameRepair 12870 scalarRow12870 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12870Cells j).1 (repair12870Cells j).2.1
  endpoint_upper := fun j => ((repair12870Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12870Cells j).2.2

theorem repair12871Cells (j : Fin 43) :
    0 ≤ (scalarRow12871.table (sourceIndex j)).upper ∧
    (scalarRow12871.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12871.table (sourceIndex j)).centre) /
      (scalarRow12871.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12871.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12871,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12871,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12871,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12871,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12871,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12871,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12871,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12871,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12871,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12871,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12871,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12871,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12871,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12871,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12871,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12871,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12871,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12871,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12871,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12871,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12871,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12871,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12871,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12871,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12871,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12871,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12871,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12871,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12871,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12871,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12871,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12871,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12871,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12871,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12871,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12871,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12871,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12871,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12871,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12871,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12871,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12871,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12871,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12871,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12871,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12871,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12871,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12871,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12871,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12871,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12871,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12871,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12871,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12871,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12871,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12871,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12871,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12871,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12871,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12871,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12871,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12871,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12871,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12871,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12871,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12871,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12871,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12871,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12871,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12871,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12871,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12871,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12871,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12871,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12871,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12871,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12871,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12871,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12871,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12871,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12871,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12871,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12871,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12871,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12871,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12871,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12871 : FrameRepair 12871 scalarRow12871 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12871Cells j).1 (repair12871Cells j).2.1
  endpoint_upper := fun j => ((repair12871Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12871Cells j).2.2

theorem repair12872Cells (j : Fin 43) :
    0 ≤ (scalarRow12872.table (sourceIndex j)).upper ∧
    (scalarRow12872.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12872.table (sourceIndex j)).centre) /
      (scalarRow12872.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12872.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12872,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12872,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12872,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12872,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12872,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12872,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12872,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12872,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12872,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12872,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12872,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12872,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12872,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12872,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12872,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12872,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12872,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12872,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12872,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12872,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12872,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12872,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12872,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12872,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12872,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12872,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12872,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12872,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12872,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12872,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12872,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12872,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12872,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12872,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12872,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12872,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12872,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12872,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12872,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12872,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12872,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12872,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12872,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12872,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12872,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12872,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12872,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12872,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12872,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12872,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12872,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12872,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12872,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12872,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12872,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12872,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12872,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12872,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12872,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12872,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12872,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12872,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12872,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12872,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12872,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12872,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12872,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12872,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12872,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12872,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12872,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12872,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12872,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12872,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12872,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12872,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12872,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12872,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12872,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12872,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12872,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12872,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12872,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12872,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12872,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12872,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12872 : FrameRepair 12872 scalarRow12872 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12872Cells j).1 (repair12872Cells j).2.1
  endpoint_upper := fun j => ((repair12872Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12872Cells j).2.2

theorem repair12873Cells (j : Fin 43) :
    0 ≤ (scalarRow12873.table (sourceIndex j)).upper ∧
    (scalarRow12873.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12873.table (sourceIndex j)).centre) /
      (scalarRow12873.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12873.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12873,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12873,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12873,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12873,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12873,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12873,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12873,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12873,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12873,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12873,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12873,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12873,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12873,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12873,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12873,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12873,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12873,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12873,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12873,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12873,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12873,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12873,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12873,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12873,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12873,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12873,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12873,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12873,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12873,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12873,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12873,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12873,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12873,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12873,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12873,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12873,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12873,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12873,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12873,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12873,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12873,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12873,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12873,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12873,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12873,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12873,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12873,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12873,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12873,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12873,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12873,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12873,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12873,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12873,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12873,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12873,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12873,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12873,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12873,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12873,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12873,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12873,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12873,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12873,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12873,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12873,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12873,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12873,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12873,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12873,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12873,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12873,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12873,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12873,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12873,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12873,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12873,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12873,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12873,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12873,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12873,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12873,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12873,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12873,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12873,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12873,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12873 : FrameRepair 12873 scalarRow12873 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12873Cells j).1 (repair12873Cells j).2.1
  endpoint_upper := fun j => ((repair12873Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12873Cells j).2.2

theorem repair12874Cells (j : Fin 43) :
    0 ≤ (scalarRow12874.table (sourceIndex j)).upper ∧
    (scalarRow12874.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12874.table (sourceIndex j)).centre) /
      (scalarRow12874.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12874.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12874,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12874,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12874,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12874,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12874,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12874,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12874,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12874,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12874,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12874,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12874,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12874,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12874,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12874,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12874,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12874,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12874,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12874,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12874,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12874,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12874,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12874,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12874,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12874,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12874,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12874,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12874,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12874,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12874,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12874,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12874,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12874,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12874,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12874,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12874,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12874,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12874,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12874,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12874,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12874,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12874,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12874,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12874,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12874,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12874,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12874,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12874,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12874,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12874,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12874,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12874,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12874,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12874,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12874,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12874,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12874,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12874,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12874,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12874,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12874,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12874,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12874,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12874,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12874,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12874,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12874,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12874,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12874,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12874,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12874,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12874,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12874,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12874,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12874,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12874,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12874,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12874,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12874,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12874,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12874,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12874,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12874,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12874,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12874,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12874,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12874,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12874 : FrameRepair 12874 scalarRow12874 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12874Cells j).1 (repair12874Cells j).2.1
  endpoint_upper := fun j => ((repair12874Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12874Cells j).2.2

end BstLean.Part269
