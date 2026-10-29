import BstLean.Part269Rows8
import BstLean.Part269RepairCommon
namespace BstLean.Part269
open Real Set BstLean.Part255 BstLean.Part263 BstLean.Part264
theorem repair12550Cells (j : Fin 43) :
    0 ≤ (scalarRow12550.table (sourceIndex j)).upper ∧
    (scalarRow12550.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12550.table (sourceIndex j)).centre) /
      (scalarRow12550.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12550.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12550,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12550,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12550,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12550,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12550,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12550,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12550,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12550,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12550,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12550,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12550,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12550,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12550,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12550,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12550,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12550,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12550,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12550,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12550,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12550,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12550,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12550,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12550,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12550,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12550,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12550,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12550,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12550,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12550,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12550,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12550,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12550,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12550,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12550,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12550,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12550,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12550,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12550,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12550,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12550,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12550,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12550,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12550,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12550,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12550,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12550,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12550,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12550,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12550,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12550,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12550,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12550,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12550,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12550,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12550,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12550,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12550,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12550,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12550,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12550,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12550,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12550,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12550,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12550,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12550,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12550,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12550,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12550,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12550,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12550,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12550,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12550,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12550,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12550,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12550,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12550,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12550,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12550,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12550,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12550,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12550,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12550,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12550,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12550,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12550,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12550,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12550 : FrameRepair 12550 scalarRow12550 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12550Cells j).1 (repair12550Cells j).2.1
  endpoint_upper := fun j => ((repair12550Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12550Cells j).2.2

theorem repair12551Cells (j : Fin 43) :
    0 ≤ (scalarRow12551.table (sourceIndex j)).upper ∧
    (scalarRow12551.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12551.table (sourceIndex j)).centre) /
      (scalarRow12551.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12551.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12551,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12551,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12551,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12551,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12551,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12551,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12551,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12551,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12551,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12551,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12551,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12551,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12551,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12551,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12551,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12551,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12551,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12551,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12551,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12551,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12551,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12551,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12551,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12551,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12551,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12551,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12551,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12551,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12551,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12551,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12551,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12551,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12551,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12551,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12551,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12551,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12551,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12551,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12551,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12551,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12551,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12551,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12551,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12551,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12551,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12551,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12551,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12551,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12551,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12551,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12551,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12551,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12551,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12551,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12551,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12551,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12551,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12551,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12551,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12551,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12551,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12551,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12551,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12551,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12551,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12551,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12551,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12551,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12551,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12551,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12551,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12551,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12551,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12551,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12551,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12551,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12551,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12551,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12551,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12551,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12551,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12551,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12551,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12551,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12551,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12551,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12551 : FrameRepair 12551 scalarRow12551 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12551Cells j).1 (repair12551Cells j).2.1
  endpoint_upper := fun j => ((repair12551Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12551Cells j).2.2

theorem repair12552Cells (j : Fin 43) :
    0 ≤ (scalarRow12552.table (sourceIndex j)).upper ∧
    (scalarRow12552.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12552.table (sourceIndex j)).centre) /
      (scalarRow12552.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12552.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12552,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12552,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12552,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12552,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12552,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12552,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12552,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12552,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12552,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12552,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12552,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12552,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12552,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12552,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12552,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12552,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12552,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12552,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12552,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12552,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12552,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12552,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12552,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12552,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12552,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12552,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12552,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12552,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12552,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12552,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12552,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12552,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12552,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12552,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12552,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12552,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12552,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12552,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12552,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12552,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12552,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12552,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12552,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12552,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12552,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12552,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12552,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12552,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12552,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12552,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12552,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12552,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12552,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12552,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12552,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12552,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12552,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12552,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12552,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12552,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12552,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12552,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12552,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12552,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12552,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12552,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12552,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12552,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12552,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12552,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12552,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12552,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12552,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12552,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12552,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12552,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12552,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12552,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12552,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12552,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12552,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12552,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12552,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12552,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12552,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12552,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12552 : FrameRepair 12552 scalarRow12552 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12552Cells j).1 (repair12552Cells j).2.1
  endpoint_upper := fun j => ((repair12552Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12552Cells j).2.2

theorem repair12553Cells (j : Fin 43) :
    0 ≤ (scalarRow12553.table (sourceIndex j)).upper ∧
    (scalarRow12553.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12553.table (sourceIndex j)).centre) /
      (scalarRow12553.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12553.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12553,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12553,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12553,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12553,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12553,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12553,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12553,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12553,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12553,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12553,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12553,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12553,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12553,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12553,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12553,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12553,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12553,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12553,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12553,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12553,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12553,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12553,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12553,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12553,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12553,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12553,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12553,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12553,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12553,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12553,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12553,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12553,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12553,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12553,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12553,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12553,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12553,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12553,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12553,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12553,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12553,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12553,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12553,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12553,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12553,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12553,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12553,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12553,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12553,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12553,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12553,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12553,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12553,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12553,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12553,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12553,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12553,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12553,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12553,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12553,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12553,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12553,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12553,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12553,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12553,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12553,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12553,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12553,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12553,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12553,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12553,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12553,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12553,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12553,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12553,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12553,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12553,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12553,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12553,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12553,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12553,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12553,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12553,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12553,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12553,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12553,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12553 : FrameRepair 12553 scalarRow12553 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12553Cells j).1 (repair12553Cells j).2.1
  endpoint_upper := fun j => ((repair12553Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12553Cells j).2.2

theorem repair12554Cells (j : Fin 43) :
    0 ≤ (scalarRow12554.table (sourceIndex j)).upper ∧
    (scalarRow12554.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12554.table (sourceIndex j)).centre) /
      (scalarRow12554.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12554.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12554,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12554,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12554,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12554,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12554,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12554,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12554,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12554,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12554,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12554,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12554,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12554,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12554,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12554,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12554,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12554,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12554,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12554,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12554,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12554,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12554,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12554,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12554,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12554,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12554,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12554,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12554,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12554,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12554,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12554,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12554,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12554,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12554,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12554,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12554,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12554,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12554,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12554,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12554,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12554,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12554,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12554,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12554,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12554,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12554,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12554,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12554,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12554,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12554,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12554,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12554,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12554,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12554,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12554,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12554,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12554,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12554,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12554,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12554,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12554,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12554,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12554,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12554,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12554,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12554,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12554,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12554,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12554,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12554,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12554,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12554,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12554,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12554,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12554,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12554,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12554,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12554,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12554,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12554,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12554,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12554,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12554,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12554,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12554,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12554,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12554,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12554 : FrameRepair 12554 scalarRow12554 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12554Cells j).1 (repair12554Cells j).2.1
  endpoint_upper := fun j => ((repair12554Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12554Cells j).2.2

theorem repair12555Cells (j : Fin 43) :
    0 ≤ (scalarRow12555.table (sourceIndex j)).upper ∧
    (scalarRow12555.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12555.table (sourceIndex j)).centre) /
      (scalarRow12555.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12555.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12555,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12555,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12555,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12555,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12555,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12555,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12555,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12555,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12555,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12555,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12555,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12555,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12555,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12555,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12555,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12555,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12555,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12555,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12555,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12555,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12555,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12555,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12555,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12555,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12555,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12555,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12555,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12555,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12555,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12555,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12555,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12555,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12555,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12555,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12555,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12555,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12555,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12555,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12555,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12555,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12555,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12555,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12555,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12555,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12555,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12555,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12555,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12555,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12555,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12555,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12555,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12555,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12555,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12555,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12555,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12555,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12555,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12555,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12555,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12555,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12555,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12555,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12555,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12555,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12555,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12555,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12555,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12555,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12555,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12555,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12555,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12555,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12555,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12555,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12555,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12555,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12555,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12555,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12555,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12555,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12555,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12555,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12555,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12555,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12555,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12555,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12555 : FrameRepair 12555 scalarRow12555 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12555Cells j).1 (repair12555Cells j).2.1
  endpoint_upper := fun j => ((repair12555Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12555Cells j).2.2

theorem repair12556Cells (j : Fin 43) :
    0 ≤ (scalarRow12556.table (sourceIndex j)).upper ∧
    (scalarRow12556.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12556.table (sourceIndex j)).centre) /
      (scalarRow12556.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12556.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12556,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12556,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12556,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12556,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12556,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12556,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12556,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12556,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12556,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12556,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12556,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12556,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12556,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12556,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12556,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12556,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12556,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12556,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12556,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12556,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12556,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12556,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12556,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12556,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12556,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12556,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12556,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12556,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12556,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12556,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12556,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12556,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12556,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12556,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12556,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12556,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12556,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12556,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12556,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12556,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12556,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12556,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12556,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12556,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12556,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12556,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12556,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12556,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12556,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12556,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12556,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12556,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12556,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12556,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12556,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12556,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12556,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12556,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12556,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12556,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12556,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12556,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12556,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12556,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12556,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12556,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12556,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12556,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12556,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12556,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12556,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12556,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12556,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12556,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12556,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12556,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12556,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12556,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12556,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12556,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12556,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12556,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12556,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12556,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12556,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12556,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12556 : FrameRepair 12556 scalarRow12556 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12556Cells j).1 (repair12556Cells j).2.1
  endpoint_upper := fun j => ((repair12556Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12556Cells j).2.2

theorem repair12557Cells (j : Fin 43) :
    0 ≤ (scalarRow12557.table (sourceIndex j)).upper ∧
    (scalarRow12557.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12557.table (sourceIndex j)).centre) /
      (scalarRow12557.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12557.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12557,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12557,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12557,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12557,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12557,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12557,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12557,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12557,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12557,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12557,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12557,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12557,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12557,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12557,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12557,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12557,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12557,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12557,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12557,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12557,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12557,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12557,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12557,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12557,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12557,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12557,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12557,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12557,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12557,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12557,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12557,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12557,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12557,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12557,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12557,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12557,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12557,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12557,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12557,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12557,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12557,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12557,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12557,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12557,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12557,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12557,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12557,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12557,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12557,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12557,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12557,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12557,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12557,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12557,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12557,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12557,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12557,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12557,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12557,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12557,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12557,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12557,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12557,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12557,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12557,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12557,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12557,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12557,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12557,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12557,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12557,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12557,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12557,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12557,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12557,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12557,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12557,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12557,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12557,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12557,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12557,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12557,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12557,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12557,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12557,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12557,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12557 : FrameRepair 12557 scalarRow12557 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12557Cells j).1 (repair12557Cells j).2.1
  endpoint_upper := fun j => ((repair12557Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12557Cells j).2.2

theorem repair12558Cells (j : Fin 43) :
    0 ≤ (scalarRow12558.table (sourceIndex j)).upper ∧
    (scalarRow12558.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12558.table (sourceIndex j)).centre) /
      (scalarRow12558.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12558.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12558,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12558,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12558,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12558,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12558,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12558,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12558,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12558,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12558,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12558,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12558,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12558,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12558,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12558,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12558,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12558,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12558,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12558,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12558,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12558,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12558,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12558,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12558,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12558,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12558,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12558,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12558,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12558,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12558,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12558,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12558,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12558,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12558,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12558,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12558,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12558,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12558,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12558,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12558,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12558,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12558,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12558,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12558,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12558,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12558,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12558,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12558,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12558,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12558,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12558,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12558,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12558,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12558,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12558,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12558,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12558,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12558,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12558,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12558,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12558,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12558,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12558,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12558,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12558,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12558,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12558,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12558,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12558,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12558,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12558,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12558,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12558,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12558,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12558,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12558,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12558,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12558,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12558,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12558,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12558,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12558,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12558,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12558,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12558,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12558,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12558,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12558 : FrameRepair 12558 scalarRow12558 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12558Cells j).1 (repair12558Cells j).2.1
  endpoint_upper := fun j => ((repair12558Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12558Cells j).2.2

theorem repair12559Cells (j : Fin 43) :
    0 ≤ (scalarRow12559.table (sourceIndex j)).upper ∧
    (scalarRow12559.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12559.table (sourceIndex j)).centre) /
      (scalarRow12559.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12559.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12559,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12559,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12559,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12559,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12559,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12559,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12559,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12559,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12559,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12559,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12559,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12559,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12559,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12559,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12559,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12559,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12559,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12559,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12559,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12559,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12559,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12559,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12559,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12559,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12559,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12559,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12559,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12559,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12559,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12559,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12559,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12559,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12559,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12559,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12559,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12559,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12559,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12559,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12559,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12559,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12559,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12559,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12559,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12559,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12559,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12559,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12559,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12559,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12559,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12559,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12559,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12559,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12559,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12559,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12559,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12559,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12559,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12559,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12559,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12559,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12559,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12559,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12559,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12559,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12559,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12559,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12559,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12559,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12559,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12559,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12559,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12559,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12559,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12559,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12559,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12559,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12559,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12559,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12559,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12559,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12559,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12559,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12559,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12559,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12559,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12559,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12559 : FrameRepair 12559 scalarRow12559 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12559Cells j).1 (repair12559Cells j).2.1
  endpoint_upper := fun j => ((repair12559Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12559Cells j).2.2

theorem repair12560Cells (j : Fin 43) :
    0 ≤ (scalarRow12560.table (sourceIndex j)).upper ∧
    (scalarRow12560.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12560.table (sourceIndex j)).centre) /
      (scalarRow12560.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12560.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12560,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12560,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12560,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12560,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12560,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12560,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12560,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12560,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12560,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12560,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12560,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12560,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12560,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12560,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12560,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12560,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12560,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12560,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12560,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12560,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12560,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12560,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12560,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12560,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12560,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12560,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12560,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12560,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12560,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12560,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12560,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12560,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12560,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12560,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12560,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12560,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12560,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12560,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12560,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12560,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12560,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12560,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12560,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12560,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12560,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12560,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12560,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12560,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12560,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12560,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12560,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12560,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12560,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12560,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12560,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12560,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12560,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12560,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12560,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12560,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12560,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12560,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12560,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12560,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12560,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12560,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12560,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12560,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12560,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12560,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12560,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12560,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12560,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12560,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12560,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12560,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12560,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12560,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12560,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12560,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12560,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12560,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12560,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12560,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12560,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12560,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12560 : FrameRepair 12560 scalarRow12560 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12560Cells j).1 (repair12560Cells j).2.1
  endpoint_upper := fun j => ((repair12560Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12560Cells j).2.2

theorem repair12561Cells (j : Fin 43) :
    0 ≤ (scalarRow12561.table (sourceIndex j)).upper ∧
    (scalarRow12561.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12561.table (sourceIndex j)).centre) /
      (scalarRow12561.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12561.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12561,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12561,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12561,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12561,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12561,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12561,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12561,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12561,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12561,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12561,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12561,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12561,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12561,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12561,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12561,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12561,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12561,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12561,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12561,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12561,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12561,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12561,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12561,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12561,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12561,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12561,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12561,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12561,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12561,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12561,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12561,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12561,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12561,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12561,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12561,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12561,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12561,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12561,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12561,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12561,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12561,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12561,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12561,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12561,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12561,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12561,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12561,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12561,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12561,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12561,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12561,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12561,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12561,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12561,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12561,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12561,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12561,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12561,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12561,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12561,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12561,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12561,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12561,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12561,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12561,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12561,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12561,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12561,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12561,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12561,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12561,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12561,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12561,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12561,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12561,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12561,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12561,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12561,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12561,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12561,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12561,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12561,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12561,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12561,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12561,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12561,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12561 : FrameRepair 12561 scalarRow12561 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12561Cells j).1 (repair12561Cells j).2.1
  endpoint_upper := fun j => ((repair12561Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12561Cells j).2.2

theorem repair12562Cells (j : Fin 43) :
    0 ≤ (scalarRow12562.table (sourceIndex j)).upper ∧
    (scalarRow12562.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12562.table (sourceIndex j)).centre) /
      (scalarRow12562.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12562.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12562,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12562,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12562,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12562,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12562,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12562,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12562,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12562,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12562,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12562,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12562,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12562,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12562,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12562,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12562,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12562,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12562,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12562,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12562,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12562,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12562,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12562,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12562,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12562,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12562,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12562,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12562,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12562,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12562,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12562,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12562,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12562,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12562,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12562,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12562,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12562,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12562,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12562,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12562,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12562,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12562,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12562,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12562,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12562,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12562,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12562,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12562,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12562,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12562,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12562,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12562,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12562,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12562,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12562,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12562,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12562,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12562,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12562,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12562,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12562,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12562,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12562,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12562,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12562,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12562,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12562,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12562,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12562,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12562,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12562,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12562,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12562,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12562,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12562,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12562,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12562,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12562,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12562,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12562,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12562,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12562,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12562,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12562,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12562,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12562,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12562,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12562 : FrameRepair 12562 scalarRow12562 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12562Cells j).1 (repair12562Cells j).2.1
  endpoint_upper := fun j => ((repair12562Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12562Cells j).2.2

theorem repair12563Cells (j : Fin 43) :
    0 ≤ (scalarRow12563.table (sourceIndex j)).upper ∧
    (scalarRow12563.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12563.table (sourceIndex j)).centre) /
      (scalarRow12563.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12563.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12563,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12563,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12563,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12563,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12563,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12563,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12563,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12563,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12563,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12563,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12563,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12563,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12563,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12563,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12563,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12563,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12563,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12563,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12563,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12563,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12563,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12563,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12563,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12563,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12563,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12563,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12563,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12563,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12563,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12563,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12563,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12563,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12563,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12563,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12563,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12563,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12563,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12563,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12563,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12563,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12563,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12563,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12563,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12563,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12563,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12563,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12563,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12563,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12563,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12563,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12563,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12563,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12563,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12563,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12563,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12563,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12563,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12563,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12563,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12563,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12563,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12563,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12563,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12563,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12563,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12563,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12563,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12563,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12563,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12563,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12563,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12563,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12563,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12563,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12563,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12563,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12563,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12563,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12563,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12563,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12563,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12563,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12563,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12563,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12563,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12563,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12563 : FrameRepair 12563 scalarRow12563 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12563Cells j).1 (repair12563Cells j).2.1
  endpoint_upper := fun j => ((repair12563Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12563Cells j).2.2

theorem repair12564Cells (j : Fin 43) :
    0 ≤ (scalarRow12564.table (sourceIndex j)).upper ∧
    (scalarRow12564.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12564.table (sourceIndex j)).centre) /
      (scalarRow12564.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12564.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12564,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12564,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12564,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12564,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12564,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12564,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12564,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12564,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12564,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12564,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12564,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12564,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12564,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12564,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12564,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12564,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12564,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12564,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12564,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12564,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12564,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12564,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12564,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12564,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12564,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12564,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12564,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12564,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12564,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12564,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12564,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12564,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12564,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12564,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12564,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12564,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12564,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12564,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12564,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12564,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12564,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12564,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12564,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12564,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12564,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12564,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12564,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12564,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12564,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12564,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12564,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12564,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12564,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12564,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12564,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12564,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12564,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12564,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12564,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12564,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12564,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12564,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12564,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12564,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12564,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12564,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12564,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12564,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12564,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12564,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12564,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12564,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12564,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12564,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12564,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12564,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12564,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12564,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12564,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12564,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12564,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12564,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12564,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12564,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12564,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12564,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12564 : FrameRepair 12564 scalarRow12564 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12564Cells j).1 (repair12564Cells j).2.1
  endpoint_upper := fun j => ((repair12564Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12564Cells j).2.2

theorem repair12565Cells (j : Fin 43) :
    0 ≤ (scalarRow12565.table (sourceIndex j)).upper ∧
    (scalarRow12565.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12565.table (sourceIndex j)).centre) /
      (scalarRow12565.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12565.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12565,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12565,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12565,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12565,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12565,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12565,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12565,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12565,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12565,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12565,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12565,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12565,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12565,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12565,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12565,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12565,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12565,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12565,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12565,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12565,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12565,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12565,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12565,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12565,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12565,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12565,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12565,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12565,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12565,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12565,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12565,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12565,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12565,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12565,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12565,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12565,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12565,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12565,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12565,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12565,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12565,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12565,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12565,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12565,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12565,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12565,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12565,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12565,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12565,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12565,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12565,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12565,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12565,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12565,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12565,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12565,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12565,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12565,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12565,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12565,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12565,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12565,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12565,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12565,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12565,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12565,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12565,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12565,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12565,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12565,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12565,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12565,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12565,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12565,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12565,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12565,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12565,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12565,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12565,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12565,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12565,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12565,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12565,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12565,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12565,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12565,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12565 : FrameRepair 12565 scalarRow12565 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12565Cells j).1 (repair12565Cells j).2.1
  endpoint_upper := fun j => ((repair12565Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12565Cells j).2.2

theorem repair12566Cells (j : Fin 43) :
    0 ≤ (scalarRow12566.table (sourceIndex j)).upper ∧
    (scalarRow12566.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12566.table (sourceIndex j)).centre) /
      (scalarRow12566.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12566.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12566,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12566,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12566,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12566,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12566,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12566,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12566,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12566,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12566,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12566,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12566,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12566,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12566,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12566,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12566,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12566,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12566,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12566,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12566,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12566,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12566,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12566,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12566,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12566,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12566,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12566,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12566,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12566,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12566,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12566,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12566,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12566,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12566,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12566,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12566,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12566,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12566,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12566,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12566,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12566,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12566,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12566,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12566,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12566,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12566,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12566,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12566,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12566,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12566,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12566,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12566,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12566,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12566,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12566,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12566,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12566,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12566,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12566,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12566,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12566,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12566,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12566,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12566,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12566,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12566,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12566,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12566,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12566,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12566,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12566,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12566,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12566,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12566,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12566,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12566,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12566,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12566,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12566,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12566,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12566,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12566,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12566,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12566,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12566,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12566,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12566,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12566 : FrameRepair 12566 scalarRow12566 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12566Cells j).1 (repair12566Cells j).2.1
  endpoint_upper := fun j => ((repair12566Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12566Cells j).2.2

theorem repair12567Cells (j : Fin 43) :
    0 ≤ (scalarRow12567.table (sourceIndex j)).upper ∧
    (scalarRow12567.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12567.table (sourceIndex j)).centre) /
      (scalarRow12567.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12567.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12567,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12567,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12567,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12567,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12567,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12567,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12567,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12567,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12567,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12567,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12567,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12567,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12567,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12567,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12567,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12567,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12567,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12567,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12567,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12567,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12567,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12567,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12567,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12567,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12567,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12567,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12567,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12567,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12567,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12567,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12567,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12567,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12567,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12567,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12567,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12567,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12567,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12567,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12567,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12567,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12567,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12567,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12567,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12567,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12567,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12567,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12567,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12567,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12567,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12567,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12567,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12567,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12567,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12567,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12567,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12567,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12567,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12567,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12567,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12567,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12567,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12567,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12567,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12567,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12567,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12567,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12567,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12567,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12567,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12567,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12567,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12567,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12567,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12567,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12567,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12567,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12567,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12567,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12567,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12567,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12567,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12567,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12567,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12567,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12567,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12567,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12567 : FrameRepair 12567 scalarRow12567 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12567Cells j).1 (repair12567Cells j).2.1
  endpoint_upper := fun j => ((repair12567Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12567Cells j).2.2

theorem repair12568Cells (j : Fin 43) :
    0 ≤ (scalarRow12568.table (sourceIndex j)).upper ∧
    (scalarRow12568.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12568.table (sourceIndex j)).centre) /
      (scalarRow12568.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12568.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12568,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12568,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12568,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12568,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12568,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12568,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12568,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12568,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12568,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12568,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12568,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12568,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12568,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12568,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12568,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12568,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12568,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12568,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12568,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12568,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12568,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12568,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12568,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12568,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12568,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12568,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12568,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12568,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12568,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12568,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12568,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12568,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12568,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12568,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12568,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12568,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12568,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12568,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12568,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12568,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12568,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12568,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12568,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12568,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12568,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12568,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12568,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12568,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12568,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12568,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12568,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12568,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12568,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12568,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12568,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12568,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12568,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12568,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12568,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12568,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12568,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12568,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12568,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12568,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12568,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12568,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12568,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12568,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12568,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12568,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12568,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12568,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12568,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12568,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12568,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12568,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12568,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12568,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12568,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12568,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12568,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12568,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12568,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12568,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12568,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12568,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12568 : FrameRepair 12568 scalarRow12568 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12568Cells j).1 (repair12568Cells j).2.1
  endpoint_upper := fun j => ((repair12568Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12568Cells j).2.2

theorem repair12569Cells (j : Fin 43) :
    0 ≤ (scalarRow12569.table (sourceIndex j)).upper ∧
    (scalarRow12569.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12569.table (sourceIndex j)).centre) /
      (scalarRow12569.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12569.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12569,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12569,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12569,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12569,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12569,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12569,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12569,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12569,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12569,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12569,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12569,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12569,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12569,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12569,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12569,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12569,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12569,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12569,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12569,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12569,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12569,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12569,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12569,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12569,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12569,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12569,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12569,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12569,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12569,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12569,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12569,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12569,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12569,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12569,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12569,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12569,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12569,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12569,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12569,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12569,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12569,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12569,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12569,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12569,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12569,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12569,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12569,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12569,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12569,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12569,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12569,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12569,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12569,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12569,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12569,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12569,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12569,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12569,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12569,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12569,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12569,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12569,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12569,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12569,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12569,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12569,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12569,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12569,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12569,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12569,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12569,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12569,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12569,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12569,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12569,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12569,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12569,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12569,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12569,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12569,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12569,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12569,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12569,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12569,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12569,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12569,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12569 : FrameRepair 12569 scalarRow12569 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12569Cells j).1 (repair12569Cells j).2.1
  endpoint_upper := fun j => ((repair12569Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12569Cells j).2.2

theorem repair12570Cells (j : Fin 43) :
    0 ≤ (scalarRow12570.table (sourceIndex j)).upper ∧
    (scalarRow12570.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12570.table (sourceIndex j)).centre) /
      (scalarRow12570.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12570.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12570,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12570,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12570,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12570,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12570,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12570,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12570,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12570,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12570,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12570,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12570,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12570,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12570,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12570,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12570,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12570,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12570,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12570,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12570,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12570,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12570,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12570,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12570,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12570,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12570,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12570,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12570,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12570,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12570,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12570,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12570,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12570,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12570,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12570,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12570,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12570,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12570,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12570,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12570,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12570,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12570,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12570,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12570,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12570,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12570,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12570,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12570,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12570,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12570,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12570,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12570,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12570,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12570,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12570,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12570,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12570,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12570,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12570,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12570,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12570,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12570,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12570,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12570,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12570,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12570,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12570,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12570,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12570,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12570,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12570,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12570,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12570,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12570,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12570,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12570,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12570,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12570,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12570,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12570,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12570,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12570,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12570,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12570,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12570,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12570,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12570,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12570 : FrameRepair 12570 scalarRow12570 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12570Cells j).1 (repair12570Cells j).2.1
  endpoint_upper := fun j => ((repair12570Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12570Cells j).2.2

theorem repair12571Cells (j : Fin 43) :
    0 ≤ (scalarRow12571.table (sourceIndex j)).upper ∧
    (scalarRow12571.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12571.table (sourceIndex j)).centre) /
      (scalarRow12571.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12571.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12571,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12571,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12571,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12571,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12571,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12571,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12571,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12571,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12571,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12571,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12571,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12571,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12571,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12571,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12571,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12571,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12571,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12571,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12571,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12571,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12571,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12571,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12571,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12571,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12571,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12571,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12571,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12571,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12571,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12571,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12571,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12571,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12571,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12571,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12571,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12571,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12571,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12571,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12571,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12571,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12571,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12571,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12571,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12571,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12571,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12571,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12571,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12571,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12571,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12571,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12571,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12571,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12571,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12571,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12571,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12571,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12571,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12571,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12571,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12571,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12571,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12571,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12571,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12571,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12571,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12571,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12571,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12571,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12571,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12571,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12571,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12571,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12571,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12571,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12571,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12571,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12571,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12571,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12571,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12571,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12571,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12571,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12571,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12571,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12571,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12571,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12571 : FrameRepair 12571 scalarRow12571 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12571Cells j).1 (repair12571Cells j).2.1
  endpoint_upper := fun j => ((repair12571Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12571Cells j).2.2

theorem repair12572Cells (j : Fin 43) :
    0 ≤ (scalarRow12572.table (sourceIndex j)).upper ∧
    (scalarRow12572.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12572.table (sourceIndex j)).centre) /
      (scalarRow12572.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12572.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12572,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12572,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12572,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12572,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12572,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12572,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12572,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12572,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12572,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12572,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12572,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12572,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12572,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12572,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12572,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12572,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12572,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12572,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12572,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12572,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12572,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12572,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12572,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12572,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12572,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12572,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12572,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12572,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12572,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12572,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12572,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12572,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12572,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12572,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12572,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12572,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12572,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12572,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12572,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12572,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12572,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12572,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12572,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12572,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12572,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12572,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12572,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12572,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12572,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12572,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12572,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12572,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12572,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12572,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12572,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12572,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12572,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12572,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12572,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12572,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12572,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12572,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12572,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12572,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12572,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12572,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12572,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12572,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12572,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12572,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12572,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12572,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12572,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12572,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12572,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12572,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12572,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12572,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12572,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12572,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12572,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12572,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12572,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12572,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12572,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12572,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12572 : FrameRepair 12572 scalarRow12572 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12572Cells j).1 (repair12572Cells j).2.1
  endpoint_upper := fun j => ((repair12572Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12572Cells j).2.2

theorem repair12573Cells (j : Fin 43) :
    0 ≤ (scalarRow12573.table (sourceIndex j)).upper ∧
    (scalarRow12573.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12573.table (sourceIndex j)).centre) /
      (scalarRow12573.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12573.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12573,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12573,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12573,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12573,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12573,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12573,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12573,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12573,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12573,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12573,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12573,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12573,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12573,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12573,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12573,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12573,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12573,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12573,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12573,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12573,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12573,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12573,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12573,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12573,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12573,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12573,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12573,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12573,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12573,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12573,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12573,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12573,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12573,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12573,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12573,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12573,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12573,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12573,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12573,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12573,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12573,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12573,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12573,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12573,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12573,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12573,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12573,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12573,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12573,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12573,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12573,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12573,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12573,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12573,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12573,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12573,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12573,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12573,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12573,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12573,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12573,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12573,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12573,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12573,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12573,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12573,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12573,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12573,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12573,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12573,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12573,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12573,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12573,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12573,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12573,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12573,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12573,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12573,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12573,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12573,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12573,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12573,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12573,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12573,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12573,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12573,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12573 : FrameRepair 12573 scalarRow12573 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12573Cells j).1 (repair12573Cells j).2.1
  endpoint_upper := fun j => ((repair12573Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12573Cells j).2.2

theorem repair12574Cells (j : Fin 43) :
    0 ≤ (scalarRow12574.table (sourceIndex j)).upper ∧
    (scalarRow12574.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12574.table (sourceIndex j)).centre) /
      (scalarRow12574.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12574.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12574,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12574,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12574,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12574,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12574,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12574,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12574,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12574,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12574,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12574,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12574,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12574,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12574,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12574,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12574,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12574,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12574,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12574,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12574,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12574,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12574,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12574,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12574,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12574,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12574,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12574,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12574,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12574,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12574,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12574,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12574,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12574,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12574,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12574,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12574,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12574,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12574,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12574,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12574,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12574,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12574,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12574,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12574,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12574,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12574,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12574,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12574,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12574,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12574,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12574,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12574,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12574,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12574,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12574,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12574,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12574,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12574,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12574,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12574,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12574,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12574,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12574,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12574,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12574,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12574,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12574,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12574,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12574,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12574,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12574,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12574,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12574,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12574,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12574,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12574,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12574,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12574,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12574,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12574,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12574,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12574,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12574,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12574,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12574,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12574,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12574,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12574 : FrameRepair 12574 scalarRow12574 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12574Cells j).1 (repair12574Cells j).2.1
  endpoint_upper := fun j => ((repair12574Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12574Cells j).2.2

end BstLean.Part269
