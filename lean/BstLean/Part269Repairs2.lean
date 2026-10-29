import BstLean.Part269Rows2
import BstLean.Part269RepairCommon
namespace BstLean.Part269
open Real Set BstLean.Part255 BstLean.Part263 BstLean.Part264
theorem repair12400Cells (j : Fin 43) :
    0 ≤ (scalarRow12400.table (sourceIndex j)).upper ∧
    (scalarRow12400.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12400.table (sourceIndex j)).centre) /
      (scalarRow12400.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12400.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12400,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12400,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12400,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12400,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12400,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12400,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12400,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12400,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12400,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12400,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12400,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12400,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12400,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12400,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12400,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12400,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12400,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12400,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12400,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12400,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12400,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12400,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12400,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12400,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12400,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12400,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12400,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12400,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12400,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12400,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12400,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12400,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12400,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12400,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12400,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12400,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12400,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12400,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12400,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12400,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12400,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12400,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12400,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12400,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12400,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12400,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12400,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12400,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12400,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12400,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12400,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12400,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12400,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12400,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12400,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12400,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12400,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12400,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12400,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12400,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12400,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12400,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12400,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12400,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12400,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12400,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12400,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12400,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12400,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12400,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12400,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12400,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12400,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12400,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12400,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12400,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12400,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12400,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12400,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12400,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12400,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12400,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12400,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12400,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12400,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12400,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12400 : FrameRepair 12400 scalarRow12400 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12400Cells j).1 (repair12400Cells j).2.1
  endpoint_upper := fun j => ((repair12400Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12400Cells j).2.2

theorem repair12401Cells (j : Fin 43) :
    0 ≤ (scalarRow12401.table (sourceIndex j)).upper ∧
    (scalarRow12401.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12401.table (sourceIndex j)).centre) /
      (scalarRow12401.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12401.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12401,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12401,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12401,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12401,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12401,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12401,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12401,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12401,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12401,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12401,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12401,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12401,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12401,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12401,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12401,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12401,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12401,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12401,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12401,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12401,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12401,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12401,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12401,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12401,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12401,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12401,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12401,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12401,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12401,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12401,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12401,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12401,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12401,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12401,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12401,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12401,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12401,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12401,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12401,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12401,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12401,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12401,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12401,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12401,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12401,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12401,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12401,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12401,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12401,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12401,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12401,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12401,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12401,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12401,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12401,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12401,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12401,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12401,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12401,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12401,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12401,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12401,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12401,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12401,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12401,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12401,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12401,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12401,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12401,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12401,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12401,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12401,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12401,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12401,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12401,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12401,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12401,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12401,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12401,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12401,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12401,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12401,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12401,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12401,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12401,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12401,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12401 : FrameRepair 12401 scalarRow12401 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12401Cells j).1 (repair12401Cells j).2.1
  endpoint_upper := fun j => ((repair12401Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12401Cells j).2.2

theorem repair12402Cells (j : Fin 43) :
    0 ≤ (scalarRow12402.table (sourceIndex j)).upper ∧
    (scalarRow12402.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12402.table (sourceIndex j)).centre) /
      (scalarRow12402.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12402.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12402,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12402,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12402,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12402,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12402,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12402,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12402,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12402,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12402,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12402,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12402,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12402,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12402,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12402,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12402,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12402,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12402,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12402,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12402,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12402,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12402,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12402,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12402,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12402,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12402,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12402,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12402,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12402,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12402,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12402,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12402,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12402,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12402,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12402,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12402,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12402,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12402,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12402,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12402,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12402,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12402,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12402,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12402,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12402,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12402,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12402,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12402,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12402,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12402,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12402,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12402,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12402,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12402,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12402,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12402,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12402,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12402,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12402,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12402,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12402,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12402,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12402,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12402,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12402,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12402,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12402,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12402,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12402,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12402,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12402,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12402,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12402,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12402,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12402,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12402,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12402,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12402,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12402,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12402,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12402,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12402,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12402,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12402,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12402,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12402,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12402,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12402 : FrameRepair 12402 scalarRow12402 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12402Cells j).1 (repair12402Cells j).2.1
  endpoint_upper := fun j => ((repair12402Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12402Cells j).2.2

theorem repair12403Cells (j : Fin 43) :
    0 ≤ (scalarRow12403.table (sourceIndex j)).upper ∧
    (scalarRow12403.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12403.table (sourceIndex j)).centre) /
      (scalarRow12403.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12403.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12403,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12403,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12403,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12403,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12403,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12403,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12403,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12403,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12403,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12403,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12403,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12403,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12403,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12403,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12403,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12403,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12403,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12403,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12403,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12403,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12403,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12403,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12403,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12403,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12403,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12403,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12403,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12403,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12403,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12403,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12403,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12403,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12403,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12403,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12403,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12403,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12403,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12403,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12403,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12403,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12403,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12403,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12403,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12403,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12403,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12403,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12403,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12403,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12403,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12403,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12403,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12403,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12403,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12403,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12403,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12403,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12403,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12403,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12403,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12403,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12403,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12403,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12403,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12403,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12403,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12403,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12403,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12403,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12403,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12403,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12403,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12403,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12403,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12403,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12403,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12403,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12403,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12403,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12403,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12403,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12403,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12403,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12403,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12403,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12403,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12403,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12403 : FrameRepair 12403 scalarRow12403 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12403Cells j).1 (repair12403Cells j).2.1
  endpoint_upper := fun j => ((repair12403Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12403Cells j).2.2

theorem repair12404Cells (j : Fin 43) :
    0 ≤ (scalarRow12404.table (sourceIndex j)).upper ∧
    (scalarRow12404.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12404.table (sourceIndex j)).centre) /
      (scalarRow12404.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12404.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12404,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12404,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12404,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12404,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12404,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12404,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12404,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12404,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12404,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12404,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12404,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12404,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12404,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12404,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12404,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12404,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12404,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12404,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12404,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12404,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12404,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12404,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12404,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12404,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12404,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12404,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12404,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12404,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12404,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12404,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12404,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12404,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12404,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12404,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12404,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12404,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12404,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12404,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12404,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12404,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12404,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12404,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12404,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12404,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12404,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12404,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12404,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12404,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12404,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12404,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12404,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12404,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12404,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12404,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12404,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12404,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12404,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12404,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12404,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12404,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12404,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12404,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12404,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12404,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12404,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12404,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12404,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12404,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12404,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12404,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12404,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12404,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12404,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12404,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12404,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12404,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12404,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12404,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12404,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12404,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12404,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12404,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12404,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12404,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12404,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12404,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12404 : FrameRepair 12404 scalarRow12404 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12404Cells j).1 (repair12404Cells j).2.1
  endpoint_upper := fun j => ((repair12404Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12404Cells j).2.2

theorem repair12405Cells (j : Fin 43) :
    0 ≤ (scalarRow12405.table (sourceIndex j)).upper ∧
    (scalarRow12405.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12405.table (sourceIndex j)).centre) /
      (scalarRow12405.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12405.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12405,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12405,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12405,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12405,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12405,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12405,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12405,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12405,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12405,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12405,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12405,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12405,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12405,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12405,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12405,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12405,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12405,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12405,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12405,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12405,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12405,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12405,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12405,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12405,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12405,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12405,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12405,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12405,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12405,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12405,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12405,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12405,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12405,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12405,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12405,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12405,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12405,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12405,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12405,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12405,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12405,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12405,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12405,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12405,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12405,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12405,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12405,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12405,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12405,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12405,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12405,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12405,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12405,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12405,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12405,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12405,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12405,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12405,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12405,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12405,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12405,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12405,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12405,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12405,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12405,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12405,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12405,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12405,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12405,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12405,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12405,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12405,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12405,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12405,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12405,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12405,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12405,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12405,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12405,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12405,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12405,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12405,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12405,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12405,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12405,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12405,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12405 : FrameRepair 12405 scalarRow12405 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12405Cells j).1 (repair12405Cells j).2.1
  endpoint_upper := fun j => ((repair12405Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12405Cells j).2.2

theorem repair12406Cells (j : Fin 43) :
    0 ≤ (scalarRow12406.table (sourceIndex j)).upper ∧
    (scalarRow12406.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12406.table (sourceIndex j)).centre) /
      (scalarRow12406.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12406.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12406,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12406,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12406,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12406,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12406,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12406,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12406,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12406,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12406,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12406,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12406,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12406,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12406,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12406,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12406,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12406,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12406,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12406,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12406,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12406,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12406,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12406,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12406,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12406,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12406,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12406,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12406,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12406,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12406,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12406,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12406,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12406,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12406,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12406,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12406,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12406,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12406,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12406,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12406,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12406,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12406,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12406,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12406,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12406,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12406,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12406,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12406,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12406,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12406,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12406,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12406,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12406,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12406,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12406,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12406,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12406,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12406,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12406,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12406,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12406,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12406,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12406,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12406,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12406,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12406,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12406,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12406,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12406,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12406,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12406,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12406,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12406,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12406,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12406,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12406,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12406,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12406,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12406,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12406,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12406,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12406,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12406,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12406,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12406,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12406,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12406,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12406 : FrameRepair 12406 scalarRow12406 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12406Cells j).1 (repair12406Cells j).2.1
  endpoint_upper := fun j => ((repair12406Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12406Cells j).2.2

theorem repair12407Cells (j : Fin 43) :
    0 ≤ (scalarRow12407.table (sourceIndex j)).upper ∧
    (scalarRow12407.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12407.table (sourceIndex j)).centre) /
      (scalarRow12407.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12407.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12407,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12407,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12407,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12407,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12407,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12407,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12407,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12407,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12407,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12407,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12407,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12407,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12407,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12407,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12407,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12407,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12407,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12407,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12407,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12407,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12407,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12407,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12407,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12407,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12407,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12407,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12407,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12407,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12407,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12407,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12407,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12407,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12407,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12407,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12407,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12407,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12407,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12407,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12407,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12407,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12407,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12407,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12407,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12407,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12407,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12407,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12407,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12407,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12407,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12407,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12407,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12407,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12407,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12407,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12407,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12407,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12407,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12407,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12407,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12407,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12407,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12407,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12407,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12407,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12407,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12407,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12407,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12407,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12407,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12407,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12407,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12407,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12407,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12407,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12407,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12407,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12407,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12407,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12407,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12407,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12407,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12407,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12407,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12407,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12407,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12407,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12407 : FrameRepair 12407 scalarRow12407 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12407Cells j).1 (repair12407Cells j).2.1
  endpoint_upper := fun j => ((repair12407Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12407Cells j).2.2

theorem repair12408Cells (j : Fin 43) :
    0 ≤ (scalarRow12408.table (sourceIndex j)).upper ∧
    (scalarRow12408.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12408.table (sourceIndex j)).centre) /
      (scalarRow12408.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12408.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12408,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12408,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12408,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12408,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12408,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12408,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12408,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12408,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12408,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12408,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12408,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12408,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12408,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12408,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12408,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12408,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12408,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12408,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12408,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12408,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12408,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12408,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12408,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12408,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12408,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12408,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12408,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12408,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12408,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12408,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12408,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12408,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12408,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12408,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12408,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12408,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12408,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12408,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12408,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12408,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12408,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12408,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12408,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12408,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12408,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12408,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12408,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12408,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12408,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12408,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12408,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12408,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12408,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12408,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12408,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12408,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12408,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12408,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12408,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12408,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12408,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12408,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12408,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12408,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12408,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12408,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12408,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12408,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12408,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12408,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12408,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12408,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12408,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12408,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12408,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12408,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12408,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12408,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12408,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12408,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12408,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12408,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12408,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12408,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12408,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12408,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12408 : FrameRepair 12408 scalarRow12408 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12408Cells j).1 (repair12408Cells j).2.1
  endpoint_upper := fun j => ((repair12408Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12408Cells j).2.2

theorem repair12409Cells (j : Fin 43) :
    0 ≤ (scalarRow12409.table (sourceIndex j)).upper ∧
    (scalarRow12409.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12409.table (sourceIndex j)).centre) /
      (scalarRow12409.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12409.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12409,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12409,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12409,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12409,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12409,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12409,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12409,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12409,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12409,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12409,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12409,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12409,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12409,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12409,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12409,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12409,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12409,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12409,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12409,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12409,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12409,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12409,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12409,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12409,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12409,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12409,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12409,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12409,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12409,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12409,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12409,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12409,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12409,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12409,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12409,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12409,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12409,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12409,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12409,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12409,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12409,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12409,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12409,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12409,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12409,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12409,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12409,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12409,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12409,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12409,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12409,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12409,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12409,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12409,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12409,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12409,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12409,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12409,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12409,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12409,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12409,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12409,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12409,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12409,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12409,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12409,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12409,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12409,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12409,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12409,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12409,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12409,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12409,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12409,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12409,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12409,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12409,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12409,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12409,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12409,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12409,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12409,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12409,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12409,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12409,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12409,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12409 : FrameRepair 12409 scalarRow12409 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12409Cells j).1 (repair12409Cells j).2.1
  endpoint_upper := fun j => ((repair12409Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12409Cells j).2.2

theorem repair12410Cells (j : Fin 43) :
    0 ≤ (scalarRow12410.table (sourceIndex j)).upper ∧
    (scalarRow12410.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12410.table (sourceIndex j)).centre) /
      (scalarRow12410.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12410.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12410,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12410,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12410,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12410,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12410,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12410,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12410,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12410,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12410,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12410,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12410,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12410,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12410,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12410,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12410,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12410,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12410,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12410,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12410,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12410,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12410,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12410,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12410,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12410,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12410,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12410,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12410,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12410,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12410,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12410,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12410,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12410,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12410,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12410,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12410,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12410,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12410,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12410,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12410,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12410,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12410,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12410,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12410,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12410,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12410,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12410,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12410,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12410,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12410,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12410,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12410,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12410,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12410,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12410,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12410,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12410,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12410,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12410,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12410,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12410,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12410,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12410,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12410,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12410,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12410,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12410,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12410,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12410,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12410,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12410,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12410,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12410,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12410,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12410,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12410,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12410,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12410,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12410,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12410,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12410,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12410,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12410,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12410,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12410,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12410,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12410,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12410 : FrameRepair 12410 scalarRow12410 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12410Cells j).1 (repair12410Cells j).2.1
  endpoint_upper := fun j => ((repair12410Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12410Cells j).2.2

theorem repair12411Cells (j : Fin 43) :
    0 ≤ (scalarRow12411.table (sourceIndex j)).upper ∧
    (scalarRow12411.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12411.table (sourceIndex j)).centre) /
      (scalarRow12411.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12411.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12411,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12411,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12411,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12411,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12411,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12411,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12411,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12411,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12411,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12411,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12411,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12411,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12411,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12411,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12411,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12411,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12411,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12411,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12411,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12411,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12411,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12411,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12411,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12411,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12411,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12411,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12411,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12411,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12411,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12411,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12411,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12411,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12411,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12411,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12411,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12411,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12411,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12411,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12411,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12411,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12411,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12411,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12411,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12411,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12411,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12411,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12411,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12411,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12411,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12411,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12411,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12411,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12411,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12411,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12411,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12411,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12411,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12411,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12411,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12411,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12411,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12411,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12411,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12411,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12411,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12411,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12411,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12411,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12411,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12411,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12411,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12411,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12411,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12411,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12411,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12411,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12411,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12411,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12411,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12411,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12411,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12411,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12411,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12411,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12411,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12411,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12411 : FrameRepair 12411 scalarRow12411 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12411Cells j).1 (repair12411Cells j).2.1
  endpoint_upper := fun j => ((repair12411Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12411Cells j).2.2

theorem repair12412Cells (j : Fin 43) :
    0 ≤ (scalarRow12412.table (sourceIndex j)).upper ∧
    (scalarRow12412.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12412.table (sourceIndex j)).centre) /
      (scalarRow12412.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12412.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12412,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12412,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12412,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12412,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12412,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12412,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12412,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12412,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12412,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12412,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12412,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12412,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12412,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12412,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12412,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12412,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12412,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12412,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12412,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12412,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12412,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12412,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12412,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12412,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12412,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12412,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12412,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12412,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12412,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12412,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12412,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12412,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12412,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12412,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12412,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12412,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12412,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12412,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12412,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12412,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12412,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12412,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12412,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12412,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12412,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12412,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12412,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12412,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12412,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12412,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12412,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12412,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12412,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12412,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12412,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12412,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12412,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12412,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12412,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12412,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12412,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12412,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12412,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12412,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12412,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12412,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12412,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12412,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12412,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12412,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12412,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12412,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12412,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12412,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12412,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12412,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12412,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12412,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12412,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12412,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12412,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12412,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12412,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12412,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12412,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12412,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12412 : FrameRepair 12412 scalarRow12412 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12412Cells j).1 (repair12412Cells j).2.1
  endpoint_upper := fun j => ((repair12412Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12412Cells j).2.2

theorem repair12413Cells (j : Fin 43) :
    0 ≤ (scalarRow12413.table (sourceIndex j)).upper ∧
    (scalarRow12413.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12413.table (sourceIndex j)).centre) /
      (scalarRow12413.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12413.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12413,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12413,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12413,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12413,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12413,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12413,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12413,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12413,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12413,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12413,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12413,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12413,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12413,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12413,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12413,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12413,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12413,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12413,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12413,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12413,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12413,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12413,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12413,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12413,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12413,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12413,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12413,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12413,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12413,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12413,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12413,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12413,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12413,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12413,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12413,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12413,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12413,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12413,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12413,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12413,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12413,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12413,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12413,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12413,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12413,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12413,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12413,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12413,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12413,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12413,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12413,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12413,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12413,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12413,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12413,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12413,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12413,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12413,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12413,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12413,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12413,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12413,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12413,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12413,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12413,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12413,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12413,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12413,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12413,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12413,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12413,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12413,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12413,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12413,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12413,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12413,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12413,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12413,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12413,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12413,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12413,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12413,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12413,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12413,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12413,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12413,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12413 : FrameRepair 12413 scalarRow12413 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12413Cells j).1 (repair12413Cells j).2.1
  endpoint_upper := fun j => ((repair12413Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12413Cells j).2.2

theorem repair12414Cells (j : Fin 43) :
    0 ≤ (scalarRow12414.table (sourceIndex j)).upper ∧
    (scalarRow12414.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12414.table (sourceIndex j)).centre) /
      (scalarRow12414.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12414.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12414,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12414,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12414,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12414,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12414,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12414,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12414,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12414,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12414,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12414,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12414,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12414,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12414,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12414,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12414,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12414,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12414,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12414,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12414,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12414,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12414,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12414,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12414,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12414,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12414,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12414,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12414,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12414,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12414,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12414,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12414,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12414,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12414,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12414,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12414,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12414,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12414,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12414,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12414,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12414,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12414,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12414,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12414,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12414,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12414,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12414,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12414,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12414,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12414,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12414,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12414,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12414,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12414,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12414,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12414,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12414,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12414,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12414,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12414,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12414,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12414,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12414,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12414,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12414,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12414,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12414,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12414,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12414,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12414,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12414,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12414,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12414,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12414,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12414,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12414,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12414,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12414,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12414,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12414,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12414,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12414,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12414,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12414,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12414,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12414,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12414,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12414 : FrameRepair 12414 scalarRow12414 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12414Cells j).1 (repair12414Cells j).2.1
  endpoint_upper := fun j => ((repair12414Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12414Cells j).2.2

theorem repair12415Cells (j : Fin 43) :
    0 ≤ (scalarRow12415.table (sourceIndex j)).upper ∧
    (scalarRow12415.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12415.table (sourceIndex j)).centre) /
      (scalarRow12415.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12415.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12415,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12415,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12415,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12415,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12415,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12415,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12415,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12415,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12415,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12415,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12415,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12415,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12415,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12415,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12415,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12415,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12415,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12415,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12415,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12415,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12415,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12415,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12415,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12415,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12415,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12415,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12415,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12415,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12415,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12415,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12415,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12415,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12415,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12415,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12415,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12415,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12415,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12415,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12415,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12415,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12415,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12415,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12415,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12415,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12415,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12415,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12415,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12415,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12415,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12415,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12415,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12415,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12415,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12415,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12415,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12415,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12415,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12415,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12415,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12415,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12415,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12415,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12415,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12415,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12415,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12415,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12415,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12415,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12415,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12415,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12415,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12415,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12415,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12415,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12415,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12415,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12415,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12415,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12415,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12415,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12415,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12415,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12415,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12415,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12415,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12415,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12415 : FrameRepair 12415 scalarRow12415 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12415Cells j).1 (repair12415Cells j).2.1
  endpoint_upper := fun j => ((repair12415Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12415Cells j).2.2

theorem repair12416Cells (j : Fin 43) :
    0 ≤ (scalarRow12416.table (sourceIndex j)).upper ∧
    (scalarRow12416.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12416.table (sourceIndex j)).centre) /
      (scalarRow12416.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12416.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12416,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12416,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12416,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12416,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12416,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12416,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12416,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12416,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12416,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12416,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12416,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12416,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12416,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12416,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12416,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12416,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12416,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12416,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12416,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12416,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12416,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12416,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12416,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12416,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12416,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12416,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12416,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12416,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12416,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12416,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12416,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12416,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12416,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12416,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12416,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12416,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12416,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12416,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12416,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12416,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12416,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12416,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12416,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12416,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12416,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12416,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12416,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12416,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12416,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12416,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12416,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12416,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12416,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12416,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12416,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12416,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12416,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12416,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12416,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12416,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12416,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12416,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12416,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12416,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12416,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12416,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12416,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12416,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12416,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12416,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12416,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12416,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12416,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12416,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12416,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12416,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12416,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12416,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12416,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12416,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12416,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12416,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12416,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12416,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12416,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12416,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12416 : FrameRepair 12416 scalarRow12416 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12416Cells j).1 (repair12416Cells j).2.1
  endpoint_upper := fun j => ((repair12416Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12416Cells j).2.2

theorem repair12417Cells (j : Fin 43) :
    0 ≤ (scalarRow12417.table (sourceIndex j)).upper ∧
    (scalarRow12417.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12417.table (sourceIndex j)).centre) /
      (scalarRow12417.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12417.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12417,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12417,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12417,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12417,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12417,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12417,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12417,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12417,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12417,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12417,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12417,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12417,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12417,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12417,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12417,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12417,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12417,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12417,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12417,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12417,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12417,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12417,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12417,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12417,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12417,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12417,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12417,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12417,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12417,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12417,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12417,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12417,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12417,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12417,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12417,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12417,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12417,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12417,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12417,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12417,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12417,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12417,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12417,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12417,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12417,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12417,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12417,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12417,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12417,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12417,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12417,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12417,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12417,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12417,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12417,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12417,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12417,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12417,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12417,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12417,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12417,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12417,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12417,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12417,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12417,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12417,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12417,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12417,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12417,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12417,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12417,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12417,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12417,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12417,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12417,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12417,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12417,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12417,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12417,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12417,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12417,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12417,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12417,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12417,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12417,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12417,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12417 : FrameRepair 12417 scalarRow12417 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12417Cells j).1 (repair12417Cells j).2.1
  endpoint_upper := fun j => ((repair12417Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12417Cells j).2.2

theorem repair12418Cells (j : Fin 43) :
    0 ≤ (scalarRow12418.table (sourceIndex j)).upper ∧
    (scalarRow12418.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12418.table (sourceIndex j)).centre) /
      (scalarRow12418.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12418.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12418,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12418,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12418,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12418,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12418,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12418,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12418,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12418,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12418,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12418,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12418,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12418,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12418,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12418,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12418,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12418,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12418,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12418,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12418,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12418,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12418,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12418,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12418,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12418,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12418,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12418,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12418,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12418,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12418,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12418,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12418,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12418,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12418,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12418,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12418,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12418,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12418,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12418,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12418,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12418,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12418,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12418,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12418,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12418,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12418,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12418,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12418,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12418,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12418,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12418,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12418,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12418,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12418,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12418,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12418,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12418,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12418,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12418,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12418,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12418,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12418,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12418,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12418,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12418,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12418,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12418,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12418,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12418,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12418,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12418,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12418,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12418,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12418,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12418,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12418,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12418,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12418,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12418,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12418,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12418,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12418,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12418,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12418,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12418,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12418,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12418,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12418 : FrameRepair 12418 scalarRow12418 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12418Cells j).1 (repair12418Cells j).2.1
  endpoint_upper := fun j => ((repair12418Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12418Cells j).2.2

theorem repair12419Cells (j : Fin 43) :
    0 ≤ (scalarRow12419.table (sourceIndex j)).upper ∧
    (scalarRow12419.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12419.table (sourceIndex j)).centre) /
      (scalarRow12419.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12419.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12419,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12419,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12419,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12419,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12419,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12419,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12419,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12419,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12419,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12419,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12419,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12419,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12419,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12419,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12419,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12419,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12419,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12419,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12419,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12419,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12419,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12419,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12419,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12419,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12419,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12419,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12419,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12419,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12419,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12419,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12419,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12419,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12419,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12419,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12419,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12419,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12419,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12419,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12419,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12419,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12419,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12419,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12419,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12419,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12419,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12419,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12419,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12419,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12419,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12419,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12419,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12419,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12419,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12419,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12419,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12419,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12419,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12419,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12419,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12419,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12419,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12419,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12419,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12419,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12419,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12419,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12419,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12419,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12419,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12419,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12419,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12419,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12419,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12419,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12419,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12419,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12419,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12419,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12419,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12419,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12419,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12419,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12419,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12419,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12419,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12419,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12419 : FrameRepair 12419 scalarRow12419 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12419Cells j).1 (repair12419Cells j).2.1
  endpoint_upper := fun j => ((repair12419Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12419Cells j).2.2

theorem repair12420Cells (j : Fin 43) :
    0 ≤ (scalarRow12420.table (sourceIndex j)).upper ∧
    (scalarRow12420.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12420.table (sourceIndex j)).centre) /
      (scalarRow12420.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12420.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12420,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12420,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12420,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12420,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12420,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12420,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12420,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12420,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12420,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12420,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12420,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12420,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12420,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12420,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12420,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12420,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12420,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12420,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12420,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12420,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12420,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12420,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12420,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12420,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12420,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12420,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12420,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12420,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12420,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12420,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12420,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12420,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12420,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12420,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12420,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12420,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12420,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12420,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12420,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12420,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12420,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12420,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12420,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12420,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12420,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12420,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12420,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12420,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12420,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12420,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12420,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12420,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12420,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12420,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12420,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12420,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12420,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12420,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12420,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12420,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12420,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12420,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12420,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12420,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12420,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12420,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12420,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12420,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12420,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12420,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12420,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12420,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12420,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12420,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12420,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12420,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12420,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12420,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12420,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12420,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12420,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12420,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12420,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12420,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12420,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12420,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12420 : FrameRepair 12420 scalarRow12420 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12420Cells j).1 (repair12420Cells j).2.1
  endpoint_upper := fun j => ((repair12420Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12420Cells j).2.2

theorem repair12421Cells (j : Fin 43) :
    0 ≤ (scalarRow12421.table (sourceIndex j)).upper ∧
    (scalarRow12421.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12421.table (sourceIndex j)).centre) /
      (scalarRow12421.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12421.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12421,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12421,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12421,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12421,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12421,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12421,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12421,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12421,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12421,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12421,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12421,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12421,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12421,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12421,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12421,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12421,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12421,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12421,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12421,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12421,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12421,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12421,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12421,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12421,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12421,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12421,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12421,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12421,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12421,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12421,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12421,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12421,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12421,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12421,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12421,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12421,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12421,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12421,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12421,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12421,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12421,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12421,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12421,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12421,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12421,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12421,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12421,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12421,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12421,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12421,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12421,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12421,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12421,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12421,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12421,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12421,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12421,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12421,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12421,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12421,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12421,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12421,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12421,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12421,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12421,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12421,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12421,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12421,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12421,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12421,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12421,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12421,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12421,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12421,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12421,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12421,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12421,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12421,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12421,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12421,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12421,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12421,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12421,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12421,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12421,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12421,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12421 : FrameRepair 12421 scalarRow12421 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12421Cells j).1 (repair12421Cells j).2.1
  endpoint_upper := fun j => ((repair12421Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12421Cells j).2.2

theorem repair12422Cells (j : Fin 43) :
    0 ≤ (scalarRow12422.table (sourceIndex j)).upper ∧
    (scalarRow12422.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12422.table (sourceIndex j)).centre) /
      (scalarRow12422.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12422.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12422,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12422,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12422,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12422,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12422,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12422,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12422,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12422,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12422,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12422,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12422,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12422,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12422,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12422,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12422,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12422,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12422,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12422,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12422,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12422,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12422,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12422,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12422,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12422,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12422,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12422,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12422,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12422,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12422,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12422,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12422,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12422,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12422,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12422,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12422,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12422,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12422,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12422,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12422,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12422,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12422,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12422,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12422,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12422,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12422,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12422,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12422,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12422,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12422,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12422,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12422,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12422,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12422,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12422,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12422,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12422,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12422,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12422,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12422,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12422,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12422,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12422,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12422,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12422,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12422,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12422,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12422,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12422,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12422,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12422,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12422,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12422,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12422,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12422,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12422,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12422,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12422,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12422,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12422,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12422,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12422,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12422,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12422,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12422,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12422,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12422,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12422 : FrameRepair 12422 scalarRow12422 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12422Cells j).1 (repair12422Cells j).2.1
  endpoint_upper := fun j => ((repair12422Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12422Cells j).2.2

theorem repair12423Cells (j : Fin 43) :
    0 ≤ (scalarRow12423.table (sourceIndex j)).upper ∧
    (scalarRow12423.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12423.table (sourceIndex j)).centre) /
      (scalarRow12423.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12423.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12423,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12423,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12423,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12423,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12423,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12423,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12423,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12423,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12423,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12423,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12423,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12423,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12423,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12423,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12423,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12423,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12423,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12423,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12423,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12423,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12423,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12423,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12423,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12423,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12423,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12423,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12423,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12423,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12423,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12423,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12423,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12423,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12423,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12423,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12423,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12423,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12423,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12423,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12423,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12423,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12423,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12423,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12423,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12423,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12423,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12423,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12423,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12423,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12423,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12423,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12423,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12423,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12423,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12423,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12423,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12423,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12423,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12423,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12423,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12423,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12423,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12423,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12423,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12423,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12423,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12423,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12423,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12423,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12423,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12423,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12423,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12423,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12423,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12423,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12423,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12423,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12423,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12423,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12423,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12423,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12423,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12423,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12423,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12423,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12423,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12423,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12423 : FrameRepair 12423 scalarRow12423 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12423Cells j).1 (repair12423Cells j).2.1
  endpoint_upper := fun j => ((repair12423Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12423Cells j).2.2

theorem repair12424Cells (j : Fin 43) :
    0 ≤ (scalarRow12424.table (sourceIndex j)).upper ∧
    (scalarRow12424.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12424.table (sourceIndex j)).centre) /
      (scalarRow12424.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12424.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12424,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12424,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12424,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12424,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12424,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12424,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12424,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12424,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12424,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12424,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12424,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12424,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12424,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12424,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12424,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12424,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12424,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12424,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12424,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12424,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12424,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12424,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12424,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12424,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12424,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12424,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12424,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12424,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12424,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12424,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12424,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12424,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12424,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12424,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12424,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12424,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12424,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12424,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12424,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12424,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12424,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12424,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12424,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12424,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12424,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12424,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12424,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12424,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12424,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12424,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12424,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12424,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12424,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12424,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12424,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12424,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12424,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12424,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12424,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12424,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12424,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12424,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12424,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12424,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12424,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12424,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12424,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12424,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12424,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12424,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12424,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12424,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12424,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12424,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12424,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12424,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12424,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12424,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12424,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12424,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12424,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12424,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12424,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12424,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12424,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12424,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12424 : FrameRepair 12424 scalarRow12424 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12424Cells j).1 (repair12424Cells j).2.1
  endpoint_upper := fun j => ((repair12424Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12424Cells j).2.2

end BstLean.Part269
