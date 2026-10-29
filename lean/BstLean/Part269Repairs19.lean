import BstLean.Part269Rows19
import BstLean.Part269RepairCommon
namespace BstLean.Part269
open Real Set BstLean.Part255 BstLean.Part263 BstLean.Part264
theorem repair12825Cells (j : Fin 43) :
    0 ≤ (scalarRow12825.table (sourceIndex j)).upper ∧
    (scalarRow12825.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12825.table (sourceIndex j)).centre) /
      (scalarRow12825.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12825.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12825,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12825,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12825,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12825,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12825,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12825,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12825,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12825,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12825,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12825,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12825,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12825,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12825,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12825,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12825,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12825,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12825,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12825,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12825,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12825,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12825,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12825,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12825,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12825,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12825,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12825,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12825,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12825,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12825,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12825,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12825,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12825,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12825,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12825,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12825,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12825,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12825,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12825,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12825,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12825,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12825,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12825,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12825,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12825,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12825,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12825,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12825,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12825,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12825,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12825,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12825,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12825,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12825,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12825,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12825,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12825,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12825,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12825,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12825,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12825,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12825,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12825,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12825,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12825,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12825,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12825,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12825,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12825,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12825,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12825,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12825,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12825,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12825,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12825,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12825,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12825,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12825,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12825,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12825,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12825,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12825,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12825,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12825,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12825,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12825,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12825,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12825 : FrameRepair 12825 scalarRow12825 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12825Cells j).1 (repair12825Cells j).2.1
  endpoint_upper := fun j => ((repair12825Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12825Cells j).2.2

theorem repair12826Cells (j : Fin 43) :
    0 ≤ (scalarRow12826.table (sourceIndex j)).upper ∧
    (scalarRow12826.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12826.table (sourceIndex j)).centre) /
      (scalarRow12826.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12826.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12826,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12826,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12826,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12826,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12826,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12826,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12826,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12826,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12826,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12826,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12826,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12826,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12826,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12826,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12826,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12826,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12826,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12826,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12826,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12826,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12826,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12826,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12826,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12826,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12826,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12826,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12826,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12826,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12826,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12826,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12826,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12826,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12826,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12826,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12826,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12826,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12826,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12826,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12826,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12826,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12826,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12826,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12826,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12826,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12826,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12826,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12826,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12826,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12826,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12826,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12826,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12826,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12826,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12826,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12826,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12826,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12826,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12826,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12826,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12826,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12826,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12826,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12826,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12826,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12826,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12826,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12826,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12826,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12826,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12826,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12826,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12826,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12826,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12826,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12826,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12826,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12826,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12826,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12826,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12826,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12826,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12826,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12826,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12826,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12826,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12826,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12826 : FrameRepair 12826 scalarRow12826 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12826Cells j).1 (repair12826Cells j).2.1
  endpoint_upper := fun j => ((repair12826Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12826Cells j).2.2

theorem repair12827Cells (j : Fin 43) :
    0 ≤ (scalarRow12827.table (sourceIndex j)).upper ∧
    (scalarRow12827.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12827.table (sourceIndex j)).centre) /
      (scalarRow12827.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12827.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12827,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12827,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12827,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12827,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12827,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12827,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12827,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12827,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12827,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12827,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12827,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12827,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12827,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12827,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12827,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12827,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12827,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12827,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12827,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12827,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12827,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12827,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12827,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12827,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12827,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12827,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12827,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12827,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12827,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12827,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12827,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12827,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12827,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12827,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12827,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12827,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12827,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12827,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12827,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12827,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12827,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12827,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12827,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12827,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12827,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12827,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12827,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12827,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12827,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12827,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12827,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12827,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12827,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12827,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12827,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12827,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12827,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12827,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12827,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12827,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12827,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12827,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12827,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12827,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12827,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12827,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12827,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12827,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12827,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12827,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12827,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12827,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12827,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12827,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12827,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12827,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12827,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12827,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12827,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12827,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12827,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12827,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12827,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12827,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12827,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12827,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12827 : FrameRepair 12827 scalarRow12827 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12827Cells j).1 (repair12827Cells j).2.1
  endpoint_upper := fun j => ((repair12827Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12827Cells j).2.2

theorem repair12828Cells (j : Fin 43) :
    0 ≤ (scalarRow12828.table (sourceIndex j)).upper ∧
    (scalarRow12828.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12828.table (sourceIndex j)).centre) /
      (scalarRow12828.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12828.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12828,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12828,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12828,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12828,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12828,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12828,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12828,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12828,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12828,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12828,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12828,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12828,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12828,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12828,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12828,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12828,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12828,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12828,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12828,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12828,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12828,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12828,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12828,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12828,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12828,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12828,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12828,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12828,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12828,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12828,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12828,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12828,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12828,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12828,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12828,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12828,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12828,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12828,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12828,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12828,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12828,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12828,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12828,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12828,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12828,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12828,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12828,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12828,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12828,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12828,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12828,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12828,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12828,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12828,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12828,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12828,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12828,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12828,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12828,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12828,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12828,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12828,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12828,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12828,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12828,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12828,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12828,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12828,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12828,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12828,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12828,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12828,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12828,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12828,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12828,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12828,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12828,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12828,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12828,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12828,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12828,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12828,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12828,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12828,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12828,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12828,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12828 : FrameRepair 12828 scalarRow12828 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12828Cells j).1 (repair12828Cells j).2.1
  endpoint_upper := fun j => ((repair12828Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12828Cells j).2.2

theorem repair12829Cells (j : Fin 43) :
    0 ≤ (scalarRow12829.table (sourceIndex j)).upper ∧
    (scalarRow12829.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12829.table (sourceIndex j)).centre) /
      (scalarRow12829.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12829.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12829,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12829,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12829,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12829,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12829,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12829,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12829,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12829,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12829,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12829,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12829,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12829,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12829,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12829,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12829,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12829,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12829,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12829,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12829,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12829,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12829,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12829,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12829,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12829,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12829,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12829,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12829,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12829,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12829,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12829,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12829,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12829,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12829,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12829,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12829,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12829,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12829,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12829,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12829,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12829,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12829,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12829,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12829,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12829,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12829,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12829,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12829,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12829,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12829,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12829,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12829,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12829,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12829,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12829,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12829,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12829,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12829,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12829,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12829,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12829,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12829,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12829,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12829,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12829,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12829,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12829,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12829,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12829,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12829,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12829,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12829,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12829,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12829,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12829,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12829,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12829,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12829,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12829,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12829,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12829,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12829,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12829,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12829,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12829,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12829,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12829,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12829 : FrameRepair 12829 scalarRow12829 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12829Cells j).1 (repair12829Cells j).2.1
  endpoint_upper := fun j => ((repair12829Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12829Cells j).2.2

theorem repair12830Cells (j : Fin 43) :
    0 ≤ (scalarRow12830.table (sourceIndex j)).upper ∧
    (scalarRow12830.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12830.table (sourceIndex j)).centre) /
      (scalarRow12830.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12830.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12830,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12830,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12830,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12830,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12830,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12830,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12830,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12830,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12830,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12830,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12830,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12830,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12830,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12830,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12830,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12830,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12830,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12830,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12830,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12830,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12830,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12830,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12830,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12830,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12830,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12830,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12830,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12830,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12830,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12830,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12830,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12830,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12830,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12830,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12830,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12830,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12830,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12830,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12830,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12830,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12830,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12830,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12830,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12830,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12830,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12830,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12830,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12830,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12830,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12830,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12830,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12830,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12830,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12830,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12830,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12830,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12830,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12830,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12830,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12830,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12830,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12830,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12830,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12830,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12830,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12830,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12830,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12830,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12830,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12830,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12830,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12830,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12830,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12830,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12830,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12830,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12830,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12830,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12830,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12830,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12830,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12830,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12830,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12830,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12830,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12830,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12830 : FrameRepair 12830 scalarRow12830 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12830Cells j).1 (repair12830Cells j).2.1
  endpoint_upper := fun j => ((repair12830Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12830Cells j).2.2

theorem repair12831Cells (j : Fin 43) :
    0 ≤ (scalarRow12831.table (sourceIndex j)).upper ∧
    (scalarRow12831.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12831.table (sourceIndex j)).centre) /
      (scalarRow12831.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12831.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12831,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12831,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12831,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12831,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12831,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12831,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12831,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12831,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12831,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12831,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12831,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12831,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12831,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12831,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12831,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12831,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12831,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12831,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12831,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12831,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12831,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12831,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12831,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12831,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12831,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12831,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12831,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12831,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12831,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12831,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12831,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12831,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12831,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12831,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12831,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12831,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12831,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12831,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12831,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12831,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12831,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12831,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12831,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12831,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12831,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12831,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12831,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12831,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12831,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12831,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12831,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12831,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12831,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12831,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12831,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12831,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12831,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12831,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12831,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12831,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12831,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12831,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12831,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12831,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12831,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12831,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12831,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12831,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12831,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12831,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12831,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12831,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12831,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12831,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12831,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12831,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12831,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12831,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12831,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12831,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12831,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12831,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12831,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12831,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12831,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12831,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12831 : FrameRepair 12831 scalarRow12831 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12831Cells j).1 (repair12831Cells j).2.1
  endpoint_upper := fun j => ((repair12831Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12831Cells j).2.2

theorem repair12832Cells (j : Fin 43) :
    0 ≤ (scalarRow12832.table (sourceIndex j)).upper ∧
    (scalarRow12832.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12832.table (sourceIndex j)).centre) /
      (scalarRow12832.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12832.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12832,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12832,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12832,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12832,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12832,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12832,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12832,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12832,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12832,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12832,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12832,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12832,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12832,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12832,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12832,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12832,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12832,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12832,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12832,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12832,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12832,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12832,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12832,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12832,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12832,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12832,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12832,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12832,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12832,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12832,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12832,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12832,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12832,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12832,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12832,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12832,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12832,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12832,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12832,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12832,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12832,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12832,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12832,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12832,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12832,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12832,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12832,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12832,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12832,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12832,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12832,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12832,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12832,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12832,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12832,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12832,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12832,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12832,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12832,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12832,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12832,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12832,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12832,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12832,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12832,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12832,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12832,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12832,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12832,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12832,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12832,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12832,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12832,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12832,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12832,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12832,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12832,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12832,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12832,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12832,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12832,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12832,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12832,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12832,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12832,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12832,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12832 : FrameRepair 12832 scalarRow12832 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12832Cells j).1 (repair12832Cells j).2.1
  endpoint_upper := fun j => ((repair12832Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12832Cells j).2.2

theorem repair12833Cells (j : Fin 43) :
    0 ≤ (scalarRow12833.table (sourceIndex j)).upper ∧
    (scalarRow12833.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12833.table (sourceIndex j)).centre) /
      (scalarRow12833.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12833.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12833,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12833,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12833,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12833,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12833,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12833,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12833,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12833,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12833,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12833,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12833,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12833,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12833,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12833,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12833,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12833,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12833,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12833,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12833,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12833,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12833,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12833,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12833,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12833,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12833,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12833,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12833,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12833,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12833,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12833,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12833,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12833,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12833,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12833,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12833,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12833,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12833,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12833,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12833,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12833,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12833,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12833,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12833,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12833,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12833,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12833,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12833,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12833,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12833,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12833,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12833,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12833,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12833,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12833,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12833,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12833,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12833,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12833,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12833,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12833,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12833,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12833,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12833,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12833,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12833,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12833,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12833,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12833,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12833,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12833,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12833,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12833,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12833,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12833,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12833,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12833,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12833,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12833,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12833,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12833,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12833,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12833,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12833,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12833,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12833,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12833,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12833 : FrameRepair 12833 scalarRow12833 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12833Cells j).1 (repair12833Cells j).2.1
  endpoint_upper := fun j => ((repair12833Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12833Cells j).2.2

theorem repair12834Cells (j : Fin 43) :
    0 ≤ (scalarRow12834.table (sourceIndex j)).upper ∧
    (scalarRow12834.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12834.table (sourceIndex j)).centre) /
      (scalarRow12834.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12834.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12834,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12834,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12834,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12834,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12834,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12834,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12834,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12834,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12834,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12834,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12834,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12834,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12834,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12834,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12834,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12834,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12834,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12834,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12834,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12834,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12834,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12834,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12834,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12834,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12834,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12834,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12834,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12834,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12834,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12834,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12834,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12834,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12834,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12834,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12834,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12834,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12834,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12834,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12834,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12834,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12834,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12834,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12834,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12834,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12834,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12834,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12834,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12834,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12834,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12834,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12834,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12834,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12834,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12834,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12834,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12834,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12834,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12834,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12834,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12834,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12834,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12834,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12834,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12834,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12834,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12834,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12834,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12834,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12834,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12834,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12834,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12834,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12834,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12834,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12834,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12834,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12834,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12834,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12834,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12834,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12834,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12834,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12834,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12834,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12834,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12834,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12834 : FrameRepair 12834 scalarRow12834 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12834Cells j).1 (repair12834Cells j).2.1
  endpoint_upper := fun j => ((repair12834Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12834Cells j).2.2

theorem repair12835Cells (j : Fin 43) :
    0 ≤ (scalarRow12835.table (sourceIndex j)).upper ∧
    (scalarRow12835.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12835.table (sourceIndex j)).centre) /
      (scalarRow12835.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12835.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12835,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12835,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12835,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12835,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12835,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12835,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12835,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12835,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12835,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12835,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12835,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12835,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12835,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12835,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12835,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12835,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12835,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12835,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12835,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12835,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12835,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12835,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12835,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12835,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12835,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12835,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12835,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12835,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12835,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12835,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12835,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12835,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12835,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12835,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12835,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12835,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12835,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12835,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12835,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12835,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12835,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12835,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12835,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12835,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12835,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12835,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12835,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12835,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12835,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12835,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12835,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12835,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12835,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12835,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12835,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12835,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12835,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12835,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12835,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12835,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12835,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12835,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12835,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12835,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12835,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12835,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12835,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12835,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12835,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12835,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12835,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12835,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12835,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12835,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12835,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12835,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12835,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12835,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12835,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12835,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12835,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12835,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12835,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12835,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12835,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12835,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12835 : FrameRepair 12835 scalarRow12835 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12835Cells j).1 (repair12835Cells j).2.1
  endpoint_upper := fun j => ((repair12835Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12835Cells j).2.2

theorem repair12836Cells (j : Fin 43) :
    0 ≤ (scalarRow12836.table (sourceIndex j)).upper ∧
    (scalarRow12836.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12836.table (sourceIndex j)).centre) /
      (scalarRow12836.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12836.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12836,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12836,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12836,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12836,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12836,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12836,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12836,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12836,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12836,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12836,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12836,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12836,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12836,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12836,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12836,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12836,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12836,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12836,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12836,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12836,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12836,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12836,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12836,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12836,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12836,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12836,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12836,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12836,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12836,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12836,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12836,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12836,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12836,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12836,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12836,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12836,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12836,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12836,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12836,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12836,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12836,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12836,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12836,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12836,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12836,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12836,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12836,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12836,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12836,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12836,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12836,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12836,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12836,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12836,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12836,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12836,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12836,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12836,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12836,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12836,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12836,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12836,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12836,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12836,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12836,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12836,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12836,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12836,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12836,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12836,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12836,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12836,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12836,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12836,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12836,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12836,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12836,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12836,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12836,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12836,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12836,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12836,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12836,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12836,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12836,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12836,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12836 : FrameRepair 12836 scalarRow12836 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12836Cells j).1 (repair12836Cells j).2.1
  endpoint_upper := fun j => ((repair12836Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12836Cells j).2.2

theorem repair12837Cells (j : Fin 43) :
    0 ≤ (scalarRow12837.table (sourceIndex j)).upper ∧
    (scalarRow12837.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12837.table (sourceIndex j)).centre) /
      (scalarRow12837.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12837.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12837,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12837,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12837,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12837,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12837,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12837,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12837,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12837,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12837,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12837,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12837,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12837,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12837,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12837,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12837,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12837,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12837,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12837,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12837,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12837,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12837,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12837,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12837,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12837,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12837,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12837,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12837,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12837,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12837,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12837,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12837,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12837,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12837,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12837,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12837,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12837,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12837,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12837,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12837,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12837,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12837,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12837,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12837,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12837,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12837,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12837,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12837,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12837,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12837,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12837,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12837,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12837,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12837,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12837,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12837,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12837,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12837,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12837,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12837,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12837,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12837,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12837,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12837,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12837,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12837,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12837,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12837,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12837,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12837,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12837,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12837,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12837,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12837,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12837,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12837,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12837,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12837,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12837,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12837,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12837,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12837,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12837,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12837,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12837,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12837,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12837,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12837 : FrameRepair 12837 scalarRow12837 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12837Cells j).1 (repair12837Cells j).2.1
  endpoint_upper := fun j => ((repair12837Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12837Cells j).2.2

theorem repair12838Cells (j : Fin 43) :
    0 ≤ (scalarRow12838.table (sourceIndex j)).upper ∧
    (scalarRow12838.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12838.table (sourceIndex j)).centre) /
      (scalarRow12838.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12838.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12838,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12838,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12838,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12838,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12838,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12838,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12838,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12838,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12838,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12838,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12838,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12838,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12838,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12838,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12838,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12838,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12838,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12838,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12838,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12838,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12838,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12838,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12838,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12838,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12838,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12838,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12838,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12838,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12838,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12838,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12838,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12838,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12838,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12838,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12838,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12838,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12838,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12838,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12838,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12838,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12838,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12838,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12838,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12838,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12838,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12838,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12838,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12838,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12838,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12838,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12838,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12838,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12838,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12838,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12838,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12838,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12838,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12838,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12838,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12838,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12838,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12838,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12838,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12838,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12838,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12838,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12838,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12838,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12838,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12838,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12838,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12838,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12838,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12838,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12838,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12838,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12838,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12838,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12838,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12838,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12838,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12838,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12838,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12838,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12838,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12838,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12838 : FrameRepair 12838 scalarRow12838 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12838Cells j).1 (repair12838Cells j).2.1
  endpoint_upper := fun j => ((repair12838Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12838Cells j).2.2

theorem repair12839Cells (j : Fin 43) :
    0 ≤ (scalarRow12839.table (sourceIndex j)).upper ∧
    (scalarRow12839.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12839.table (sourceIndex j)).centre) /
      (scalarRow12839.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12839.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12839,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12839,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12839,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12839,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12839,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12839,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12839,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12839,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12839,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12839,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12839,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12839,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12839,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12839,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12839,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12839,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12839,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12839,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12839,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12839,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12839,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12839,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12839,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12839,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12839,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12839,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12839,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12839,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12839,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12839,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12839,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12839,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12839,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12839,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12839,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12839,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12839,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12839,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12839,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12839,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12839,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12839,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12839,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12839,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12839,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12839,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12839,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12839,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12839,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12839,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12839,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12839,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12839,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12839,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12839,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12839,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12839,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12839,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12839,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12839,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12839,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12839,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12839,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12839,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12839,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12839,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12839,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12839,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12839,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12839,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12839,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12839,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12839,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12839,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12839,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12839,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12839,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12839,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12839,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12839,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12839,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12839,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12839,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12839,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12839,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12839,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12839 : FrameRepair 12839 scalarRow12839 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12839Cells j).1 (repair12839Cells j).2.1
  endpoint_upper := fun j => ((repair12839Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12839Cells j).2.2

theorem repair12840Cells (j : Fin 43) :
    0 ≤ (scalarRow12840.table (sourceIndex j)).upper ∧
    (scalarRow12840.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12840.table (sourceIndex j)).centre) /
      (scalarRow12840.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12840.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12840,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12840,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12840,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12840,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12840,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12840,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12840,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12840,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12840,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12840,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12840,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12840,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12840,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12840,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12840,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12840,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12840,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12840,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12840,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12840,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12840,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12840,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12840,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12840,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12840,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12840,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12840,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12840,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12840,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12840,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12840,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12840,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12840,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12840,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12840,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12840,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12840,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12840,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12840,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12840,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12840,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12840,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12840,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12840,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12840,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12840,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12840,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12840,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12840,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12840,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12840,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12840,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12840,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12840,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12840,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12840,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12840,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12840,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12840,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12840,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12840,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12840,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12840,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12840,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12840,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12840,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12840,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12840,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12840,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12840,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12840,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12840,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12840,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12840,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12840,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12840,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12840,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12840,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12840,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12840,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12840,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12840,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12840,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12840,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12840,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12840,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12840 : FrameRepair 12840 scalarRow12840 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12840Cells j).1 (repair12840Cells j).2.1
  endpoint_upper := fun j => ((repair12840Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12840Cells j).2.2

theorem repair12841Cells (j : Fin 43) :
    0 ≤ (scalarRow12841.table (sourceIndex j)).upper ∧
    (scalarRow12841.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12841.table (sourceIndex j)).centre) /
      (scalarRow12841.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12841.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12841,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12841,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12841,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12841,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12841,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12841,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12841,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12841,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12841,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12841,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12841,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12841,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12841,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12841,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12841,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12841,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12841,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12841,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12841,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12841,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12841,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12841,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12841,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12841,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12841,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12841,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12841,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12841,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12841,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12841,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12841,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12841,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12841,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12841,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12841,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12841,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12841,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12841,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12841,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12841,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12841,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12841,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12841,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12841,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12841,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12841,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12841,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12841,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12841,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12841,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12841,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12841,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12841,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12841,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12841,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12841,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12841,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12841,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12841,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12841,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12841,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12841,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12841,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12841,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12841,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12841,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12841,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12841,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12841,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12841,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12841,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12841,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12841,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12841,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12841,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12841,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12841,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12841,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12841,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12841,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12841,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12841,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12841,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12841,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12841,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12841,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12841 : FrameRepair 12841 scalarRow12841 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12841Cells j).1 (repair12841Cells j).2.1
  endpoint_upper := fun j => ((repair12841Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12841Cells j).2.2

theorem repair12842Cells (j : Fin 43) :
    0 ≤ (scalarRow12842.table (sourceIndex j)).upper ∧
    (scalarRow12842.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12842.table (sourceIndex j)).centre) /
      (scalarRow12842.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12842.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12842,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12842,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12842,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12842,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12842,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12842,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12842,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12842,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12842,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12842,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12842,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12842,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12842,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12842,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12842,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12842,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12842,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12842,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12842,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12842,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12842,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12842,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12842,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12842,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12842,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12842,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12842,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12842,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12842,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12842,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12842,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12842,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12842,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12842,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12842,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12842,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12842,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12842,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12842,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12842,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12842,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12842,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12842,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12842,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12842,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12842,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12842,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12842,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12842,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12842,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12842,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12842,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12842,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12842,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12842,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12842,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12842,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12842,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12842,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12842,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12842,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12842,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12842,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12842,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12842,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12842,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12842,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12842,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12842,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12842,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12842,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12842,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12842,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12842,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12842,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12842,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12842,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12842,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12842,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12842,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12842,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12842,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12842,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12842,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12842,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12842,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12842 : FrameRepair 12842 scalarRow12842 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12842Cells j).1 (repair12842Cells j).2.1
  endpoint_upper := fun j => ((repair12842Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12842Cells j).2.2

theorem repair12843Cells (j : Fin 43) :
    0 ≤ (scalarRow12843.table (sourceIndex j)).upper ∧
    (scalarRow12843.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12843.table (sourceIndex j)).centre) /
      (scalarRow12843.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12843.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12843,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12843,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12843,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12843,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12843,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12843,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12843,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12843,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12843,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12843,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12843,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12843,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12843,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12843,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12843,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12843,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12843,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12843,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12843,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12843,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12843,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12843,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12843,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12843,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12843,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12843,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12843,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12843,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12843,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12843,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12843,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12843,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12843,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12843,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12843,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12843,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12843,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12843,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12843,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12843,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12843,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12843,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12843,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12843,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12843,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12843,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12843,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12843,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12843,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12843,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12843,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12843,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12843,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12843,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12843,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12843,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12843,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12843,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12843,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12843,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12843,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12843,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12843,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12843,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12843,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12843,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12843,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12843,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12843,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12843,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12843,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12843,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12843,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12843,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12843,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12843,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12843,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12843,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12843,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12843,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12843,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12843,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12843,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12843,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12843,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12843,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12843 : FrameRepair 12843 scalarRow12843 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12843Cells j).1 (repair12843Cells j).2.1
  endpoint_upper := fun j => ((repair12843Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12843Cells j).2.2

theorem repair12844Cells (j : Fin 43) :
    0 ≤ (scalarRow12844.table (sourceIndex j)).upper ∧
    (scalarRow12844.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12844.table (sourceIndex j)).centre) /
      (scalarRow12844.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12844.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12844,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12844,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12844,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12844,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12844,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12844,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12844,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12844,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12844,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12844,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12844,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12844,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12844,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12844,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12844,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12844,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12844,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12844,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12844,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12844,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12844,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12844,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12844,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12844,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12844,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12844,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12844,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12844,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12844,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12844,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12844,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12844,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12844,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12844,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12844,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12844,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12844,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12844,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12844,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12844,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12844,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12844,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12844,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12844,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12844,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12844,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12844,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12844,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12844,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12844,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12844,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12844,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12844,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12844,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12844,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12844,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12844,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12844,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12844,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12844,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12844,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12844,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12844,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12844,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12844,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12844,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12844,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12844,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12844,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12844,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12844,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12844,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12844,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12844,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12844,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12844,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12844,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12844,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12844,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12844,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12844,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12844,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12844,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12844,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12844,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12844,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12844 : FrameRepair 12844 scalarRow12844 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12844Cells j).1 (repair12844Cells j).2.1
  endpoint_upper := fun j => ((repair12844Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12844Cells j).2.2

theorem repair12845Cells (j : Fin 43) :
    0 ≤ (scalarRow12845.table (sourceIndex j)).upper ∧
    (scalarRow12845.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12845.table (sourceIndex j)).centre) /
      (scalarRow12845.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12845.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12845,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12845,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12845,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12845,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12845,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12845,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12845,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12845,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12845,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12845,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12845,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12845,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12845,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12845,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12845,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12845,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12845,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12845,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12845,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12845,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12845,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12845,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12845,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12845,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12845,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12845,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12845,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12845,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12845,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12845,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12845,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12845,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12845,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12845,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12845,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12845,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12845,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12845,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12845,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12845,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12845,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12845,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12845,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12845,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12845,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12845,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12845,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12845,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12845,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12845,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12845,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12845,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12845,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12845,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12845,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12845,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12845,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12845,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12845,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12845,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12845,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12845,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12845,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12845,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12845,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12845,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12845,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12845,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12845,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12845,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12845,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12845,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12845,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12845,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12845,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12845,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12845,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12845,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12845,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12845,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12845,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12845,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12845,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12845,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12845,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12845,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12845 : FrameRepair 12845 scalarRow12845 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12845Cells j).1 (repair12845Cells j).2.1
  endpoint_upper := fun j => ((repair12845Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12845Cells j).2.2

theorem repair12846Cells (j : Fin 43) :
    0 ≤ (scalarRow12846.table (sourceIndex j)).upper ∧
    (scalarRow12846.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12846.table (sourceIndex j)).centre) /
      (scalarRow12846.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12846.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12846,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12846,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12846,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12846,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12846,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12846,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12846,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12846,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12846,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12846,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12846,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12846,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12846,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12846,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12846,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12846,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12846,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12846,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12846,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12846,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12846,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12846,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12846,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12846,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12846,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12846,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12846,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12846,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12846,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12846,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12846,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12846,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12846,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12846,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12846,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12846,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12846,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12846,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12846,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12846,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12846,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12846,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12846,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12846,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12846,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12846,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12846,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12846,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12846,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12846,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12846,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12846,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12846,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12846,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12846,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12846,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12846,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12846,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12846,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12846,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12846,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12846,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12846,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12846,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12846,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12846,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12846,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12846,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12846,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12846,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12846,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12846,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12846,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12846,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12846,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12846,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12846,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12846,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12846,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12846,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12846,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12846,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12846,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12846,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12846,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12846,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12846 : FrameRepair 12846 scalarRow12846 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12846Cells j).1 (repair12846Cells j).2.1
  endpoint_upper := fun j => ((repair12846Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12846Cells j).2.2

theorem repair12847Cells (j : Fin 43) :
    0 ≤ (scalarRow12847.table (sourceIndex j)).upper ∧
    (scalarRow12847.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12847.table (sourceIndex j)).centre) /
      (scalarRow12847.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12847.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12847,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12847,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12847,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12847,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12847,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12847,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12847,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12847,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12847,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12847,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12847,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12847,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12847,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12847,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12847,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12847,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12847,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12847,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12847,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12847,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12847,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12847,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12847,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12847,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12847,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12847,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12847,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12847,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12847,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12847,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12847,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12847,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12847,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12847,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12847,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12847,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12847,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12847,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12847,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12847,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12847,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12847,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12847,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12847,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12847,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12847,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12847,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12847,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12847,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12847,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12847,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12847,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12847,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12847,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12847,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12847,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12847,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12847,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12847,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12847,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12847,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12847,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12847,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12847,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12847,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12847,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12847,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12847,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12847,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12847,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12847,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12847,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12847,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12847,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12847,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12847,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12847,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12847,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12847,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12847,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12847,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12847,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12847,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12847,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12847,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12847,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12847 : FrameRepair 12847 scalarRow12847 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12847Cells j).1 (repair12847Cells j).2.1
  endpoint_upper := fun j => ((repair12847Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12847Cells j).2.2

theorem repair12848Cells (j : Fin 43) :
    0 ≤ (scalarRow12848.table (sourceIndex j)).upper ∧
    (scalarRow12848.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12848.table (sourceIndex j)).centre) /
      (scalarRow12848.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12848.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12848,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12848,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12848,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12848,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12848,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12848,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12848,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12848,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12848,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12848,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12848,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12848,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12848,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12848,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12848,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12848,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12848,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12848,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12848,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12848,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12848,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12848,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12848,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12848,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12848,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12848,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12848,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12848,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12848,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12848,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12848,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12848,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12848,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12848,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12848,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12848,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12848,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12848,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12848,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12848,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12848,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12848,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12848,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12848,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12848,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12848,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12848,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12848,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12848,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12848,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12848,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12848,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12848,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12848,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12848,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12848,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12848,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12848,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12848,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12848,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12848,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12848,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12848,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12848,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12848,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12848,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12848,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12848,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12848,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12848,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12848,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12848,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12848,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12848,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12848,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12848,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12848,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12848,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12848,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12848,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12848,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12848,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12848,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12848,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12848,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12848,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12848 : FrameRepair 12848 scalarRow12848 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12848Cells j).1 (repair12848Cells j).2.1
  endpoint_upper := fun j => ((repair12848Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12848Cells j).2.2

theorem repair12849Cells (j : Fin 43) :
    0 ≤ (scalarRow12849.table (sourceIndex j)).upper ∧
    (scalarRow12849.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12849.table (sourceIndex j)).centre) /
      (scalarRow12849.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12849.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12849,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12849,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12849,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12849,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12849,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12849,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12849,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12849,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12849,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12849,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12849,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12849,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12849,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12849,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12849,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12849,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12849,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12849,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12849,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12849,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12849,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12849,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12849,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12849,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12849,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12849,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12849,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12849,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12849,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12849,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12849,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12849,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12849,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12849,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12849,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12849,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12849,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12849,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12849,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12849,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12849,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12849,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12849,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12849,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12849,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12849,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12849,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12849,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12849,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12849,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12849,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12849,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12849,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12849,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12849,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12849,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12849,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12849,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12849,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12849,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12849,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12849,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12849,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12849,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12849,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12849,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12849,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12849,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12849,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12849,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12849,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12849,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12849,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12849,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12849,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12849,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12849,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12849,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12849,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12849,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12849,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12849,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12849,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12849,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12849,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12849,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12849 : FrameRepair 12849 scalarRow12849 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12849Cells j).1 (repair12849Cells j).2.1
  endpoint_upper := fun j => ((repair12849Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12849Cells j).2.2

end BstLean.Part269
