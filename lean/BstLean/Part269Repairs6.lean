import BstLean.Part269Rows6
import BstLean.Part269RepairCommon
namespace BstLean.Part269
open Real Set BstLean.Part255 BstLean.Part263 BstLean.Part264
theorem repair12500Cells (j : Fin 43) :
    0 ≤ (scalarRow12500.table (sourceIndex j)).upper ∧
    (scalarRow12500.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12500.table (sourceIndex j)).centre) /
      (scalarRow12500.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12500.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12500,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12500,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12500,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12500,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12500,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12500,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12500,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12500,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12500,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12500,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12500,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12500,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12500,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12500,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12500,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12500,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12500,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12500,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12500,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12500,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12500,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12500,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12500,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12500,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12500,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12500,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12500,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12500,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12500,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12500,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12500,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12500,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12500,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12500,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12500,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12500,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12500,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12500,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12500,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12500,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12500,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12500,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12500,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12500,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12500,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12500,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12500,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12500,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12500,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12500,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12500,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12500,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12500,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12500,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12500,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12500,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12500,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12500,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12500,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12500,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12500,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12500,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12500,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12500,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12500,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12500,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12500,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12500,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12500,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12500,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12500,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12500,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12500,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12500,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12500,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12500,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12500,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12500,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12500,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12500,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12500,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12500,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12500,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12500,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12500,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12500,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12500 : FrameRepair 12500 scalarRow12500 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12500Cells j).1 (repair12500Cells j).2.1
  endpoint_upper := fun j => ((repair12500Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12500Cells j).2.2

theorem repair12501Cells (j : Fin 43) :
    0 ≤ (scalarRow12501.table (sourceIndex j)).upper ∧
    (scalarRow12501.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12501.table (sourceIndex j)).centre) /
      (scalarRow12501.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12501.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12501,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12501,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12501,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12501,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12501,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12501,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12501,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12501,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12501,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12501,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12501,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12501,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12501,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12501,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12501,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12501,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12501,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12501,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12501,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12501,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12501,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12501,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12501,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12501,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12501,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12501,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12501,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12501,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12501,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12501,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12501,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12501,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12501,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12501,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12501,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12501,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12501,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12501,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12501,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12501,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12501,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12501,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12501,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12501,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12501,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12501,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12501,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12501,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12501,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12501,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12501,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12501,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12501,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12501,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12501,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12501,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12501,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12501,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12501,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12501,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12501,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12501,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12501,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12501,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12501,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12501,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12501,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12501,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12501,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12501,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12501,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12501,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12501,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12501,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12501,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12501,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12501,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12501,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12501,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12501,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12501,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12501,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12501,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12501,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12501,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12501,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12501 : FrameRepair 12501 scalarRow12501 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12501Cells j).1 (repair12501Cells j).2.1
  endpoint_upper := fun j => ((repair12501Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12501Cells j).2.2

theorem repair12502Cells (j : Fin 43) :
    0 ≤ (scalarRow12502.table (sourceIndex j)).upper ∧
    (scalarRow12502.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12502.table (sourceIndex j)).centre) /
      (scalarRow12502.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12502.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12502,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12502,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12502,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12502,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12502,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12502,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12502,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12502,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12502,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12502,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12502,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12502,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12502,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12502,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12502,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12502,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12502,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12502,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12502,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12502,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12502,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12502,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12502,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12502,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12502,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12502,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12502,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12502,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12502,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12502,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12502,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12502,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12502,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12502,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12502,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12502,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12502,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12502,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12502,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12502,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12502,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12502,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12502,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12502,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12502,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12502,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12502,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12502,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12502,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12502,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12502,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12502,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12502,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12502,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12502,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12502,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12502,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12502,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12502,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12502,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12502,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12502,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12502,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12502,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12502,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12502,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12502,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12502,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12502,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12502,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12502,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12502,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12502,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12502,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12502,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12502,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12502,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12502,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12502,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12502,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12502,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12502,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12502,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12502,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12502,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12502,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12502 : FrameRepair 12502 scalarRow12502 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12502Cells j).1 (repair12502Cells j).2.1
  endpoint_upper := fun j => ((repair12502Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12502Cells j).2.2

theorem repair12503Cells (j : Fin 43) :
    0 ≤ (scalarRow12503.table (sourceIndex j)).upper ∧
    (scalarRow12503.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12503.table (sourceIndex j)).centre) /
      (scalarRow12503.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12503.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12503,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12503,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12503,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12503,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12503,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12503,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12503,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12503,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12503,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12503,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12503,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12503,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12503,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12503,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12503,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12503,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12503,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12503,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12503,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12503,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12503,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12503,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12503,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12503,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12503,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12503,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12503,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12503,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12503,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12503,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12503,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12503,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12503,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12503,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12503,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12503,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12503,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12503,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12503,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12503,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12503,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12503,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12503,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12503,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12503,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12503,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12503,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12503,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12503,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12503,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12503,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12503,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12503,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12503,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12503,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12503,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12503,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12503,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12503,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12503,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12503,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12503,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12503,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12503,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12503,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12503,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12503,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12503,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12503,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12503,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12503,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12503,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12503,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12503,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12503,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12503,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12503,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12503,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12503,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12503,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12503,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12503,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12503,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12503,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12503,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12503,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12503 : FrameRepair 12503 scalarRow12503 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12503Cells j).1 (repair12503Cells j).2.1
  endpoint_upper := fun j => ((repair12503Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12503Cells j).2.2

theorem repair12504Cells (j : Fin 43) :
    0 ≤ (scalarRow12504.table (sourceIndex j)).upper ∧
    (scalarRow12504.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12504.table (sourceIndex j)).centre) /
      (scalarRow12504.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12504.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12504,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12504,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12504,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12504,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12504,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12504,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12504,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12504,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12504,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12504,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12504,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12504,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12504,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12504,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12504,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12504,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12504,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12504,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12504,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12504,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12504,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12504,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12504,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12504,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12504,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12504,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12504,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12504,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12504,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12504,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12504,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12504,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12504,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12504,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12504,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12504,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12504,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12504,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12504,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12504,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12504,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12504,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12504,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12504,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12504,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12504,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12504,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12504,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12504,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12504,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12504,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12504,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12504,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12504,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12504,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12504,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12504,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12504,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12504,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12504,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12504,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12504,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12504,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12504,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12504,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12504,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12504,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12504,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12504,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12504,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12504,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12504,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12504,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12504,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12504,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12504,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12504,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12504,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12504,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12504,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12504,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12504,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12504,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12504,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12504,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12504,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12504 : FrameRepair 12504 scalarRow12504 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12504Cells j).1 (repair12504Cells j).2.1
  endpoint_upper := fun j => ((repair12504Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12504Cells j).2.2

theorem repair12505Cells (j : Fin 43) :
    0 ≤ (scalarRow12505.table (sourceIndex j)).upper ∧
    (scalarRow12505.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12505.table (sourceIndex j)).centre) /
      (scalarRow12505.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12505.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12505,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12505,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12505,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12505,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12505,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12505,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12505,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12505,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12505,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12505,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12505,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12505,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12505,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12505,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12505,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12505,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12505,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12505,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12505,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12505,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12505,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12505,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12505,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12505,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12505,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12505,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12505,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12505,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12505,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12505,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12505,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12505,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12505,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12505,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12505,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12505,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12505,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12505,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12505,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12505,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12505,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12505,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12505,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12505,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12505,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12505,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12505,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12505,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12505,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12505,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12505,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12505,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12505,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12505,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12505,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12505,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12505,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12505,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12505,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12505,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12505,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12505,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12505,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12505,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12505,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12505,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12505,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12505,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12505,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12505,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12505,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12505,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12505,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12505,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12505,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12505,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12505,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12505,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12505,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12505,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12505,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12505,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12505,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12505,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12505,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12505,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12505 : FrameRepair 12505 scalarRow12505 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12505Cells j).1 (repair12505Cells j).2.1
  endpoint_upper := fun j => ((repair12505Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12505Cells j).2.2

theorem repair12506Cells (j : Fin 43) :
    0 ≤ (scalarRow12506.table (sourceIndex j)).upper ∧
    (scalarRow12506.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12506.table (sourceIndex j)).centre) /
      (scalarRow12506.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12506.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12506,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12506,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12506,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12506,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12506,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12506,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12506,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12506,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12506,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12506,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12506,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12506,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12506,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12506,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12506,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12506,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12506,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12506,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12506,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12506,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12506,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12506,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12506,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12506,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12506,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12506,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12506,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12506,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12506,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12506,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12506,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12506,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12506,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12506,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12506,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12506,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12506,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12506,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12506,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12506,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12506,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12506,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12506,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12506,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12506,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12506,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12506,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12506,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12506,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12506,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12506,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12506,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12506,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12506,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12506,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12506,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12506,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12506,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12506,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12506,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12506,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12506,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12506,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12506,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12506,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12506,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12506,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12506,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12506,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12506,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12506,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12506,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12506,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12506,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12506,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12506,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12506,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12506,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12506,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12506,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12506,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12506,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12506,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12506,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12506,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12506,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12506 : FrameRepair 12506 scalarRow12506 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12506Cells j).1 (repair12506Cells j).2.1
  endpoint_upper := fun j => ((repair12506Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12506Cells j).2.2

theorem repair12507Cells (j : Fin 43) :
    0 ≤ (scalarRow12507.table (sourceIndex j)).upper ∧
    (scalarRow12507.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12507.table (sourceIndex j)).centre) /
      (scalarRow12507.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12507.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12507,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12507,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12507,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12507,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12507,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12507,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12507,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12507,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12507,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12507,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12507,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12507,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12507,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12507,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12507,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12507,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12507,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12507,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12507,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12507,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12507,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12507,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12507,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12507,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12507,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12507,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12507,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12507,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12507,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12507,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12507,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12507,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12507,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12507,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12507,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12507,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12507,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12507,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12507,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12507,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12507,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12507,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12507,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12507,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12507,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12507,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12507,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12507,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12507,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12507,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12507,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12507,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12507,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12507,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12507,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12507,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12507,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12507,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12507,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12507,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12507,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12507,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12507,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12507,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12507,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12507,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12507,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12507,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12507,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12507,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12507,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12507,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12507,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12507,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12507,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12507,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12507,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12507,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12507,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12507,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12507,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12507,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12507,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12507,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12507,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12507,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12507 : FrameRepair 12507 scalarRow12507 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12507Cells j).1 (repair12507Cells j).2.1
  endpoint_upper := fun j => ((repair12507Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12507Cells j).2.2

theorem repair12508Cells (j : Fin 43) :
    0 ≤ (scalarRow12508.table (sourceIndex j)).upper ∧
    (scalarRow12508.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12508.table (sourceIndex j)).centre) /
      (scalarRow12508.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12508.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12508,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12508,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12508,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12508,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12508,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12508,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12508,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12508,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12508,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12508,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12508,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12508,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12508,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12508,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12508,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12508,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12508,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12508,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12508,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12508,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12508,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12508,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12508,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12508,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12508,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12508,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12508,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12508,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12508,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12508,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12508,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12508,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12508,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12508,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12508,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12508,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12508,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12508,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12508,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12508,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12508,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12508,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12508,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12508,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12508,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12508,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12508,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12508,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12508,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12508,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12508,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12508,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12508,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12508,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12508,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12508,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12508,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12508,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12508,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12508,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12508,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12508,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12508,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12508,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12508,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12508,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12508,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12508,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12508,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12508,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12508,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12508,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12508,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12508,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12508,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12508,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12508,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12508,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12508,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12508,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12508,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12508,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12508,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12508,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12508,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12508,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12508 : FrameRepair 12508 scalarRow12508 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12508Cells j).1 (repair12508Cells j).2.1
  endpoint_upper := fun j => ((repair12508Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12508Cells j).2.2

theorem repair12509Cells (j : Fin 43) :
    0 ≤ (scalarRow12509.table (sourceIndex j)).upper ∧
    (scalarRow12509.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12509.table (sourceIndex j)).centre) /
      (scalarRow12509.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12509.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12509,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12509,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12509,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12509,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12509,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12509,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12509,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12509,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12509,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12509,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12509,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12509,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12509,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12509,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12509,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12509,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12509,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12509,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12509,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12509,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12509,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12509,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12509,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12509,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12509,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12509,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12509,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12509,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12509,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12509,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12509,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12509,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12509,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12509,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12509,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12509,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12509,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12509,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12509,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12509,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12509,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12509,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12509,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12509,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12509,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12509,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12509,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12509,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12509,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12509,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12509,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12509,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12509,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12509,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12509,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12509,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12509,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12509,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12509,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12509,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12509,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12509,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12509,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12509,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12509,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12509,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12509,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12509,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12509,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12509,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12509,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12509,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12509,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12509,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12509,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12509,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12509,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12509,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12509,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12509,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12509,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12509,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12509,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12509,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12509,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12509,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12509 : FrameRepair 12509 scalarRow12509 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12509Cells j).1 (repair12509Cells j).2.1
  endpoint_upper := fun j => ((repair12509Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12509Cells j).2.2

theorem repair12510Cells (j : Fin 43) :
    0 ≤ (scalarRow12510.table (sourceIndex j)).upper ∧
    (scalarRow12510.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12510.table (sourceIndex j)).centre) /
      (scalarRow12510.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12510.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12510,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12510,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12510,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12510,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12510,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12510,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12510,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12510,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12510,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12510,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12510,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12510,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12510,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12510,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12510,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12510,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12510,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12510,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12510,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12510,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12510,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12510,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12510,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12510,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12510,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12510,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12510,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12510,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12510,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12510,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12510,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12510,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12510,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12510,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12510,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12510,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12510,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12510,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12510,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12510,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12510,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12510,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12510,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12510,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12510,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12510,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12510,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12510,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12510,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12510,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12510,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12510,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12510,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12510,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12510,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12510,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12510,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12510,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12510,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12510,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12510,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12510,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12510,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12510,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12510,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12510,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12510,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12510,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12510,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12510,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12510,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12510,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12510,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12510,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12510,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12510,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12510,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12510,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12510,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12510,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12510,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12510,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12510,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12510,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12510,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12510,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12510 : FrameRepair 12510 scalarRow12510 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12510Cells j).1 (repair12510Cells j).2.1
  endpoint_upper := fun j => ((repair12510Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12510Cells j).2.2

theorem repair12511Cells (j : Fin 43) :
    0 ≤ (scalarRow12511.table (sourceIndex j)).upper ∧
    (scalarRow12511.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12511.table (sourceIndex j)).centre) /
      (scalarRow12511.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12511.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12511,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12511,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12511,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12511,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12511,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12511,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12511,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12511,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12511,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12511,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12511,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12511,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12511,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12511,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12511,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12511,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12511,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12511,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12511,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12511,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12511,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12511,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12511,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12511,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12511,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12511,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12511,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12511,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12511,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12511,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12511,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12511,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12511,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12511,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12511,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12511,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12511,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12511,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12511,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12511,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12511,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12511,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12511,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12511,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12511,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12511,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12511,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12511,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12511,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12511,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12511,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12511,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12511,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12511,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12511,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12511,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12511,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12511,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12511,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12511,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12511,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12511,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12511,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12511,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12511,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12511,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12511,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12511,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12511,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12511,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12511,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12511,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12511,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12511,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12511,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12511,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12511,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12511,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12511,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12511,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12511,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12511,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12511,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12511,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12511,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12511,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12511 : FrameRepair 12511 scalarRow12511 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12511Cells j).1 (repair12511Cells j).2.1
  endpoint_upper := fun j => ((repair12511Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12511Cells j).2.2

theorem repair12512Cells (j : Fin 43) :
    0 ≤ (scalarRow12512.table (sourceIndex j)).upper ∧
    (scalarRow12512.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12512.table (sourceIndex j)).centre) /
      (scalarRow12512.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12512.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12512,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12512,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12512,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12512,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12512,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12512,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12512,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12512,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12512,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12512,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12512,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12512,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12512,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12512,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12512,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12512,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12512,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12512,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12512,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12512,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12512,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12512,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12512,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12512,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12512,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12512,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12512,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12512,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12512,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12512,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12512,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12512,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12512,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12512,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12512,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12512,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12512,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12512,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12512,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12512,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12512,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12512,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12512,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12512,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12512,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12512,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12512,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12512,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12512,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12512,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12512,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12512,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12512,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12512,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12512,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12512,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12512,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12512,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12512,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12512,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12512,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12512,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12512,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12512,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12512,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12512,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12512,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12512,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12512,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12512,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12512,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12512,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12512,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12512,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12512,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12512,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12512,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12512,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12512,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12512,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12512,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12512,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12512,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12512,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12512,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12512,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12512 : FrameRepair 12512 scalarRow12512 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12512Cells j).1 (repair12512Cells j).2.1
  endpoint_upper := fun j => ((repair12512Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12512Cells j).2.2

theorem repair12513Cells (j : Fin 43) :
    0 ≤ (scalarRow12513.table (sourceIndex j)).upper ∧
    (scalarRow12513.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12513.table (sourceIndex j)).centre) /
      (scalarRow12513.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12513.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12513,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12513,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12513,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12513,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12513,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12513,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12513,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12513,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12513,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12513,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12513,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12513,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12513,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12513,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12513,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12513,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12513,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12513,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12513,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12513,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12513,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12513,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12513,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12513,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12513,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12513,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12513,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12513,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12513,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12513,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12513,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12513,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12513,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12513,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12513,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12513,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12513,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12513,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12513,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12513,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12513,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12513,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12513,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12513,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12513,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12513,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12513,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12513,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12513,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12513,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12513,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12513,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12513,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12513,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12513,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12513,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12513,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12513,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12513,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12513,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12513,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12513,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12513,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12513,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12513,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12513,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12513,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12513,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12513,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12513,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12513,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12513,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12513,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12513,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12513,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12513,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12513,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12513,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12513,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12513,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12513,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12513,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12513,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12513,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12513,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12513,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12513 : FrameRepair 12513 scalarRow12513 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12513Cells j).1 (repair12513Cells j).2.1
  endpoint_upper := fun j => ((repair12513Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12513Cells j).2.2

theorem repair12514Cells (j : Fin 43) :
    0 ≤ (scalarRow12514.table (sourceIndex j)).upper ∧
    (scalarRow12514.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12514.table (sourceIndex j)).centre) /
      (scalarRow12514.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12514.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12514,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12514,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12514,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12514,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12514,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12514,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12514,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12514,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12514,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12514,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12514,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12514,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12514,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12514,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12514,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12514,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12514,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12514,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12514,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12514,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12514,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12514,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12514,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12514,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12514,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12514,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12514,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12514,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12514,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12514,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12514,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12514,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12514,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12514,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12514,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12514,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12514,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12514,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12514,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12514,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12514,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12514,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12514,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12514,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12514,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12514,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12514,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12514,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12514,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12514,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12514,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12514,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12514,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12514,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12514,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12514,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12514,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12514,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12514,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12514,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12514,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12514,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12514,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12514,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12514,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12514,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12514,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12514,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12514,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12514,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12514,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12514,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12514,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12514,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12514,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12514,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12514,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12514,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12514,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12514,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12514,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12514,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12514,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12514,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12514,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12514,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12514 : FrameRepair 12514 scalarRow12514 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12514Cells j).1 (repair12514Cells j).2.1
  endpoint_upper := fun j => ((repair12514Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12514Cells j).2.2

theorem repair12515Cells (j : Fin 43) :
    0 ≤ (scalarRow12515.table (sourceIndex j)).upper ∧
    (scalarRow12515.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12515.table (sourceIndex j)).centre) /
      (scalarRow12515.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12515.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12515,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12515,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12515,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12515,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12515,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12515,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12515,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12515,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12515,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12515,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12515,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12515,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12515,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12515,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12515,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12515,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12515,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12515,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12515,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12515,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12515,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12515,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12515,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12515,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12515,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12515,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12515,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12515,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12515,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12515,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12515,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12515,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12515,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12515,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12515,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12515,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12515,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12515,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12515,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12515,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12515,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12515,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12515,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12515,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12515,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12515,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12515,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12515,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12515,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12515,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12515,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12515,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12515,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12515,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12515,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12515,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12515,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12515,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12515,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12515,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12515,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12515,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12515,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12515,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12515,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12515,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12515,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12515,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12515,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12515,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12515,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12515,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12515,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12515,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12515,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12515,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12515,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12515,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12515,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12515,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12515,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12515,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12515,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12515,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12515,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12515,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12515 : FrameRepair 12515 scalarRow12515 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12515Cells j).1 (repair12515Cells j).2.1
  endpoint_upper := fun j => ((repair12515Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12515Cells j).2.2

theorem repair12516Cells (j : Fin 43) :
    0 ≤ (scalarRow12516.table (sourceIndex j)).upper ∧
    (scalarRow12516.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12516.table (sourceIndex j)).centre) /
      (scalarRow12516.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12516.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12516,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12516,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12516,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12516,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12516,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12516,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12516,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12516,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12516,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12516,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12516,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12516,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12516,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12516,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12516,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12516,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12516,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12516,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12516,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12516,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12516,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12516,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12516,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12516,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12516,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12516,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12516,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12516,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12516,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12516,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12516,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12516,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12516,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12516,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12516,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12516,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12516,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12516,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12516,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12516,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12516,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12516,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12516,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12516,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12516,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12516,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12516,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12516,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12516,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12516,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12516,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12516,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12516,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12516,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12516,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12516,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12516,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12516,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12516,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12516,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12516,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12516,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12516,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12516,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12516,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12516,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12516,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12516,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12516,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12516,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12516,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12516,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12516,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12516,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12516,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12516,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12516,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12516,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12516,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12516,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12516,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12516,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12516,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12516,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12516,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12516,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12516 : FrameRepair 12516 scalarRow12516 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12516Cells j).1 (repair12516Cells j).2.1
  endpoint_upper := fun j => ((repair12516Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12516Cells j).2.2

theorem repair12517Cells (j : Fin 43) :
    0 ≤ (scalarRow12517.table (sourceIndex j)).upper ∧
    (scalarRow12517.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12517.table (sourceIndex j)).centre) /
      (scalarRow12517.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12517.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12517,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12517,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12517,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12517,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12517,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12517,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12517,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12517,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12517,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12517,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12517,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12517,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12517,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12517,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12517,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12517,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12517,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12517,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12517,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12517,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12517,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12517,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12517,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12517,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12517,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12517,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12517,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12517,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12517,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12517,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12517,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12517,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12517,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12517,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12517,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12517,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12517,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12517,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12517,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12517,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12517,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12517,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12517,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12517,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12517,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12517,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12517,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12517,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12517,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12517,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12517,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12517,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12517,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12517,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12517,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12517,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12517,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12517,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12517,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12517,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12517,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12517,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12517,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12517,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12517,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12517,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12517,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12517,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12517,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12517,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12517,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12517,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12517,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12517,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12517,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12517,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12517,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12517,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12517,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12517,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12517,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12517,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12517,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12517,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12517,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12517,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12517 : FrameRepair 12517 scalarRow12517 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12517Cells j).1 (repair12517Cells j).2.1
  endpoint_upper := fun j => ((repair12517Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12517Cells j).2.2

theorem repair12518Cells (j : Fin 43) :
    0 ≤ (scalarRow12518.table (sourceIndex j)).upper ∧
    (scalarRow12518.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12518.table (sourceIndex j)).centre) /
      (scalarRow12518.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12518.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12518,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12518,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12518,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12518,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12518,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12518,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12518,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12518,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12518,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12518,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12518,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12518,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12518,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12518,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12518,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12518,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12518,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12518,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12518,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12518,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12518,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12518,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12518,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12518,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12518,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12518,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12518,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12518,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12518,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12518,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12518,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12518,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12518,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12518,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12518,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12518,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12518,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12518,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12518,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12518,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12518,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12518,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12518,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12518,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12518,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12518,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12518,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12518,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12518,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12518,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12518,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12518,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12518,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12518,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12518,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12518,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12518,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12518,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12518,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12518,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12518,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12518,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12518,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12518,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12518,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12518,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12518,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12518,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12518,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12518,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12518,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12518,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12518,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12518,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12518,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12518,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12518,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12518,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12518,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12518,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12518,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12518,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12518,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12518,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12518,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12518,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12518 : FrameRepair 12518 scalarRow12518 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12518Cells j).1 (repair12518Cells j).2.1
  endpoint_upper := fun j => ((repair12518Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12518Cells j).2.2

theorem repair12519Cells (j : Fin 43) :
    0 ≤ (scalarRow12519.table (sourceIndex j)).upper ∧
    (scalarRow12519.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12519.table (sourceIndex j)).centre) /
      (scalarRow12519.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12519.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12519,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12519,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12519,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12519,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12519,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12519,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12519,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12519,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12519,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12519,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12519,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12519,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12519,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12519,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12519,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12519,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12519,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12519,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12519,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12519,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12519,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12519,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12519,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12519,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12519,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12519,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12519,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12519,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12519,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12519,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12519,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12519,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12519,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12519,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12519,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12519,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12519,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12519,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12519,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12519,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12519,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12519,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12519,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12519,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12519,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12519,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12519,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12519,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12519,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12519,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12519,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12519,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12519,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12519,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12519,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12519,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12519,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12519,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12519,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12519,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12519,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12519,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12519,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12519,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12519,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12519,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12519,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12519,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12519,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12519,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12519,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12519,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12519,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12519,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12519,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12519,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12519,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12519,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12519,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12519,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12519,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12519,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12519,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12519,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12519,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12519,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12519 : FrameRepair 12519 scalarRow12519 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12519Cells j).1 (repair12519Cells j).2.1
  endpoint_upper := fun j => ((repair12519Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12519Cells j).2.2

theorem repair12520Cells (j : Fin 43) :
    0 ≤ (scalarRow12520.table (sourceIndex j)).upper ∧
    (scalarRow12520.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12520.table (sourceIndex j)).centre) /
      (scalarRow12520.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12520.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12520,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12520,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12520,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12520,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12520,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12520,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12520,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12520,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12520,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12520,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12520,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12520,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12520,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12520,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12520,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12520,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12520,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12520,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12520,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12520,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12520,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12520,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12520,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12520,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12520,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12520,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12520,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12520,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12520,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12520,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12520,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12520,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12520,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12520,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12520,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12520,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12520,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12520,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12520,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12520,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12520,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12520,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12520,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12520,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12520,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12520,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12520,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12520,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12520,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12520,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12520,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12520,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12520,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12520,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12520,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12520,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12520,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12520,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12520,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12520,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12520,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12520,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12520,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12520,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12520,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12520,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12520,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12520,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12520,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12520,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12520,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12520,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12520,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12520,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12520,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12520,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12520,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12520,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12520,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12520,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12520,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12520,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12520,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12520,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12520,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12520,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12520 : FrameRepair 12520 scalarRow12520 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12520Cells j).1 (repair12520Cells j).2.1
  endpoint_upper := fun j => ((repair12520Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12520Cells j).2.2

theorem repair12521Cells (j : Fin 43) :
    0 ≤ (scalarRow12521.table (sourceIndex j)).upper ∧
    (scalarRow12521.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12521.table (sourceIndex j)).centre) /
      (scalarRow12521.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12521.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12521,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12521,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12521,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12521,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12521,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12521,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12521,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12521,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12521,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12521,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12521,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12521,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12521,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12521,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12521,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12521,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12521,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12521,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12521,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12521,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12521,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12521,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12521,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12521,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12521,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12521,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12521,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12521,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12521,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12521,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12521,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12521,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12521,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12521,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12521,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12521,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12521,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12521,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12521,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12521,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12521,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12521,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12521,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12521,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12521,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12521,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12521,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12521,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12521,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12521,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12521,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12521,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12521,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12521,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12521,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12521,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12521,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12521,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12521,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12521,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12521,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12521,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12521,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12521,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12521,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12521,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12521,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12521,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12521,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12521,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12521,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12521,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12521,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12521,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12521,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12521,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12521,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12521,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12521,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12521,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12521,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12521,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12521,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12521,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12521,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12521,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12521 : FrameRepair 12521 scalarRow12521 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12521Cells j).1 (repair12521Cells j).2.1
  endpoint_upper := fun j => ((repair12521Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12521Cells j).2.2

theorem repair12522Cells (j : Fin 43) :
    0 ≤ (scalarRow12522.table (sourceIndex j)).upper ∧
    (scalarRow12522.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12522.table (sourceIndex j)).centre) /
      (scalarRow12522.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12522.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12522,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12522,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12522,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12522,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12522,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12522,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12522,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12522,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12522,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12522,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12522,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12522,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12522,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12522,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12522,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12522,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12522,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12522,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12522,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12522,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12522,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12522,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12522,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12522,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12522,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12522,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12522,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12522,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12522,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12522,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12522,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12522,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12522,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12522,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12522,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12522,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12522,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12522,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12522,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12522,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12522,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12522,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12522,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12522,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12522,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12522,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12522,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12522,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12522,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12522,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12522,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12522,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12522,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12522,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12522,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12522,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12522,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12522,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12522,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12522,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12522,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12522,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12522,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12522,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12522,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12522,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12522,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12522,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12522,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12522,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12522,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12522,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12522,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12522,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12522,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12522,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12522,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12522,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12522,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12522,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12522,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12522,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12522,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12522,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12522,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12522,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12522 : FrameRepair 12522 scalarRow12522 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12522Cells j).1 (repair12522Cells j).2.1
  endpoint_upper := fun j => ((repair12522Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12522Cells j).2.2

theorem repair12523Cells (j : Fin 43) :
    0 ≤ (scalarRow12523.table (sourceIndex j)).upper ∧
    (scalarRow12523.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12523.table (sourceIndex j)).centre) /
      (scalarRow12523.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12523.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12523,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12523,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12523,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12523,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12523,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12523,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12523,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12523,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12523,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12523,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12523,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12523,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12523,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12523,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12523,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12523,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12523,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12523,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12523,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12523,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12523,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12523,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12523,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12523,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12523,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12523,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12523,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12523,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12523,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12523,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12523,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12523,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12523,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12523,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12523,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12523,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12523,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12523,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12523,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12523,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12523,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12523,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12523,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12523,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12523,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12523,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12523,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12523,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12523,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12523,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12523,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12523,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12523,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12523,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12523,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12523,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12523,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12523,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12523,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12523,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12523,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12523,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12523,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12523,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12523,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12523,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12523,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12523,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12523,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12523,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12523,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12523,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12523,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12523,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12523,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12523,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12523,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12523,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12523,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12523,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12523,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12523,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12523,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12523,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12523,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12523,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12523 : FrameRepair 12523 scalarRow12523 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12523Cells j).1 (repair12523Cells j).2.1
  endpoint_upper := fun j => ((repair12523Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12523Cells j).2.2

theorem repair12524Cells (j : Fin 43) :
    0 ≤ (scalarRow12524.table (sourceIndex j)).upper ∧
    (scalarRow12524.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12524.table (sourceIndex j)).centre) /
      (scalarRow12524.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12524.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12524,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12524,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12524,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12524,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12524,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12524,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12524,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12524,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12524,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12524,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12524,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12524,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12524,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12524,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12524,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12524,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12524,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12524,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12524,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12524,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12524,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12524,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12524,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12524,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12524,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12524,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12524,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12524,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12524,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12524,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12524,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12524,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12524,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12524,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12524,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12524,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12524,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12524,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12524,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12524,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12524,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12524,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12524,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12524,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12524,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12524,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12524,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12524,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12524,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12524,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12524,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12524,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12524,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12524,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12524,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12524,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12524,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12524,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12524,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12524,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12524,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12524,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12524,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12524,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12524,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12524,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12524,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12524,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12524,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12524,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12524,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12524,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12524,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12524,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12524,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12524,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12524,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12524,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12524,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12524,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12524,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12524,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12524,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12524,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12524,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12524,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12524 : FrameRepair 12524 scalarRow12524 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12524Cells j).1 (repair12524Cells j).2.1
  endpoint_upper := fun j => ((repair12524Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12524Cells j).2.2

end BstLean.Part269
