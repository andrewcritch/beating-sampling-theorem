import BstLean.Part269Rows24
import BstLean.Part269RepairCommon
namespace BstLean.Part269
open Real Set BstLean.Part255 BstLean.Part263 BstLean.Part264
theorem repair12950Cells (j : Fin 43) :
    0 ≤ (scalarRow12950.table (sourceIndex j)).upper ∧
    (scalarRow12950.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12950.table (sourceIndex j)).centre) /
      (scalarRow12950.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12950.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12950,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12950,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12950,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12950,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12950,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12950,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12950,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12950,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12950,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12950,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12950,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12950,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12950,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12950,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12950,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12950,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12950,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12950,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12950,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12950,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12950,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12950,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12950,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12950,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12950,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12950,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12950,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12950,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12950,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12950,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12950,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12950,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12950,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12950,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12950,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12950,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12950,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12950,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12950,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12950,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12950,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12950,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12950,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12950,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12950,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12950,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12950,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12950,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12950,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12950,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12950,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12950,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12950,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12950,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12950,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12950,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12950,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12950,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12950,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12950,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12950,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12950,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12950,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12950,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12950,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12950,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12950,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12950,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12950,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12950,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12950,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12950,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12950,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12950,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12950,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12950,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12950,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12950,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12950,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12950,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12950,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12950,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12950,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12950,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12950,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12950,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12950 : FrameRepair 12950 scalarRow12950 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12950Cells j).1 (repair12950Cells j).2.1
  endpoint_upper := fun j => ((repair12950Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12950Cells j).2.2

theorem repair12951Cells (j : Fin 43) :
    0 ≤ (scalarRow12951.table (sourceIndex j)).upper ∧
    (scalarRow12951.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12951.table (sourceIndex j)).centre) /
      (scalarRow12951.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12951.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12951,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12951,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12951,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12951,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12951,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12951,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12951,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12951,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12951,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12951,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12951,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12951,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12951,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12951,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12951,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12951,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12951,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12951,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12951,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12951,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12951,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12951,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12951,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12951,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12951,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12951,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12951,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12951,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12951,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12951,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12951,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12951,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12951,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12951,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12951,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12951,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12951,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12951,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12951,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12951,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12951,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12951,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12951,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12951,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12951,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12951,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12951,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12951,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12951,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12951,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12951,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12951,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12951,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12951,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12951,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12951,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12951,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12951,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12951,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12951,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12951,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12951,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12951,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12951,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12951,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12951,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12951,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12951,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12951,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12951,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12951,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12951,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12951,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12951,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12951,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12951,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12951,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12951,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12951,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12951,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12951,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12951,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12951,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12951,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12951,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12951,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12951 : FrameRepair 12951 scalarRow12951 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12951Cells j).1 (repair12951Cells j).2.1
  endpoint_upper := fun j => ((repair12951Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12951Cells j).2.2

theorem repair12952Cells (j : Fin 43) :
    0 ≤ (scalarRow12952.table (sourceIndex j)).upper ∧
    (scalarRow12952.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12952.table (sourceIndex j)).centre) /
      (scalarRow12952.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12952.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12952,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12952,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12952,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12952,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12952,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12952,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12952,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12952,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12952,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12952,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12952,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12952,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12952,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12952,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12952,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12952,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12952,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12952,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12952,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12952,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12952,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12952,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12952,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12952,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12952,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12952,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12952,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12952,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12952,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12952,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12952,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12952,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12952,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12952,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12952,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12952,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12952,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12952,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12952,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12952,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12952,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12952,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12952,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12952,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12952,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12952,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12952,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12952,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12952,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12952,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12952,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12952,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12952,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12952,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12952,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12952,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12952,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12952,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12952,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12952,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12952,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12952,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12952,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12952,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12952,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12952,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12952,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12952,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12952,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12952,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12952,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12952,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12952,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12952,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12952,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12952,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12952,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12952,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12952,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12952,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12952,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12952,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12952,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12952,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12952,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12952,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12952 : FrameRepair 12952 scalarRow12952 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12952Cells j).1 (repair12952Cells j).2.1
  endpoint_upper := fun j => ((repair12952Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12952Cells j).2.2

theorem repair12953Cells (j : Fin 43) :
    0 ≤ (scalarRow12953.table (sourceIndex j)).upper ∧
    (scalarRow12953.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12953.table (sourceIndex j)).centre) /
      (scalarRow12953.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12953.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12953,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12953,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12953,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12953,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12953,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12953,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12953,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12953,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12953,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12953,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12953,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12953,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12953,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12953,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12953,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12953,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12953,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12953,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12953,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12953,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12953,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12953,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12953,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12953,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12953,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12953,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12953,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12953,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12953,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12953,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12953,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12953,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12953,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12953,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12953,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12953,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12953,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12953,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12953,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12953,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12953,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12953,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12953,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12953,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12953,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12953,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12953,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12953,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12953,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12953,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12953,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12953,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12953,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12953,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12953,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12953,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12953,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12953,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12953,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12953,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12953,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12953,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12953,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12953,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12953,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12953,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12953,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12953,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12953,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12953,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12953,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12953,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12953,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12953,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12953,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12953,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12953,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12953,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12953,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12953,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12953,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12953,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12953,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12953,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12953,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12953,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12953 : FrameRepair 12953 scalarRow12953 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12953Cells j).1 (repair12953Cells j).2.1
  endpoint_upper := fun j => ((repair12953Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12953Cells j).2.2

theorem repair12954Cells (j : Fin 43) :
    0 ≤ (scalarRow12954.table (sourceIndex j)).upper ∧
    (scalarRow12954.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12954.table (sourceIndex j)).centre) /
      (scalarRow12954.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12954.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12954,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12954,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12954,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12954,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12954,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12954,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12954,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12954,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12954,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12954,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12954,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12954,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12954,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12954,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12954,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12954,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12954,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12954,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12954,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12954,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12954,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12954,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12954,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12954,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12954,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12954,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12954,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12954,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12954,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12954,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12954,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12954,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12954,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12954,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12954,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12954,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12954,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12954,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12954,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12954,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12954,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12954,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12954,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12954,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12954,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12954,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12954,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12954,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12954,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12954,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12954,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12954,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12954,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12954,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12954,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12954,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12954,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12954,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12954,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12954,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12954,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12954,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12954,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12954,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12954,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12954,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12954,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12954,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12954,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12954,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12954,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12954,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12954,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12954,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12954,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12954,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12954,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12954,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12954,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12954,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12954,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12954,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12954,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12954,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12954,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12954,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12954 : FrameRepair 12954 scalarRow12954 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12954Cells j).1 (repair12954Cells j).2.1
  endpoint_upper := fun j => ((repair12954Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12954Cells j).2.2

theorem repair12955Cells (j : Fin 43) :
    0 ≤ (scalarRow12955.table (sourceIndex j)).upper ∧
    (scalarRow12955.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12955.table (sourceIndex j)).centre) /
      (scalarRow12955.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12955.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12955,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12955,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12955,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12955,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12955,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12955,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12955,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12955,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12955,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12955,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12955,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12955,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12955,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12955,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12955,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12955,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12955,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12955,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12955,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12955,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12955,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12955,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12955,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12955,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12955,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12955,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12955,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12955,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12955,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12955,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12955,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12955,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12955,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12955,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12955,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12955,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12955,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12955,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12955,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12955,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12955,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12955,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12955,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12955,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12955,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12955,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12955,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12955,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12955,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12955,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12955,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12955,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12955,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12955,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12955,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12955,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12955,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12955,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12955,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12955,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12955,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12955,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12955,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12955,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12955,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12955,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12955,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12955,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12955,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12955,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12955,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12955,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12955,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12955,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12955,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12955,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12955,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12955,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12955,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12955,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12955,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12955,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12955,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12955,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12955,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12955,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12955 : FrameRepair 12955 scalarRow12955 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12955Cells j).1 (repair12955Cells j).2.1
  endpoint_upper := fun j => ((repair12955Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12955Cells j).2.2

theorem repair12956Cells (j : Fin 43) :
    0 ≤ (scalarRow12956.table (sourceIndex j)).upper ∧
    (scalarRow12956.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12956.table (sourceIndex j)).centre) /
      (scalarRow12956.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12956.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12956,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12956,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12956,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12956,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12956,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12956,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12956,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12956,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12956,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12956,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12956,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12956,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12956,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12956,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12956,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12956,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12956,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12956,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12956,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12956,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12956,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12956,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12956,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12956,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12956,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12956,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12956,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12956,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12956,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12956,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12956,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12956,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12956,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12956,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12956,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12956,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12956,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12956,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12956,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12956,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12956,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12956,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12956,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12956,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12956,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12956,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12956,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12956,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12956,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12956,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12956,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12956,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12956,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12956,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12956,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12956,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12956,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12956,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12956,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12956,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12956,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12956,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12956,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12956,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12956,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12956,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12956,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12956,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12956,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12956,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12956,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12956,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12956,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12956,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12956,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12956,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12956,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12956,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12956,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12956,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12956,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12956,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12956,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12956,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12956,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12956,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12956 : FrameRepair 12956 scalarRow12956 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12956Cells j).1 (repair12956Cells j).2.1
  endpoint_upper := fun j => ((repair12956Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12956Cells j).2.2

theorem repair12957Cells (j : Fin 43) :
    0 ≤ (scalarRow12957.table (sourceIndex j)).upper ∧
    (scalarRow12957.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12957.table (sourceIndex j)).centre) /
      (scalarRow12957.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12957.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12957,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12957,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12957,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12957,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12957,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12957,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12957,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12957,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12957,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12957,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12957,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12957,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12957,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12957,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12957,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12957,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12957,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12957,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12957,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12957,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12957,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12957,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12957,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12957,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12957,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12957,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12957,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12957,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12957,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12957,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12957,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12957,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12957,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12957,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12957,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12957,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12957,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12957,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12957,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12957,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12957,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12957,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12957,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12957,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12957,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12957,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12957,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12957,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12957,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12957,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12957,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12957,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12957,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12957,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12957,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12957,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12957,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12957,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12957,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12957,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12957,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12957,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12957,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12957,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12957,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12957,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12957,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12957,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12957,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12957,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12957,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12957,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12957,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12957,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12957,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12957,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12957,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12957,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12957,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12957,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12957,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12957,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12957,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12957,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12957,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12957,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12957 : FrameRepair 12957 scalarRow12957 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12957Cells j).1 (repair12957Cells j).2.1
  endpoint_upper := fun j => ((repair12957Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12957Cells j).2.2

theorem repair12958Cells (j : Fin 43) :
    0 ≤ (scalarRow12958.table (sourceIndex j)).upper ∧
    (scalarRow12958.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12958.table (sourceIndex j)).centre) /
      (scalarRow12958.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12958.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12958,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12958,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12958,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12958,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12958,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12958,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12958,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12958,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12958,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12958,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12958,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12958,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12958,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12958,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12958,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12958,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12958,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12958,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12958,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12958,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12958,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12958,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12958,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12958,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12958,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12958,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12958,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12958,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12958,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12958,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12958,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12958,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12958,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12958,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12958,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12958,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12958,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12958,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12958,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12958,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12958,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12958,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12958,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12958,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12958,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12958,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12958,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12958,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12958,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12958,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12958,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12958,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12958,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12958,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12958,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12958,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12958,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12958,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12958,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12958,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12958,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12958,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12958,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12958,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12958,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12958,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12958,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12958,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12958,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12958,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12958,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12958,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12958,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12958,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12958,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12958,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12958,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12958,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12958,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12958,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12958,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12958,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12958,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12958,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12958,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12958,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12958 : FrameRepair 12958 scalarRow12958 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12958Cells j).1 (repair12958Cells j).2.1
  endpoint_upper := fun j => ((repair12958Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12958Cells j).2.2

theorem repair12959Cells (j : Fin 43) :
    0 ≤ (scalarRow12959.table (sourceIndex j)).upper ∧
    (scalarRow12959.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12959.table (sourceIndex j)).centre) /
      (scalarRow12959.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12959.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12959,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12959,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12959,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12959,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12959,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12959,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12959,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12959,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12959,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12959,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12959,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12959,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12959,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12959,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12959,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12959,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12959,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12959,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12959,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12959,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12959,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12959,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12959,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12959,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12959,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12959,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12959,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12959,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12959,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12959,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12959,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12959,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12959,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12959,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12959,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12959,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12959,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12959,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12959,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12959,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12959,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12959,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12959,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12959,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12959,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12959,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12959,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12959,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12959,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12959,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12959,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12959,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12959,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12959,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12959,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12959,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12959,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12959,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12959,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12959,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12959,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12959,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12959,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12959,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12959,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12959,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12959,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12959,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12959,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12959,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12959,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12959,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12959,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12959,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12959,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12959,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12959,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12959,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12959,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12959,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12959,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12959,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12959,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12959,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12959,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12959,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12959 : FrameRepair 12959 scalarRow12959 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12959Cells j).1 (repair12959Cells j).2.1
  endpoint_upper := fun j => ((repair12959Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12959Cells j).2.2

theorem repair12960Cells (j : Fin 43) :
    0 ≤ (scalarRow12960.table (sourceIndex j)).upper ∧
    (scalarRow12960.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12960.table (sourceIndex j)).centre) /
      (scalarRow12960.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12960.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12960,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12960,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12960,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12960,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12960,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12960,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12960,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12960,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12960,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12960,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12960,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12960,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12960,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12960,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12960,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12960,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12960,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12960,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12960,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12960,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12960,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12960,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12960,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12960,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12960,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12960,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12960,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12960,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12960,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12960,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12960,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12960,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12960,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12960,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12960,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12960,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12960,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12960,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12960,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12960,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12960,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12960,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12960,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12960,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12960,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12960,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12960,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12960,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12960,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12960,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12960,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12960,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12960,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12960,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12960,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12960,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12960,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12960,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12960,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12960,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12960,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12960,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12960,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12960,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12960,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12960,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12960,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12960,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12960,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12960,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12960,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12960,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12960,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12960,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12960,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12960,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12960,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12960,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12960,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12960,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12960,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12960,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12960,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12960,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12960,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12960,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12960 : FrameRepair 12960 scalarRow12960 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12960Cells j).1 (repair12960Cells j).2.1
  endpoint_upper := fun j => ((repair12960Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12960Cells j).2.2

theorem repair12961Cells (j : Fin 43) :
    0 ≤ (scalarRow12961.table (sourceIndex j)).upper ∧
    (scalarRow12961.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12961.table (sourceIndex j)).centre) /
      (scalarRow12961.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12961.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12961,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12961,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12961,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12961,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12961,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12961,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12961,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12961,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12961,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12961,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12961,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12961,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12961,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12961,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12961,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12961,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12961,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12961,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12961,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12961,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12961,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12961,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12961,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12961,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12961,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12961,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12961,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12961,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12961,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12961,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12961,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12961,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12961,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12961,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12961,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12961,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12961,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12961,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12961,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12961,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12961,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12961,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12961,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12961,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12961,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12961,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12961,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12961,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12961,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12961,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12961,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12961,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12961,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12961,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12961,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12961,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12961,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12961,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12961,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12961,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12961,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12961,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12961,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12961,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12961,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12961,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12961,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12961,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12961,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12961,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12961,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12961,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12961,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12961,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12961,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12961,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12961,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12961,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12961,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12961,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12961,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12961,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12961,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12961,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12961,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12961,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12961 : FrameRepair 12961 scalarRow12961 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12961Cells j).1 (repair12961Cells j).2.1
  endpoint_upper := fun j => ((repair12961Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12961Cells j).2.2

theorem repair12962Cells (j : Fin 43) :
    0 ≤ (scalarRow12962.table (sourceIndex j)).upper ∧
    (scalarRow12962.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12962.table (sourceIndex j)).centre) /
      (scalarRow12962.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12962.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12962,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12962,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12962,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12962,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12962,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12962,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12962,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12962,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12962,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12962,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12962,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12962,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12962,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12962,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12962,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12962,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12962,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12962,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12962,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12962,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12962,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12962,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12962,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12962,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12962,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12962,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12962,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12962,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12962,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12962,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12962,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12962,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12962,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12962,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12962,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12962,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12962,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12962,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12962,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12962,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12962,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12962,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12962,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12962,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12962,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12962,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12962,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12962,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12962,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12962,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12962,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12962,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12962,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12962,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12962,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12962,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12962,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12962,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12962,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12962,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12962,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12962,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12962,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12962,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12962,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12962,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12962,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12962,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12962,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12962,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12962,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12962,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12962,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12962,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12962,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12962,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12962,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12962,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12962,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12962,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12962,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12962,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12962,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12962,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12962,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12962,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12962 : FrameRepair 12962 scalarRow12962 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12962Cells j).1 (repair12962Cells j).2.1
  endpoint_upper := fun j => ((repair12962Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12962Cells j).2.2

theorem repair12963Cells (j : Fin 43) :
    0 ≤ (scalarRow12963.table (sourceIndex j)).upper ∧
    (scalarRow12963.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12963.table (sourceIndex j)).centre) /
      (scalarRow12963.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12963.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12963,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12963,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12963,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12963,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12963,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12963,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12963,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12963,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12963,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12963,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12963,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12963,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12963,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12963,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12963,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12963,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12963,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12963,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12963,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12963,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12963,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12963,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12963,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12963,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12963,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12963,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12963,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12963,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12963,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12963,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12963,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12963,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12963,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12963,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12963,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12963,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12963,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12963,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12963,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12963,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12963,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12963,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12963,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12963,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12963,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12963,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12963,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12963,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12963,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12963,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12963,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12963,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12963,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12963,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12963,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12963,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12963,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12963,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12963,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12963,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12963,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12963,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12963,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12963,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12963,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12963,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12963,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12963,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12963,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12963,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12963,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12963,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12963,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12963,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12963,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12963,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12963,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12963,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12963,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12963,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12963,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12963,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12963,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12963,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12963,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12963,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12963 : FrameRepair 12963 scalarRow12963 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12963Cells j).1 (repair12963Cells j).2.1
  endpoint_upper := fun j => ((repair12963Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12963Cells j).2.2

theorem repair12964Cells (j : Fin 43) :
    0 ≤ (scalarRow12964.table (sourceIndex j)).upper ∧
    (scalarRow12964.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12964.table (sourceIndex j)).centre) /
      (scalarRow12964.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12964.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12964,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12964,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12964,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12964,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12964,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12964,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12964,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12964,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12964,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12964,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12964,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12964,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12964,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12964,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12964,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12964,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12964,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12964,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12964,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12964,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12964,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12964,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12964,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12964,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12964,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12964,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12964,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12964,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12964,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12964,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12964,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12964,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12964,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12964,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12964,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12964,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12964,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12964,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12964,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12964,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12964,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12964,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12964,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12964,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12964,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12964,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12964,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12964,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12964,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12964,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12964,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12964,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12964,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12964,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12964,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12964,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12964,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12964,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12964,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12964,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12964,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12964,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12964,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12964,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12964,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12964,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12964,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12964,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12964,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12964,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12964,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12964,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12964,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12964,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12964,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12964,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12964,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12964,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12964,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12964,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12964,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12964,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12964,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12964,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12964,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12964,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12964 : FrameRepair 12964 scalarRow12964 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12964Cells j).1 (repair12964Cells j).2.1
  endpoint_upper := fun j => ((repair12964Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12964Cells j).2.2

theorem repair12965Cells (j : Fin 43) :
    0 ≤ (scalarRow12965.table (sourceIndex j)).upper ∧
    (scalarRow12965.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12965.table (sourceIndex j)).centre) /
      (scalarRow12965.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12965.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12965,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12965,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12965,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12965,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12965,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12965,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12965,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12965,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12965,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12965,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12965,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12965,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12965,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12965,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12965,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12965,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12965,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12965,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12965,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12965,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12965,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12965,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12965,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12965,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12965,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12965,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12965,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12965,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12965,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12965,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12965,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12965,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12965,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12965,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12965,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12965,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12965,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12965,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12965,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12965,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12965,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12965,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12965,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12965,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12965,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12965,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12965,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12965,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12965,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12965,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12965,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12965,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12965,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12965,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12965,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12965,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12965,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12965,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12965,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12965,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12965,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12965,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12965,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12965,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12965,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12965,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12965,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12965,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12965,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12965,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12965,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12965,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12965,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12965,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12965,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12965,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12965,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12965,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12965,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12965,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12965,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12965,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12965,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12965,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12965,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12965,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12965 : FrameRepair 12965 scalarRow12965 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12965Cells j).1 (repair12965Cells j).2.1
  endpoint_upper := fun j => ((repair12965Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12965Cells j).2.2

theorem repair12966Cells (j : Fin 43) :
    0 ≤ (scalarRow12966.table (sourceIndex j)).upper ∧
    (scalarRow12966.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12966.table (sourceIndex j)).centre) /
      (scalarRow12966.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12966.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12966,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12966,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12966,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12966,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12966,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12966,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12966,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12966,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12966,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12966,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12966,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12966,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12966,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12966,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12966,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12966,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12966,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12966,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12966,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12966,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12966,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12966,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12966,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12966,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12966,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12966,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12966,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12966,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12966,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12966,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12966,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12966,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12966,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12966,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12966,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12966,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12966,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12966,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12966,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12966,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12966,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12966,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12966,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12966,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12966,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12966,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12966,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12966,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12966,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12966,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12966,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12966,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12966,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12966,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12966,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12966,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12966,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12966,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12966,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12966,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12966,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12966,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12966,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12966,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12966,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12966,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12966,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12966,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12966,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12966,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12966,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12966,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12966,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12966,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12966,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12966,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12966,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12966,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12966,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12966,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12966,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12966,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12966,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12966,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12966,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12966,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12966 : FrameRepair 12966 scalarRow12966 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12966Cells j).1 (repair12966Cells j).2.1
  endpoint_upper := fun j => ((repair12966Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12966Cells j).2.2

theorem repair12967Cells (j : Fin 43) :
    0 ≤ (scalarRow12967.table (sourceIndex j)).upper ∧
    (scalarRow12967.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12967.table (sourceIndex j)).centre) /
      (scalarRow12967.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12967.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12967,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12967,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12967,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12967,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12967,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12967,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12967,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12967,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12967,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12967,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12967,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12967,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12967,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12967,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12967,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12967,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12967,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12967,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12967,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12967,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12967,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12967,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12967,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12967,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12967,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12967,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12967,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12967,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12967,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12967,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12967,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12967,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12967,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12967,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12967,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12967,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12967,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12967,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12967,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12967,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12967,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12967,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12967,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12967,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12967,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12967,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12967,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12967,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12967,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12967,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12967,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12967,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12967,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12967,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12967,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12967,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12967,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12967,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12967,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12967,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12967,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12967,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12967,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12967,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12967,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12967,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12967,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12967,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12967,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12967,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12967,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12967,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12967,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12967,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12967,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12967,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12967,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12967,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12967,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12967,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12967,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12967,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12967,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12967,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12967,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12967,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12967 : FrameRepair 12967 scalarRow12967 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12967Cells j).1 (repair12967Cells j).2.1
  endpoint_upper := fun j => ((repair12967Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12967Cells j).2.2

theorem repair12968Cells (j : Fin 43) :
    0 ≤ (scalarRow12968.table (sourceIndex j)).upper ∧
    (scalarRow12968.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12968.table (sourceIndex j)).centre) /
      (scalarRow12968.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12968.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12968,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12968,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12968,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12968,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12968,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12968,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12968,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12968,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12968,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12968,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12968,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12968,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12968,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12968,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12968,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12968,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12968,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12968,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12968,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12968,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12968,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12968,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12968,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12968,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12968,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12968,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12968,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12968,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12968,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12968,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12968,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12968,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12968,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12968,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12968,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12968,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12968,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12968,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12968,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12968,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12968,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12968,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12968,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12968,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12968,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12968,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12968,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12968,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12968,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12968,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12968,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12968,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12968,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12968,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12968,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12968,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12968,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12968,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12968,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12968,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12968,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12968,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12968,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12968,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12968,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12968,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12968,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12968,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12968,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12968,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12968,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12968,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12968,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12968,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12968,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12968,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12968,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12968,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12968,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12968,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12968,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12968,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12968,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12968,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12968,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12968,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12968 : FrameRepair 12968 scalarRow12968 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12968Cells j).1 (repair12968Cells j).2.1
  endpoint_upper := fun j => ((repair12968Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12968Cells j).2.2

theorem repair12969Cells (j : Fin 43) :
    0 ≤ (scalarRow12969.table (sourceIndex j)).upper ∧
    (scalarRow12969.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12969.table (sourceIndex j)).centre) /
      (scalarRow12969.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12969.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12969,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12969,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12969,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12969,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12969,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12969,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12969,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12969,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12969,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12969,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12969,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12969,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12969,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12969,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12969,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12969,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12969,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12969,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12969,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12969,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12969,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12969,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12969,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12969,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12969,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12969,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12969,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12969,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12969,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12969,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12969,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12969,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12969,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12969,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12969,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12969,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12969,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12969,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12969,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12969,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12969,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12969,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12969,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12969,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12969,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12969,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12969,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12969,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12969,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12969,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12969,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12969,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12969,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12969,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12969,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12969,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12969,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12969,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12969,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12969,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12969,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12969,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12969,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12969,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12969,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12969,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12969,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12969,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12969,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12969,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12969,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12969,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12969,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12969,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12969,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12969,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12969,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12969,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12969,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12969,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12969,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12969,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12969,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12969,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12969,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12969,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12969 : FrameRepair 12969 scalarRow12969 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12969Cells j).1 (repair12969Cells j).2.1
  endpoint_upper := fun j => ((repair12969Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12969Cells j).2.2

theorem repair12970Cells (j : Fin 43) :
    0 ≤ (scalarRow12970.table (sourceIndex j)).upper ∧
    (scalarRow12970.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12970.table (sourceIndex j)).centre) /
      (scalarRow12970.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12970.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12970,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12970,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12970,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12970,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12970,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12970,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12970,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12970,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12970,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12970,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12970,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12970,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12970,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12970,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12970,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12970,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12970,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12970,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12970,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12970,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12970,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12970,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12970,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12970,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12970,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12970,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12970,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12970,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12970,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12970,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12970,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12970,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12970,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12970,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12970,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12970,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12970,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12970,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12970,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12970,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12970,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12970,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12970,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12970,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12970,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12970,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12970,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12970,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12970,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12970,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12970,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12970,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12970,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12970,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12970,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12970,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12970,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12970,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12970,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12970,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12970,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12970,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12970,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12970,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12970,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12970,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12970,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12970,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12970,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12970,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12970,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12970,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12970,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12970,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12970,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12970,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12970,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12970,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12970,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12970,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12970,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12970,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12970,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12970,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12970,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12970,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12970 : FrameRepair 12970 scalarRow12970 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12970Cells j).1 (repair12970Cells j).2.1
  endpoint_upper := fun j => ((repair12970Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12970Cells j).2.2

theorem repair12971Cells (j : Fin 43) :
    0 ≤ (scalarRow12971.table (sourceIndex j)).upper ∧
    (scalarRow12971.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12971.table (sourceIndex j)).centre) /
      (scalarRow12971.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12971.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12971,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12971,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12971,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12971,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12971,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12971,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12971,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12971,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12971,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12971,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12971,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12971,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12971,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12971,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12971,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12971,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12971,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12971,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12971,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12971,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12971,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12971,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12971,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12971,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12971,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12971,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12971,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12971,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12971,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12971,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12971,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12971,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12971,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12971,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12971,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12971,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12971,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12971,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12971,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12971,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12971,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12971,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12971,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12971,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12971,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12971,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12971,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12971,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12971,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12971,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12971,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12971,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12971,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12971,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12971,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12971,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12971,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12971,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12971,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12971,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12971,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12971,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12971,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12971,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12971,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12971,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12971,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12971,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12971,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12971,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12971,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12971,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12971,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12971,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12971,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12971,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12971,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12971,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12971,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12971,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12971,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12971,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12971,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12971,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12971,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12971,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12971 : FrameRepair 12971 scalarRow12971 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12971Cells j).1 (repair12971Cells j).2.1
  endpoint_upper := fun j => ((repair12971Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12971Cells j).2.2

theorem repair12972Cells (j : Fin 43) :
    0 ≤ (scalarRow12972.table (sourceIndex j)).upper ∧
    (scalarRow12972.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12972.table (sourceIndex j)).centre) /
      (scalarRow12972.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12972.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12972,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12972,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12972,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12972,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12972,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12972,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12972,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12972,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12972,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12972,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12972,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12972,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12972,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12972,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12972,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12972,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12972,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12972,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12972,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12972,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12972,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12972,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12972,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12972,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12972,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12972,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12972,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12972,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12972,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12972,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12972,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12972,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12972,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12972,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12972,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12972,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12972,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12972,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12972,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12972,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12972,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12972,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12972,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12972,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12972,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12972,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12972,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12972,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12972,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12972,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12972,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12972,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12972,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12972,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12972,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12972,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12972,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12972,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12972,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12972,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12972,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12972,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12972,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12972,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12972,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12972,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12972,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12972,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12972,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12972,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12972,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12972,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12972,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12972,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12972,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12972,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12972,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12972,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12972,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12972,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12972,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12972,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12972,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12972,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12972,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12972,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12972 : FrameRepair 12972 scalarRow12972 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12972Cells j).1 (repair12972Cells j).2.1
  endpoint_upper := fun j => ((repair12972Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12972Cells j).2.2

theorem repair12973Cells (j : Fin 43) :
    0 ≤ (scalarRow12973.table (sourceIndex j)).upper ∧
    (scalarRow12973.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12973.table (sourceIndex j)).centre) /
      (scalarRow12973.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12973.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12973,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12973,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12973,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12973,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12973,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12973,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12973,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12973,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12973,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12973,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12973,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12973,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12973,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12973,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12973,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12973,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12973,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12973,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12973,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12973,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12973,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12973,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12973,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12973,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12973,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12973,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12973,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12973,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12973,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12973,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12973,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12973,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12973,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12973,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12973,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12973,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12973,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12973,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12973,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12973,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12973,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12973,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12973,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12973,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12973,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12973,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12973,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12973,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12973,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12973,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12973,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12973,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12973,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12973,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12973,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12973,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12973,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12973,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12973,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12973,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12973,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12973,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12973,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12973,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12973,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12973,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12973,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12973,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12973,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12973,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12973,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12973,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12973,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12973,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12973,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12973,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12973,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12973,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12973,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12973,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12973,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12973,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12973,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12973,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12973,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12973,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12973 : FrameRepair 12973 scalarRow12973 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12973Cells j).1 (repair12973Cells j).2.1
  endpoint_upper := fun j => ((repair12973Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12973Cells j).2.2

theorem repair12974Cells (j : Fin 43) :
    0 ≤ (scalarRow12974.table (sourceIndex j)).upper ∧
    (scalarRow12974.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12974.table (sourceIndex j)).centre) /
      (scalarRow12974.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12974.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12974,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12974,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12974,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12974,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12974,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12974,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12974,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12974,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12974,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12974,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12974,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12974,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12974,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12974,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12974,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12974,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12974,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12974,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12974,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12974,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12974,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12974,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12974,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12974,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12974,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12974,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12974,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12974,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12974,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12974,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12974,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12974,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12974,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12974,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12974,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12974,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12974,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12974,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12974,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12974,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12974,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12974,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12974,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12974,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12974,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12974,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12974,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12974,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12974,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12974,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12974,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12974,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12974,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12974,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12974,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12974,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12974,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12974,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12974,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12974,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12974,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12974,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12974,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12974,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12974,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12974,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12974,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12974,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12974,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12974,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12974,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12974,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12974,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12974,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12974,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12974,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12974,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12974,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12974,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12974,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12974,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12974,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12974,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12974,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12974,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12974,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12974 : FrameRepair 12974 scalarRow12974 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12974Cells j).1 (repair12974Cells j).2.1
  endpoint_upper := fun j => ((repair12974Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12974Cells j).2.2

end BstLean.Part269
