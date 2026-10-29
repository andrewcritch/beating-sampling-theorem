import BstLean.Part269Rows3
import BstLean.Part269RepairCommon
namespace BstLean.Part269
open Real Set BstLean.Part255 BstLean.Part263 BstLean.Part264
theorem repair12425Cells (j : Fin 43) :
    0 ≤ (scalarRow12425.table (sourceIndex j)).upper ∧
    (scalarRow12425.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12425.table (sourceIndex j)).centre) /
      (scalarRow12425.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12425.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12425,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12425,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12425,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12425,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12425,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12425,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12425,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12425,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12425,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12425,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12425,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12425,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12425,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12425,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12425,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12425,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12425,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12425,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12425,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12425,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12425,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12425,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12425,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12425,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12425,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12425,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12425,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12425,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12425,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12425,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12425,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12425,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12425,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12425,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12425,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12425,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12425,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12425,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12425,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12425,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12425,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12425,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12425,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12425,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12425,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12425,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12425,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12425,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12425,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12425,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12425,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12425,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12425,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12425,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12425,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12425,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12425,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12425,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12425,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12425,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12425,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12425,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12425,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12425,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12425,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12425,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12425,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12425,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12425,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12425,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12425,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12425,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12425,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12425,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12425,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12425,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12425,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12425,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12425,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12425,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12425,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12425,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12425,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12425,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12425,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12425,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12425 : FrameRepair 12425 scalarRow12425 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12425Cells j).1 (repair12425Cells j).2.1
  endpoint_upper := fun j => ((repair12425Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12425Cells j).2.2

theorem repair12426Cells (j : Fin 43) :
    0 ≤ (scalarRow12426.table (sourceIndex j)).upper ∧
    (scalarRow12426.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12426.table (sourceIndex j)).centre) /
      (scalarRow12426.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12426.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12426,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12426,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12426,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12426,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12426,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12426,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12426,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12426,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12426,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12426,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12426,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12426,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12426,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12426,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12426,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12426,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12426,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12426,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12426,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12426,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12426,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12426,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12426,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12426,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12426,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12426,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12426,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12426,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12426,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12426,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12426,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12426,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12426,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12426,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12426,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12426,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12426,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12426,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12426,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12426,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12426,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12426,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12426,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12426,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12426,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12426,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12426,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12426,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12426,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12426,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12426,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12426,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12426,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12426,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12426,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12426,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12426,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12426,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12426,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12426,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12426,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12426,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12426,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12426,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12426,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12426,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12426,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12426,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12426,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12426,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12426,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12426,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12426,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12426,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12426,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12426,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12426,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12426,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12426,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12426,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12426,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12426,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12426,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12426,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12426,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12426,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12426 : FrameRepair 12426 scalarRow12426 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12426Cells j).1 (repair12426Cells j).2.1
  endpoint_upper := fun j => ((repair12426Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12426Cells j).2.2

theorem repair12427Cells (j : Fin 43) :
    0 ≤ (scalarRow12427.table (sourceIndex j)).upper ∧
    (scalarRow12427.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12427.table (sourceIndex j)).centre) /
      (scalarRow12427.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12427.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12427,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12427,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12427,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12427,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12427,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12427,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12427,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12427,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12427,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12427,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12427,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12427,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12427,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12427,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12427,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12427,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12427,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12427,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12427,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12427,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12427,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12427,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12427,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12427,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12427,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12427,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12427,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12427,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12427,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12427,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12427,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12427,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12427,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12427,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12427,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12427,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12427,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12427,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12427,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12427,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12427,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12427,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12427,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12427,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12427,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12427,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12427,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12427,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12427,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12427,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12427,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12427,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12427,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12427,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12427,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12427,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12427,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12427,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12427,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12427,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12427,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12427,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12427,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12427,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12427,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12427,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12427,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12427,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12427,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12427,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12427,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12427,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12427,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12427,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12427,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12427,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12427,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12427,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12427,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12427,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12427,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12427,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12427,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12427,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12427,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12427,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12427 : FrameRepair 12427 scalarRow12427 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12427Cells j).1 (repair12427Cells j).2.1
  endpoint_upper := fun j => ((repair12427Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12427Cells j).2.2

theorem repair12428Cells (j : Fin 43) :
    0 ≤ (scalarRow12428.table (sourceIndex j)).upper ∧
    (scalarRow12428.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12428.table (sourceIndex j)).centre) /
      (scalarRow12428.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12428.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12428,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12428,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12428,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12428,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12428,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12428,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12428,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12428,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12428,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12428,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12428,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12428,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12428,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12428,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12428,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12428,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12428,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12428,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12428,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12428,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12428,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12428,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12428,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12428,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12428,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12428,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12428,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12428,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12428,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12428,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12428,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12428,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12428,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12428,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12428,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12428,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12428,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12428,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12428,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12428,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12428,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12428,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12428,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12428,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12428,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12428,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12428,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12428,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12428,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12428,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12428,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12428,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12428,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12428,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12428,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12428,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12428,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12428,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12428,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12428,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12428,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12428,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12428,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12428,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12428,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12428,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12428,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12428,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12428,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12428,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12428,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12428,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12428,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12428,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12428,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12428,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12428,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12428,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12428,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12428,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12428,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12428,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12428,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12428,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12428,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12428,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12428 : FrameRepair 12428 scalarRow12428 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12428Cells j).1 (repair12428Cells j).2.1
  endpoint_upper := fun j => ((repair12428Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12428Cells j).2.2

theorem repair12429Cells (j : Fin 43) :
    0 ≤ (scalarRow12429.table (sourceIndex j)).upper ∧
    (scalarRow12429.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12429.table (sourceIndex j)).centre) /
      (scalarRow12429.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12429.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12429,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12429,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12429,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12429,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12429,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12429,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12429,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12429,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12429,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12429,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12429,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12429,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12429,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12429,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12429,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12429,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12429,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12429,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12429,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12429,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12429,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12429,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12429,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12429,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12429,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12429,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12429,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12429,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12429,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12429,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12429,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12429,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12429,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12429,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12429,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12429,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12429,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12429,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12429,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12429,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12429,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12429,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12429,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12429,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12429,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12429,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12429,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12429,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12429,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12429,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12429,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12429,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12429,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12429,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12429,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12429,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12429,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12429,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12429,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12429,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12429,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12429,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12429,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12429,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12429,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12429,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12429,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12429,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12429,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12429,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12429,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12429,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12429,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12429,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12429,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12429,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12429,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12429,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12429,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12429,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12429,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12429,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12429,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12429,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12429,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12429,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12429 : FrameRepair 12429 scalarRow12429 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12429Cells j).1 (repair12429Cells j).2.1
  endpoint_upper := fun j => ((repair12429Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12429Cells j).2.2

theorem repair12430Cells (j : Fin 43) :
    0 ≤ (scalarRow12430.table (sourceIndex j)).upper ∧
    (scalarRow12430.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12430.table (sourceIndex j)).centre) /
      (scalarRow12430.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12430.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12430,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12430,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12430,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12430,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12430,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12430,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12430,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12430,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12430,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12430,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12430,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12430,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12430,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12430,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12430,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12430,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12430,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12430,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12430,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12430,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12430,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12430,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12430,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12430,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12430,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12430,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12430,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12430,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12430,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12430,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12430,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12430,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12430,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12430,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12430,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12430,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12430,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12430,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12430,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12430,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12430,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12430,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12430,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12430,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12430,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12430,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12430,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12430,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12430,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12430,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12430,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12430,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12430,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12430,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12430,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12430,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12430,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12430,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12430,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12430,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12430,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12430,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12430,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12430,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12430,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12430,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12430,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12430,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12430,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12430,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12430,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12430,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12430,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12430,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12430,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12430,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12430,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12430,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12430,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12430,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12430,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12430,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12430,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12430,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12430,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12430,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12430 : FrameRepair 12430 scalarRow12430 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12430Cells j).1 (repair12430Cells j).2.1
  endpoint_upper := fun j => ((repair12430Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12430Cells j).2.2

theorem repair12431Cells (j : Fin 43) :
    0 ≤ (scalarRow12431.table (sourceIndex j)).upper ∧
    (scalarRow12431.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12431.table (sourceIndex j)).centre) /
      (scalarRow12431.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12431.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12431,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12431,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12431,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12431,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12431,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12431,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12431,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12431,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12431,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12431,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12431,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12431,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12431,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12431,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12431,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12431,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12431,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12431,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12431,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12431,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12431,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12431,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12431,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12431,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12431,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12431,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12431,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12431,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12431,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12431,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12431,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12431,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12431,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12431,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12431,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12431,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12431,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12431,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12431,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12431,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12431,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12431,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12431,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12431,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12431,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12431,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12431,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12431,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12431,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12431,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12431,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12431,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12431,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12431,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12431,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12431,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12431,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12431,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12431,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12431,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12431,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12431,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12431,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12431,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12431,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12431,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12431,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12431,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12431,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12431,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12431,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12431,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12431,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12431,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12431,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12431,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12431,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12431,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12431,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12431,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12431,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12431,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12431,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12431,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12431,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12431,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12431 : FrameRepair 12431 scalarRow12431 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12431Cells j).1 (repair12431Cells j).2.1
  endpoint_upper := fun j => ((repair12431Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12431Cells j).2.2

theorem repair12432Cells (j : Fin 43) :
    0 ≤ (scalarRow12432.table (sourceIndex j)).upper ∧
    (scalarRow12432.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12432.table (sourceIndex j)).centre) /
      (scalarRow12432.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12432.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12432,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12432,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12432,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12432,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12432,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12432,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12432,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12432,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12432,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12432,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12432,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12432,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12432,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12432,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12432,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12432,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12432,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12432,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12432,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12432,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12432,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12432,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12432,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12432,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12432,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12432,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12432,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12432,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12432,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12432,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12432,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12432,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12432,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12432,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12432,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12432,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12432,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12432,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12432,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12432,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12432,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12432,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12432,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12432,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12432,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12432,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12432,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12432,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12432,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12432,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12432,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12432,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12432,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12432,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12432,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12432,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12432,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12432,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12432,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12432,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12432,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12432,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12432,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12432,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12432,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12432,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12432,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12432,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12432,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12432,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12432,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12432,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12432,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12432,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12432,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12432,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12432,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12432,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12432,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12432,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12432,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12432,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12432,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12432,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12432,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12432,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12432 : FrameRepair 12432 scalarRow12432 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12432Cells j).1 (repair12432Cells j).2.1
  endpoint_upper := fun j => ((repair12432Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12432Cells j).2.2

theorem repair12433Cells (j : Fin 43) :
    0 ≤ (scalarRow12433.table (sourceIndex j)).upper ∧
    (scalarRow12433.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12433.table (sourceIndex j)).centre) /
      (scalarRow12433.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12433.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12433,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12433,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12433,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12433,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12433,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12433,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12433,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12433,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12433,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12433,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12433,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12433,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12433,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12433,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12433,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12433,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12433,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12433,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12433,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12433,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12433,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12433,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12433,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12433,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12433,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12433,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12433,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12433,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12433,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12433,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12433,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12433,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12433,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12433,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12433,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12433,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12433,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12433,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12433,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12433,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12433,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12433,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12433,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12433,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12433,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12433,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12433,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12433,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12433,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12433,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12433,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12433,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12433,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12433,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12433,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12433,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12433,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12433,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12433,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12433,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12433,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12433,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12433,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12433,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12433,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12433,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12433,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12433,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12433,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12433,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12433,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12433,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12433,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12433,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12433,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12433,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12433,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12433,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12433,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12433,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12433,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12433,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12433,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12433,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12433,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12433,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12433 : FrameRepair 12433 scalarRow12433 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12433Cells j).1 (repair12433Cells j).2.1
  endpoint_upper := fun j => ((repair12433Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12433Cells j).2.2

theorem repair12434Cells (j : Fin 43) :
    0 ≤ (scalarRow12434.table (sourceIndex j)).upper ∧
    (scalarRow12434.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12434.table (sourceIndex j)).centre) /
      (scalarRow12434.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12434.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12434,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12434,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12434,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12434,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12434,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12434,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12434,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12434,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12434,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12434,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12434,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12434,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12434,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12434,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12434,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12434,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12434,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12434,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12434,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12434,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12434,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12434,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12434,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12434,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12434,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12434,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12434,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12434,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12434,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12434,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12434,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12434,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12434,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12434,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12434,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12434,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12434,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12434,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12434,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12434,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12434,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12434,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12434,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12434,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12434,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12434,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12434,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12434,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12434,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12434,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12434,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12434,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12434,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12434,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12434,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12434,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12434,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12434,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12434,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12434,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12434,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12434,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12434,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12434,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12434,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12434,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12434,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12434,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12434,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12434,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12434,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12434,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12434,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12434,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12434,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12434,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12434,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12434,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12434,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12434,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12434,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12434,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12434,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12434,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12434,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12434,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12434 : FrameRepair 12434 scalarRow12434 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12434Cells j).1 (repair12434Cells j).2.1
  endpoint_upper := fun j => ((repair12434Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12434Cells j).2.2

theorem repair12435Cells (j : Fin 43) :
    0 ≤ (scalarRow12435.table (sourceIndex j)).upper ∧
    (scalarRow12435.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12435.table (sourceIndex j)).centre) /
      (scalarRow12435.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12435.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12435,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12435,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12435,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12435,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12435,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12435,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12435,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12435,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12435,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12435,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12435,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12435,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12435,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12435,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12435,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12435,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12435,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12435,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12435,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12435,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12435,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12435,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12435,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12435,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12435,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12435,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12435,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12435,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12435,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12435,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12435,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12435,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12435,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12435,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12435,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12435,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12435,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12435,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12435,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12435,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12435,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12435,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12435,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12435,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12435,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12435,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12435,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12435,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12435,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12435,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12435,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12435,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12435,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12435,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12435,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12435,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12435,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12435,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12435,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12435,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12435,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12435,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12435,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12435,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12435,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12435,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12435,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12435,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12435,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12435,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12435,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12435,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12435,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12435,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12435,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12435,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12435,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12435,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12435,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12435,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12435,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12435,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12435,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12435,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12435,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12435,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12435 : FrameRepair 12435 scalarRow12435 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12435Cells j).1 (repair12435Cells j).2.1
  endpoint_upper := fun j => ((repair12435Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12435Cells j).2.2

theorem repair12436Cells (j : Fin 43) :
    0 ≤ (scalarRow12436.table (sourceIndex j)).upper ∧
    (scalarRow12436.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12436.table (sourceIndex j)).centre) /
      (scalarRow12436.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12436.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12436,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12436,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12436,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12436,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12436,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12436,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12436,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12436,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12436,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12436,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12436,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12436,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12436,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12436,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12436,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12436,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12436,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12436,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12436,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12436,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12436,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12436,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12436,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12436,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12436,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12436,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12436,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12436,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12436,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12436,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12436,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12436,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12436,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12436,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12436,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12436,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12436,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12436,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12436,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12436,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12436,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12436,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12436,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12436,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12436,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12436,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12436,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12436,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12436,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12436,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12436,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12436,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12436,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12436,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12436,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12436,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12436,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12436,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12436,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12436,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12436,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12436,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12436,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12436,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12436,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12436,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12436,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12436,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12436,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12436,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12436,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12436,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12436,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12436,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12436,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12436,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12436,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12436,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12436,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12436,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12436,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12436,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12436,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12436,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12436,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12436,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12436 : FrameRepair 12436 scalarRow12436 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12436Cells j).1 (repair12436Cells j).2.1
  endpoint_upper := fun j => ((repair12436Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12436Cells j).2.2

theorem repair12437Cells (j : Fin 43) :
    0 ≤ (scalarRow12437.table (sourceIndex j)).upper ∧
    (scalarRow12437.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12437.table (sourceIndex j)).centre) /
      (scalarRow12437.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12437.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12437,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12437,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12437,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12437,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12437,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12437,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12437,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12437,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12437,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12437,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12437,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12437,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12437,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12437,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12437,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12437,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12437,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12437,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12437,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12437,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12437,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12437,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12437,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12437,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12437,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12437,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12437,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12437,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12437,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12437,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12437,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12437,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12437,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12437,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12437,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12437,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12437,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12437,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12437,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12437,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12437,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12437,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12437,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12437,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12437,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12437,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12437,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12437,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12437,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12437,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12437,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12437,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12437,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12437,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12437,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12437,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12437,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12437,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12437,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12437,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12437,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12437,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12437,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12437,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12437,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12437,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12437,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12437,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12437,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12437,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12437,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12437,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12437,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12437,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12437,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12437,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12437,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12437,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12437,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12437,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12437,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12437,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12437,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12437,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12437,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12437,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12437 : FrameRepair 12437 scalarRow12437 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12437Cells j).1 (repair12437Cells j).2.1
  endpoint_upper := fun j => ((repair12437Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12437Cells j).2.2

theorem repair12438Cells (j : Fin 43) :
    0 ≤ (scalarRow12438.table (sourceIndex j)).upper ∧
    (scalarRow12438.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12438.table (sourceIndex j)).centre) /
      (scalarRow12438.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12438.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12438,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12438,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12438,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12438,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12438,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12438,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12438,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12438,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12438,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12438,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12438,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12438,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12438,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12438,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12438,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12438,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12438,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12438,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12438,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12438,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12438,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12438,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12438,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12438,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12438,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12438,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12438,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12438,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12438,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12438,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12438,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12438,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12438,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12438,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12438,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12438,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12438,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12438,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12438,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12438,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12438,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12438,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12438,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12438,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12438,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12438,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12438,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12438,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12438,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12438,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12438,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12438,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12438,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12438,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12438,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12438,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12438,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12438,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12438,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12438,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12438,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12438,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12438,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12438,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12438,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12438,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12438,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12438,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12438,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12438,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12438,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12438,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12438,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12438,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12438,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12438,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12438,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12438,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12438,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12438,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12438,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12438,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12438,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12438,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12438,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12438,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12438 : FrameRepair 12438 scalarRow12438 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12438Cells j).1 (repair12438Cells j).2.1
  endpoint_upper := fun j => ((repair12438Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12438Cells j).2.2

theorem repair12439Cells (j : Fin 43) :
    0 ≤ (scalarRow12439.table (sourceIndex j)).upper ∧
    (scalarRow12439.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12439.table (sourceIndex j)).centre) /
      (scalarRow12439.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12439.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12439,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12439,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12439,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12439,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12439,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12439,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12439,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12439,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12439,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12439,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12439,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12439,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12439,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12439,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12439,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12439,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12439,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12439,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12439,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12439,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12439,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12439,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12439,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12439,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12439,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12439,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12439,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12439,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12439,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12439,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12439,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12439,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12439,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12439,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12439,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12439,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12439,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12439,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12439,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12439,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12439,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12439,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12439,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12439,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12439,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12439,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12439,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12439,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12439,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12439,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12439,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12439,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12439,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12439,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12439,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12439,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12439,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12439,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12439,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12439,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12439,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12439,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12439,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12439,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12439,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12439,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12439,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12439,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12439,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12439,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12439,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12439,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12439,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12439,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12439,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12439,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12439,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12439,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12439,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12439,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12439,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12439,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12439,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12439,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12439,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12439,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12439 : FrameRepair 12439 scalarRow12439 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12439Cells j).1 (repair12439Cells j).2.1
  endpoint_upper := fun j => ((repair12439Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12439Cells j).2.2

theorem repair12440Cells (j : Fin 43) :
    0 ≤ (scalarRow12440.table (sourceIndex j)).upper ∧
    (scalarRow12440.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12440.table (sourceIndex j)).centre) /
      (scalarRow12440.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12440.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12440,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12440,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12440,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12440,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12440,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12440,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12440,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12440,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12440,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12440,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12440,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12440,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12440,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12440,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12440,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12440,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12440,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12440,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12440,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12440,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12440,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12440,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12440,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12440,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12440,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12440,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12440,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12440,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12440,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12440,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12440,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12440,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12440,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12440,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12440,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12440,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12440,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12440,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12440,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12440,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12440,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12440,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12440,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12440,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12440,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12440,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12440,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12440,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12440,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12440,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12440,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12440,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12440,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12440,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12440,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12440,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12440,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12440,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12440,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12440,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12440,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12440,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12440,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12440,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12440,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12440,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12440,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12440,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12440,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12440,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12440,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12440,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12440,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12440,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12440,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12440,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12440,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12440,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12440,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12440,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12440,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12440,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12440,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12440,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12440,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12440,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12440 : FrameRepair 12440 scalarRow12440 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12440Cells j).1 (repair12440Cells j).2.1
  endpoint_upper := fun j => ((repair12440Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12440Cells j).2.2

theorem repair12441Cells (j : Fin 43) :
    0 ≤ (scalarRow12441.table (sourceIndex j)).upper ∧
    (scalarRow12441.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12441.table (sourceIndex j)).centre) /
      (scalarRow12441.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12441.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12441,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12441,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12441,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12441,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12441,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12441,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12441,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12441,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12441,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12441,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12441,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12441,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12441,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12441,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12441,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12441,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12441,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12441,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12441,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12441,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12441,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12441,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12441,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12441,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12441,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12441,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12441,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12441,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12441,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12441,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12441,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12441,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12441,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12441,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12441,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12441,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12441,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12441,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12441,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12441,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12441,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12441,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12441,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12441,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12441,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12441,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12441,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12441,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12441,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12441,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12441,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12441,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12441,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12441,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12441,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12441,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12441,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12441,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12441,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12441,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12441,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12441,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12441,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12441,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12441,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12441,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12441,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12441,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12441,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12441,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12441,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12441,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12441,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12441,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12441,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12441,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12441,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12441,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12441,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12441,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12441,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12441,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12441,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12441,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12441,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12441,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12441 : FrameRepair 12441 scalarRow12441 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12441Cells j).1 (repair12441Cells j).2.1
  endpoint_upper := fun j => ((repair12441Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12441Cells j).2.2

theorem repair12442Cells (j : Fin 43) :
    0 ≤ (scalarRow12442.table (sourceIndex j)).upper ∧
    (scalarRow12442.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12442.table (sourceIndex j)).centre) /
      (scalarRow12442.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12442.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12442,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12442,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12442,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12442,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12442,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12442,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12442,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12442,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12442,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12442,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12442,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12442,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12442,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12442,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12442,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12442,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12442,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12442,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12442,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12442,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12442,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12442,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12442,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12442,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12442,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12442,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12442,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12442,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12442,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12442,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12442,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12442,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12442,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12442,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12442,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12442,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12442,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12442,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12442,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12442,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12442,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12442,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12442,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12442,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12442,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12442,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12442,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12442,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12442,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12442,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12442,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12442,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12442,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12442,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12442,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12442,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12442,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12442,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12442,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12442,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12442,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12442,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12442,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12442,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12442,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12442,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12442,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12442,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12442,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12442,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12442,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12442,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12442,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12442,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12442,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12442,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12442,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12442,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12442,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12442,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12442,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12442,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12442,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12442,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12442,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12442,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12442 : FrameRepair 12442 scalarRow12442 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12442Cells j).1 (repair12442Cells j).2.1
  endpoint_upper := fun j => ((repair12442Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12442Cells j).2.2

theorem repair12443Cells (j : Fin 43) :
    0 ≤ (scalarRow12443.table (sourceIndex j)).upper ∧
    (scalarRow12443.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12443.table (sourceIndex j)).centre) /
      (scalarRow12443.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12443.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12443,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12443,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12443,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12443,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12443,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12443,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12443,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12443,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12443,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12443,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12443,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12443,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12443,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12443,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12443,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12443,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12443,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12443,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12443,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12443,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12443,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12443,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12443,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12443,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12443,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12443,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12443,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12443,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12443,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12443,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12443,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12443,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12443,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12443,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12443,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12443,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12443,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12443,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12443,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12443,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12443,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12443,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12443,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12443,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12443,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12443,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12443,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12443,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12443,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12443,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12443,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12443,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12443,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12443,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12443,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12443,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12443,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12443,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12443,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12443,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12443,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12443,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12443,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12443,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12443,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12443,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12443,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12443,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12443,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12443,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12443,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12443,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12443,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12443,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12443,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12443,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12443,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12443,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12443,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12443,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12443,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12443,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12443,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12443,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12443,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12443,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12443 : FrameRepair 12443 scalarRow12443 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12443Cells j).1 (repair12443Cells j).2.1
  endpoint_upper := fun j => ((repair12443Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12443Cells j).2.2

theorem repair12444Cells (j : Fin 43) :
    0 ≤ (scalarRow12444.table (sourceIndex j)).upper ∧
    (scalarRow12444.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12444.table (sourceIndex j)).centre) /
      (scalarRow12444.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12444.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12444,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12444,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12444,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12444,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12444,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12444,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12444,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12444,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12444,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12444,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12444,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12444,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12444,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12444,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12444,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12444,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12444,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12444,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12444,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12444,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12444,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12444,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12444,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12444,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12444,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12444,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12444,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12444,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12444,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12444,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12444,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12444,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12444,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12444,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12444,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12444,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12444,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12444,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12444,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12444,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12444,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12444,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12444,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12444,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12444,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12444,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12444,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12444,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12444,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12444,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12444,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12444,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12444,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12444,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12444,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12444,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12444,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12444,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12444,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12444,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12444,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12444,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12444,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12444,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12444,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12444,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12444,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12444,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12444,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12444,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12444,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12444,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12444,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12444,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12444,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12444,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12444,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12444,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12444,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12444,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12444,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12444,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12444,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12444,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12444,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12444,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12444 : FrameRepair 12444 scalarRow12444 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12444Cells j).1 (repair12444Cells j).2.1
  endpoint_upper := fun j => ((repair12444Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12444Cells j).2.2

theorem repair12445Cells (j : Fin 43) :
    0 ≤ (scalarRow12445.table (sourceIndex j)).upper ∧
    (scalarRow12445.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12445.table (sourceIndex j)).centre) /
      (scalarRow12445.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12445.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12445,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12445,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12445,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12445,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12445,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12445,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12445,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12445,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12445,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12445,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12445,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12445,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12445,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12445,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12445,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12445,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12445,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12445,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12445,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12445,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12445,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12445,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12445,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12445,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12445,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12445,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12445,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12445,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12445,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12445,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12445,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12445,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12445,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12445,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12445,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12445,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12445,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12445,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12445,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12445,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12445,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12445,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12445,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12445,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12445,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12445,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12445,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12445,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12445,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12445,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12445,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12445,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12445,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12445,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12445,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12445,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12445,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12445,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12445,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12445,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12445,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12445,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12445,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12445,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12445,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12445,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12445,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12445,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12445,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12445,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12445,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12445,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12445,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12445,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12445,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12445,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12445,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12445,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12445,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12445,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12445,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12445,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12445,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12445,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12445,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12445,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12445 : FrameRepair 12445 scalarRow12445 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12445Cells j).1 (repair12445Cells j).2.1
  endpoint_upper := fun j => ((repair12445Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12445Cells j).2.2

theorem repair12446Cells (j : Fin 43) :
    0 ≤ (scalarRow12446.table (sourceIndex j)).upper ∧
    (scalarRow12446.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12446.table (sourceIndex j)).centre) /
      (scalarRow12446.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12446.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12446,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12446,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12446,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12446,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12446,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12446,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12446,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12446,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12446,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12446,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12446,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12446,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12446,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12446,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12446,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12446,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12446,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12446,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12446,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12446,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12446,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12446,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12446,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12446,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12446,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12446,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12446,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12446,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12446,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12446,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12446,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12446,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12446,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12446,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12446,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12446,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12446,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12446,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12446,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12446,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12446,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12446,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12446,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12446,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12446,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12446,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12446,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12446,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12446,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12446,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12446,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12446,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12446,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12446,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12446,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12446,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12446,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12446,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12446,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12446,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12446,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12446,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12446,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12446,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12446,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12446,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12446,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12446,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12446,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12446,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12446,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12446,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12446,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12446,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12446,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12446,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12446,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12446,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12446,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12446,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12446,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12446,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12446,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12446,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12446,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12446,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12446 : FrameRepair 12446 scalarRow12446 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12446Cells j).1 (repair12446Cells j).2.1
  endpoint_upper := fun j => ((repair12446Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12446Cells j).2.2

theorem repair12447Cells (j : Fin 43) :
    0 ≤ (scalarRow12447.table (sourceIndex j)).upper ∧
    (scalarRow12447.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12447.table (sourceIndex j)).centre) /
      (scalarRow12447.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12447.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12447,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12447,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12447,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12447,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12447,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12447,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12447,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12447,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12447,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12447,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12447,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12447,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12447,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12447,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12447,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12447,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12447,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12447,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12447,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12447,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12447,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12447,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12447,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12447,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12447,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12447,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12447,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12447,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12447,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12447,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12447,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12447,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12447,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12447,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12447,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12447,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12447,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12447,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12447,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12447,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12447,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12447,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12447,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12447,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12447,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12447,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12447,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12447,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12447,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12447,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12447,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12447,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12447,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12447,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12447,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12447,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12447,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12447,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12447,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12447,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12447,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12447,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12447,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12447,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12447,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12447,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12447,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12447,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12447,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12447,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12447,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12447,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12447,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12447,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12447,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12447,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12447,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12447,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12447,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12447,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12447,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12447,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12447,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12447,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12447,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12447,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12447 : FrameRepair 12447 scalarRow12447 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12447Cells j).1 (repair12447Cells j).2.1
  endpoint_upper := fun j => ((repair12447Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12447Cells j).2.2

theorem repair12448Cells (j : Fin 43) :
    0 ≤ (scalarRow12448.table (sourceIndex j)).upper ∧
    (scalarRow12448.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12448.table (sourceIndex j)).centre) /
      (scalarRow12448.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12448.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12448,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12448,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12448,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12448,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12448,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12448,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12448,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12448,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12448,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12448,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12448,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12448,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12448,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12448,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12448,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12448,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12448,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12448,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12448,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12448,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12448,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12448,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12448,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12448,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12448,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12448,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12448,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12448,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12448,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12448,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12448,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12448,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12448,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12448,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12448,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12448,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12448,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12448,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12448,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12448,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12448,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12448,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12448,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12448,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12448,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12448,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12448,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12448,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12448,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12448,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12448,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12448,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12448,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12448,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12448,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12448,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12448,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12448,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12448,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12448,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12448,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12448,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12448,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12448,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12448,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12448,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12448,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12448,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12448,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12448,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12448,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12448,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12448,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12448,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12448,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12448,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12448,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12448,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12448,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12448,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12448,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12448,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12448,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12448,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12448,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12448,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12448 : FrameRepair 12448 scalarRow12448 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12448Cells j).1 (repair12448Cells j).2.1
  endpoint_upper := fun j => ((repair12448Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12448Cells j).2.2

theorem repair12449Cells (j : Fin 43) :
    0 ≤ (scalarRow12449.table (sourceIndex j)).upper ∧
    (scalarRow12449.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12449.table (sourceIndex j)).centre) /
      (scalarRow12449.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12449.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12449,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12449,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12449,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12449,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12449,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12449,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12449,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12449,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12449,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12449,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12449,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12449,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12449,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12449,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12449,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12449,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12449,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12449,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12449,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12449,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12449,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12449,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12449,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12449,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12449,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12449,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12449,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12449,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12449,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12449,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12449,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12449,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12449,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12449,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12449,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12449,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12449,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12449,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12449,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12449,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12449,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12449,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12449,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12449,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12449,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12449,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12449,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12449,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12449,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12449,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12449,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12449,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12449,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12449,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12449,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12449,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12449,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12449,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12449,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12449,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12449,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12449,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12449,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12449,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12449,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12449,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12449,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12449,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12449,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12449,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12449,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12449,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12449,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12449,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12449,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12449,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12449,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12449,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12449,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12449,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12449,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12449,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12449,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12449,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12449,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12449,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12449 : FrameRepair 12449 scalarRow12449 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12449Cells j).1 (repair12449Cells j).2.1
  endpoint_upper := fun j => ((repair12449Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12449Cells j).2.2

end BstLean.Part269
