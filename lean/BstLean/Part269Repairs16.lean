import BstLean.Part269Rows16
import BstLean.Part269RepairCommon
namespace BstLean.Part269
open Real Set BstLean.Part255 BstLean.Part263 BstLean.Part264
theorem repair12750Cells (j : Fin 43) :
    0 ≤ (scalarRow12750.table (sourceIndex j)).upper ∧
    (scalarRow12750.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12750.table (sourceIndex j)).centre) /
      (scalarRow12750.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12750.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12750,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12750,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12750,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12750,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12750,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12750,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12750,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12750,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12750,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12750,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12750,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12750,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12750,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12750,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12750,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12750,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12750,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12750,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12750,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12750,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12750,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12750,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12750,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12750,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12750,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12750,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12750,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12750,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12750,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12750,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12750,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12750,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12750,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12750,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12750,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12750,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12750,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12750,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12750,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12750,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12750,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12750,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12750,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12750,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12750,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12750,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12750,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12750,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12750,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12750,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12750,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12750,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12750,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12750,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12750,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12750,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12750,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12750,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12750,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12750,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12750,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12750,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12750,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12750,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12750,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12750,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12750,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12750,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12750,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12750,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12750,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12750,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12750,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12750,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12750,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12750,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12750,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12750,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12750,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12750,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12750,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12750,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12750,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12750,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12750,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12750,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12750 : FrameRepair 12750 scalarRow12750 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12750Cells j).1 (repair12750Cells j).2.1
  endpoint_upper := fun j => ((repair12750Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12750Cells j).2.2

theorem repair12751Cells (j : Fin 43) :
    0 ≤ (scalarRow12751.table (sourceIndex j)).upper ∧
    (scalarRow12751.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12751.table (sourceIndex j)).centre) /
      (scalarRow12751.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12751.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12751,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12751,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12751,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12751,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12751,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12751,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12751,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12751,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12751,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12751,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12751,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12751,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12751,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12751,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12751,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12751,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12751,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12751,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12751,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12751,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12751,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12751,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12751,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12751,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12751,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12751,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12751,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12751,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12751,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12751,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12751,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12751,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12751,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12751,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12751,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12751,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12751,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12751,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12751,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12751,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12751,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12751,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12751,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12751,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12751,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12751,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12751,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12751,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12751,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12751,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12751,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12751,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12751,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12751,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12751,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12751,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12751,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12751,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12751,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12751,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12751,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12751,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12751,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12751,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12751,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12751,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12751,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12751,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12751,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12751,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12751,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12751,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12751,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12751,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12751,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12751,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12751,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12751,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12751,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12751,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12751,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12751,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12751,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12751,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12751,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12751,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12751 : FrameRepair 12751 scalarRow12751 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12751Cells j).1 (repair12751Cells j).2.1
  endpoint_upper := fun j => ((repair12751Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12751Cells j).2.2

theorem repair12752Cells (j : Fin 43) :
    0 ≤ (scalarRow12752.table (sourceIndex j)).upper ∧
    (scalarRow12752.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12752.table (sourceIndex j)).centre) /
      (scalarRow12752.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12752.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12752,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12752,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12752,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12752,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12752,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12752,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12752,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12752,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12752,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12752,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12752,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12752,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12752,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12752,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12752,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12752,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12752,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12752,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12752,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12752,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12752,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12752,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12752,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12752,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12752,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12752,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12752,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12752,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12752,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12752,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12752,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12752,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12752,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12752,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12752,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12752,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12752,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12752,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12752,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12752,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12752,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12752,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12752,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12752,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12752,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12752,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12752,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12752,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12752,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12752,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12752,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12752,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12752,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12752,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12752,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12752,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12752,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12752,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12752,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12752,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12752,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12752,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12752,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12752,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12752,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12752,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12752,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12752,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12752,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12752,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12752,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12752,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12752,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12752,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12752,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12752,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12752,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12752,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12752,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12752,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12752,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12752,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12752,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12752,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12752,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12752,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12752 : FrameRepair 12752 scalarRow12752 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12752Cells j).1 (repair12752Cells j).2.1
  endpoint_upper := fun j => ((repair12752Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12752Cells j).2.2

theorem repair12753Cells (j : Fin 43) :
    0 ≤ (scalarRow12753.table (sourceIndex j)).upper ∧
    (scalarRow12753.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12753.table (sourceIndex j)).centre) /
      (scalarRow12753.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12753.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12753,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12753,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12753,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12753,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12753,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12753,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12753,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12753,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12753,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12753,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12753,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12753,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12753,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12753,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12753,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12753,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12753,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12753,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12753,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12753,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12753,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12753,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12753,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12753,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12753,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12753,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12753,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12753,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12753,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12753,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12753,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12753,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12753,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12753,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12753,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12753,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12753,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12753,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12753,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12753,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12753,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12753,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12753,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12753,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12753,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12753,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12753,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12753,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12753,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12753,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12753,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12753,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12753,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12753,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12753,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12753,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12753,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12753,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12753,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12753,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12753,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12753,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12753,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12753,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12753,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12753,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12753,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12753,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12753,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12753,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12753,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12753,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12753,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12753,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12753,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12753,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12753,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12753,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12753,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12753,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12753,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12753,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12753,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12753,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12753,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12753,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12753 : FrameRepair 12753 scalarRow12753 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12753Cells j).1 (repair12753Cells j).2.1
  endpoint_upper := fun j => ((repair12753Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12753Cells j).2.2

theorem repair12754Cells (j : Fin 43) :
    0 ≤ (scalarRow12754.table (sourceIndex j)).upper ∧
    (scalarRow12754.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12754.table (sourceIndex j)).centre) /
      (scalarRow12754.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12754.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12754,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12754,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12754,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12754,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12754,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12754,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12754,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12754,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12754,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12754,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12754,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12754,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12754,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12754,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12754,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12754,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12754,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12754,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12754,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12754,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12754,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12754,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12754,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12754,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12754,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12754,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12754,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12754,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12754,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12754,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12754,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12754,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12754,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12754,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12754,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12754,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12754,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12754,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12754,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12754,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12754,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12754,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12754,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12754,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12754,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12754,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12754,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12754,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12754,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12754,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12754,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12754,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12754,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12754,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12754,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12754,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12754,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12754,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12754,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12754,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12754,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12754,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12754,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12754,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12754,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12754,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12754,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12754,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12754,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12754,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12754,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12754,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12754,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12754,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12754,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12754,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12754,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12754,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12754,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12754,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12754,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12754,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12754,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12754,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12754,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12754,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12754 : FrameRepair 12754 scalarRow12754 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12754Cells j).1 (repair12754Cells j).2.1
  endpoint_upper := fun j => ((repair12754Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12754Cells j).2.2

theorem repair12755Cells (j : Fin 43) :
    0 ≤ (scalarRow12755.table (sourceIndex j)).upper ∧
    (scalarRow12755.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12755.table (sourceIndex j)).centre) /
      (scalarRow12755.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12755.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12755,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12755,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12755,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12755,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12755,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12755,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12755,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12755,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12755,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12755,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12755,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12755,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12755,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12755,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12755,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12755,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12755,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12755,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12755,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12755,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12755,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12755,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12755,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12755,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12755,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12755,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12755,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12755,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12755,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12755,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12755,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12755,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12755,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12755,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12755,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12755,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12755,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12755,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12755,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12755,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12755,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12755,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12755,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12755,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12755,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12755,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12755,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12755,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12755,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12755,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12755,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12755,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12755,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12755,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12755,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12755,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12755,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12755,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12755,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12755,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12755,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12755,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12755,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12755,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12755,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12755,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12755,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12755,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12755,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12755,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12755,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12755,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12755,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12755,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12755,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12755,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12755,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12755,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12755,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12755,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12755,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12755,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12755,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12755,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12755,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12755,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12755 : FrameRepair 12755 scalarRow12755 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12755Cells j).1 (repair12755Cells j).2.1
  endpoint_upper := fun j => ((repair12755Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12755Cells j).2.2

theorem repair12756Cells (j : Fin 43) :
    0 ≤ (scalarRow12756.table (sourceIndex j)).upper ∧
    (scalarRow12756.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12756.table (sourceIndex j)).centre) /
      (scalarRow12756.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12756.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12756,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12756,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12756,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12756,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12756,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12756,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12756,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12756,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12756,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12756,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12756,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12756,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12756,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12756,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12756,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12756,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12756,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12756,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12756,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12756,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12756,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12756,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12756,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12756,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12756,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12756,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12756,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12756,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12756,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12756,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12756,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12756,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12756,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12756,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12756,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12756,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12756,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12756,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12756,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12756,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12756,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12756,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12756,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12756,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12756,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12756,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12756,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12756,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12756,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12756,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12756,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12756,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12756,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12756,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12756,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12756,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12756,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12756,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12756,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12756,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12756,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12756,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12756,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12756,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12756,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12756,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12756,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12756,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12756,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12756,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12756,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12756,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12756,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12756,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12756,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12756,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12756,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12756,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12756,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12756,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12756,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12756,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12756,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12756,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12756,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12756,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12756 : FrameRepair 12756 scalarRow12756 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12756Cells j).1 (repair12756Cells j).2.1
  endpoint_upper := fun j => ((repair12756Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12756Cells j).2.2

theorem repair12757Cells (j : Fin 43) :
    0 ≤ (scalarRow12757.table (sourceIndex j)).upper ∧
    (scalarRow12757.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12757.table (sourceIndex j)).centre) /
      (scalarRow12757.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12757.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12757,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12757,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12757,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12757,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12757,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12757,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12757,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12757,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12757,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12757,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12757,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12757,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12757,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12757,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12757,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12757,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12757,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12757,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12757,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12757,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12757,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12757,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12757,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12757,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12757,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12757,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12757,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12757,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12757,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12757,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12757,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12757,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12757,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12757,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12757,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12757,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12757,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12757,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12757,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12757,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12757,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12757,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12757,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12757,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12757,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12757,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12757,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12757,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12757,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12757,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12757,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12757,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12757,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12757,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12757,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12757,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12757,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12757,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12757,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12757,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12757,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12757,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12757,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12757,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12757,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12757,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12757,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12757,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12757,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12757,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12757,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12757,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12757,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12757,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12757,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12757,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12757,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12757,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12757,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12757,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12757,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12757,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12757,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12757,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12757,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12757,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12757 : FrameRepair 12757 scalarRow12757 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12757Cells j).1 (repair12757Cells j).2.1
  endpoint_upper := fun j => ((repair12757Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12757Cells j).2.2

theorem repair12758Cells (j : Fin 43) :
    0 ≤ (scalarRow12758.table (sourceIndex j)).upper ∧
    (scalarRow12758.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12758.table (sourceIndex j)).centre) /
      (scalarRow12758.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12758.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12758,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12758,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12758,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12758,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12758,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12758,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12758,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12758,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12758,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12758,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12758,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12758,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12758,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12758,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12758,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12758,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12758,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12758,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12758,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12758,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12758,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12758,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12758,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12758,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12758,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12758,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12758,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12758,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12758,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12758,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12758,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12758,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12758,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12758,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12758,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12758,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12758,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12758,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12758,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12758,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12758,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12758,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12758,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12758,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12758,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12758,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12758,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12758,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12758,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12758,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12758,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12758,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12758,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12758,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12758,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12758,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12758,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12758,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12758,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12758,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12758,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12758,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12758,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12758,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12758,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12758,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12758,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12758,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12758,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12758,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12758,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12758,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12758,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12758,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12758,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12758,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12758,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12758,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12758,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12758,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12758,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12758,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12758,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12758,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12758,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12758,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12758 : FrameRepair 12758 scalarRow12758 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12758Cells j).1 (repair12758Cells j).2.1
  endpoint_upper := fun j => ((repair12758Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12758Cells j).2.2

theorem repair12759Cells (j : Fin 43) :
    0 ≤ (scalarRow12759.table (sourceIndex j)).upper ∧
    (scalarRow12759.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12759.table (sourceIndex j)).centre) /
      (scalarRow12759.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12759.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12759,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12759,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12759,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12759,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12759,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12759,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12759,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12759,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12759,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12759,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12759,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12759,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12759,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12759,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12759,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12759,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12759,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12759,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12759,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12759,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12759,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12759,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12759,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12759,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12759,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12759,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12759,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12759,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12759,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12759,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12759,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12759,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12759,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12759,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12759,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12759,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12759,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12759,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12759,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12759,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12759,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12759,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12759,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12759,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12759,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12759,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12759,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12759,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12759,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12759,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12759,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12759,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12759,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12759,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12759,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12759,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12759,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12759,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12759,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12759,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12759,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12759,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12759,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12759,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12759,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12759,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12759,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12759,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12759,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12759,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12759,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12759,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12759,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12759,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12759,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12759,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12759,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12759,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12759,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12759,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12759,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12759,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12759,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12759,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12759,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12759,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12759 : FrameRepair 12759 scalarRow12759 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12759Cells j).1 (repair12759Cells j).2.1
  endpoint_upper := fun j => ((repair12759Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12759Cells j).2.2

theorem repair12760Cells (j : Fin 43) :
    0 ≤ (scalarRow12760.table (sourceIndex j)).upper ∧
    (scalarRow12760.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12760.table (sourceIndex j)).centre) /
      (scalarRow12760.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12760.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12760,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12760,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12760,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12760,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12760,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12760,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12760,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12760,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12760,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12760,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12760,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12760,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12760,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12760,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12760,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12760,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12760,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12760,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12760,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12760,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12760,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12760,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12760,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12760,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12760,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12760,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12760,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12760,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12760,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12760,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12760,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12760,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12760,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12760,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12760,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12760,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12760,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12760,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12760,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12760,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12760,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12760,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12760,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12760,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12760,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12760,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12760,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12760,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12760,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12760,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12760,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12760,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12760,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12760,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12760,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12760,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12760,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12760,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12760,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12760,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12760,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12760,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12760,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12760,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12760,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12760,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12760,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12760,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12760,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12760,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12760,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12760,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12760,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12760,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12760,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12760,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12760,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12760,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12760,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12760,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12760,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12760,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12760,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12760,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12760,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12760,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12760 : FrameRepair 12760 scalarRow12760 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12760Cells j).1 (repair12760Cells j).2.1
  endpoint_upper := fun j => ((repair12760Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12760Cells j).2.2

theorem repair12761Cells (j : Fin 43) :
    0 ≤ (scalarRow12761.table (sourceIndex j)).upper ∧
    (scalarRow12761.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12761.table (sourceIndex j)).centre) /
      (scalarRow12761.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12761.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12761,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12761,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12761,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12761,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12761,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12761,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12761,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12761,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12761,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12761,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12761,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12761,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12761,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12761,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12761,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12761,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12761,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12761,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12761,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12761,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12761,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12761,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12761,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12761,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12761,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12761,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12761,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12761,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12761,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12761,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12761,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12761,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12761,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12761,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12761,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12761,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12761,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12761,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12761,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12761,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12761,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12761,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12761,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12761,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12761,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12761,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12761,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12761,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12761,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12761,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12761,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12761,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12761,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12761,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12761,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12761,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12761,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12761,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12761,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12761,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12761,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12761,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12761,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12761,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12761,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12761,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12761,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12761,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12761,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12761,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12761,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12761,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12761,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12761,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12761,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12761,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12761,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12761,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12761,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12761,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12761,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12761,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12761,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12761,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12761,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12761,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12761 : FrameRepair 12761 scalarRow12761 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12761Cells j).1 (repair12761Cells j).2.1
  endpoint_upper := fun j => ((repair12761Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12761Cells j).2.2

theorem repair12762Cells (j : Fin 43) :
    0 ≤ (scalarRow12762.table (sourceIndex j)).upper ∧
    (scalarRow12762.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12762.table (sourceIndex j)).centre) /
      (scalarRow12762.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12762.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12762,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12762,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12762,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12762,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12762,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12762,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12762,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12762,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12762,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12762,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12762,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12762,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12762,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12762,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12762,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12762,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12762,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12762,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12762,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12762,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12762,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12762,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12762,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12762,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12762,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12762,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12762,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12762,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12762,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12762,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12762,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12762,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12762,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12762,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12762,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12762,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12762,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12762,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12762,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12762,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12762,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12762,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12762,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12762,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12762,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12762,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12762,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12762,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12762,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12762,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12762,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12762,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12762,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12762,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12762,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12762,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12762,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12762,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12762,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12762,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12762,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12762,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12762,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12762,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12762,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12762,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12762,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12762,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12762,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12762,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12762,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12762,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12762,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12762,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12762,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12762,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12762,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12762,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12762,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12762,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12762,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12762,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12762,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12762,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12762,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12762,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12762 : FrameRepair 12762 scalarRow12762 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12762Cells j).1 (repair12762Cells j).2.1
  endpoint_upper := fun j => ((repair12762Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12762Cells j).2.2

theorem repair12763Cells (j : Fin 43) :
    0 ≤ (scalarRow12763.table (sourceIndex j)).upper ∧
    (scalarRow12763.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12763.table (sourceIndex j)).centre) /
      (scalarRow12763.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12763.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12763,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12763,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12763,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12763,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12763,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12763,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12763,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12763,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12763,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12763,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12763,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12763,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12763,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12763,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12763,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12763,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12763,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12763,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12763,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12763,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12763,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12763,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12763,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12763,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12763,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12763,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12763,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12763,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12763,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12763,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12763,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12763,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12763,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12763,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12763,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12763,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12763,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12763,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12763,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12763,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12763,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12763,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12763,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12763,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12763,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12763,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12763,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12763,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12763,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12763,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12763,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12763,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12763,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12763,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12763,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12763,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12763,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12763,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12763,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12763,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12763,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12763,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12763,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12763,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12763,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12763,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12763,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12763,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12763,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12763,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12763,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12763,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12763,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12763,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12763,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12763,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12763,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12763,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12763,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12763,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12763,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12763,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12763,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12763,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12763,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12763,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12763 : FrameRepair 12763 scalarRow12763 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12763Cells j).1 (repair12763Cells j).2.1
  endpoint_upper := fun j => ((repair12763Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12763Cells j).2.2

theorem repair12764Cells (j : Fin 43) :
    0 ≤ (scalarRow12764.table (sourceIndex j)).upper ∧
    (scalarRow12764.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12764.table (sourceIndex j)).centre) /
      (scalarRow12764.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12764.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12764,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12764,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12764,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12764,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12764,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12764,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12764,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12764,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12764,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12764,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12764,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12764,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12764,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12764,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12764,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12764,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12764,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12764,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12764,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12764,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12764,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12764,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12764,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12764,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12764,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12764,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12764,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12764,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12764,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12764,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12764,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12764,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12764,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12764,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12764,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12764,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12764,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12764,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12764,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12764,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12764,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12764,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12764,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12764,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12764,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12764,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12764,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12764,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12764,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12764,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12764,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12764,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12764,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12764,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12764,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12764,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12764,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12764,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12764,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12764,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12764,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12764,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12764,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12764,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12764,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12764,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12764,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12764,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12764,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12764,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12764,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12764,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12764,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12764,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12764,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12764,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12764,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12764,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12764,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12764,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12764,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12764,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12764,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12764,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12764,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12764,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12764 : FrameRepair 12764 scalarRow12764 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12764Cells j).1 (repair12764Cells j).2.1
  endpoint_upper := fun j => ((repair12764Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12764Cells j).2.2

theorem repair12765Cells (j : Fin 43) :
    0 ≤ (scalarRow12765.table (sourceIndex j)).upper ∧
    (scalarRow12765.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12765.table (sourceIndex j)).centre) /
      (scalarRow12765.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12765.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12765,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12765,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12765,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12765,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12765,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12765,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12765,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12765,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12765,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12765,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12765,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12765,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12765,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12765,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12765,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12765,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12765,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12765,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12765,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12765,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12765,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12765,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12765,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12765,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12765,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12765,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12765,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12765,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12765,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12765,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12765,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12765,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12765,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12765,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12765,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12765,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12765,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12765,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12765,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12765,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12765,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12765,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12765,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12765,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12765,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12765,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12765,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12765,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12765,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12765,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12765,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12765,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12765,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12765,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12765,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12765,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12765,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12765,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12765,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12765,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12765,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12765,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12765,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12765,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12765,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12765,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12765,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12765,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12765,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12765,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12765,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12765,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12765,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12765,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12765,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12765,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12765,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12765,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12765,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12765,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12765,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12765,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12765,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12765,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12765,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12765,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12765 : FrameRepair 12765 scalarRow12765 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12765Cells j).1 (repair12765Cells j).2.1
  endpoint_upper := fun j => ((repair12765Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12765Cells j).2.2

theorem repair12766Cells (j : Fin 43) :
    0 ≤ (scalarRow12766.table (sourceIndex j)).upper ∧
    (scalarRow12766.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12766.table (sourceIndex j)).centre) /
      (scalarRow12766.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12766.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12766,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12766,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12766,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12766,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12766,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12766,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12766,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12766,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12766,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12766,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12766,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12766,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12766,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12766,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12766,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12766,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12766,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12766,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12766,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12766,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12766,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12766,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12766,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12766,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12766,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12766,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12766,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12766,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12766,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12766,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12766,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12766,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12766,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12766,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12766,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12766,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12766,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12766,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12766,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12766,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12766,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12766,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12766,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12766,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12766,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12766,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12766,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12766,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12766,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12766,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12766,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12766,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12766,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12766,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12766,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12766,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12766,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12766,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12766,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12766,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12766,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12766,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12766,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12766,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12766,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12766,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12766,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12766,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12766,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12766,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12766,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12766,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12766,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12766,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12766,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12766,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12766,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12766,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12766,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12766,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12766,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12766,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12766,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12766,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12766,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12766,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12766 : FrameRepair 12766 scalarRow12766 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12766Cells j).1 (repair12766Cells j).2.1
  endpoint_upper := fun j => ((repair12766Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12766Cells j).2.2

theorem repair12767Cells (j : Fin 43) :
    0 ≤ (scalarRow12767.table (sourceIndex j)).upper ∧
    (scalarRow12767.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12767.table (sourceIndex j)).centre) /
      (scalarRow12767.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12767.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12767,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12767,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12767,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12767,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12767,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12767,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12767,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12767,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12767,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12767,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12767,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12767,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12767,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12767,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12767,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12767,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12767,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12767,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12767,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12767,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12767,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12767,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12767,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12767,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12767,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12767,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12767,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12767,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12767,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12767,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12767,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12767,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12767,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12767,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12767,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12767,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12767,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12767,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12767,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12767,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12767,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12767,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12767,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12767,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12767,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12767,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12767,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12767,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12767,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12767,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12767,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12767,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12767,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12767,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12767,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12767,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12767,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12767,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12767,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12767,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12767,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12767,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12767,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12767,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12767,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12767,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12767,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12767,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12767,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12767,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12767,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12767,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12767,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12767,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12767,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12767,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12767,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12767,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12767,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12767,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12767,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12767,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12767,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12767,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12767,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12767,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12767 : FrameRepair 12767 scalarRow12767 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12767Cells j).1 (repair12767Cells j).2.1
  endpoint_upper := fun j => ((repair12767Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12767Cells j).2.2

theorem repair12768Cells (j : Fin 43) :
    0 ≤ (scalarRow12768.table (sourceIndex j)).upper ∧
    (scalarRow12768.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12768.table (sourceIndex j)).centre) /
      (scalarRow12768.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12768.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12768,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12768,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12768,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12768,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12768,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12768,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12768,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12768,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12768,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12768,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12768,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12768,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12768,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12768,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12768,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12768,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12768,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12768,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12768,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12768,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12768,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12768,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12768,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12768,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12768,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12768,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12768,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12768,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12768,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12768,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12768,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12768,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12768,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12768,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12768,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12768,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12768,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12768,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12768,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12768,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12768,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12768,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12768,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12768,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12768,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12768,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12768,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12768,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12768,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12768,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12768,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12768,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12768,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12768,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12768,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12768,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12768,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12768,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12768,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12768,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12768,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12768,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12768,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12768,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12768,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12768,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12768,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12768,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12768,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12768,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12768,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12768,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12768,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12768,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12768,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12768,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12768,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12768,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12768,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12768,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12768,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12768,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12768,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12768,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12768,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12768,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12768 : FrameRepair 12768 scalarRow12768 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12768Cells j).1 (repair12768Cells j).2.1
  endpoint_upper := fun j => ((repair12768Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12768Cells j).2.2

theorem repair12769Cells (j : Fin 43) :
    0 ≤ (scalarRow12769.table (sourceIndex j)).upper ∧
    (scalarRow12769.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12769.table (sourceIndex j)).centre) /
      (scalarRow12769.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12769.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12769,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12769,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12769,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12769,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12769,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12769,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12769,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12769,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12769,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12769,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12769,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12769,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12769,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12769,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12769,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12769,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12769,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12769,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12769,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12769,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12769,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12769,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12769,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12769,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12769,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12769,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12769,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12769,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12769,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12769,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12769,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12769,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12769,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12769,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12769,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12769,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12769,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12769,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12769,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12769,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12769,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12769,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12769,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12769,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12769,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12769,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12769,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12769,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12769,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12769,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12769,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12769,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12769,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12769,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12769,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12769,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12769,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12769,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12769,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12769,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12769,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12769,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12769,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12769,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12769,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12769,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12769,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12769,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12769,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12769,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12769,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12769,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12769,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12769,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12769,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12769,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12769,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12769,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12769,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12769,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12769,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12769,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12769,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12769,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12769,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12769,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12769 : FrameRepair 12769 scalarRow12769 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12769Cells j).1 (repair12769Cells j).2.1
  endpoint_upper := fun j => ((repair12769Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12769Cells j).2.2

theorem repair12770Cells (j : Fin 43) :
    0 ≤ (scalarRow12770.table (sourceIndex j)).upper ∧
    (scalarRow12770.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12770.table (sourceIndex j)).centre) /
      (scalarRow12770.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12770.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12770,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12770,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12770,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12770,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12770,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12770,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12770,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12770,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12770,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12770,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12770,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12770,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12770,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12770,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12770,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12770,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12770,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12770,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12770,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12770,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12770,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12770,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12770,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12770,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12770,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12770,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12770,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12770,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12770,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12770,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12770,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12770,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12770,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12770,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12770,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12770,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12770,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12770,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12770,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12770,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12770,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12770,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12770,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12770,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12770,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12770,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12770,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12770,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12770,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12770,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12770,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12770,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12770,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12770,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12770,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12770,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12770,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12770,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12770,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12770,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12770,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12770,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12770,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12770,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12770,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12770,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12770,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12770,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12770,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12770,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12770,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12770,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12770,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12770,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12770,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12770,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12770,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12770,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12770,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12770,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12770,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12770,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12770,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12770,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12770,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12770,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12770 : FrameRepair 12770 scalarRow12770 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12770Cells j).1 (repair12770Cells j).2.1
  endpoint_upper := fun j => ((repair12770Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12770Cells j).2.2

theorem repair12771Cells (j : Fin 43) :
    0 ≤ (scalarRow12771.table (sourceIndex j)).upper ∧
    (scalarRow12771.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12771.table (sourceIndex j)).centre) /
      (scalarRow12771.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12771.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12771,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12771,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12771,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12771,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12771,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12771,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12771,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12771,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12771,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12771,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12771,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12771,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12771,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12771,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12771,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12771,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12771,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12771,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12771,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12771,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12771,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12771,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12771,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12771,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12771,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12771,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12771,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12771,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12771,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12771,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12771,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12771,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12771,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12771,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12771,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12771,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12771,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12771,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12771,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12771,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12771,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12771,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12771,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12771,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12771,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12771,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12771,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12771,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12771,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12771,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12771,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12771,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12771,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12771,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12771,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12771,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12771,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12771,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12771,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12771,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12771,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12771,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12771,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12771,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12771,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12771,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12771,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12771,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12771,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12771,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12771,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12771,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12771,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12771,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12771,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12771,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12771,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12771,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12771,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12771,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12771,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12771,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12771,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12771,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12771,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12771,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12771 : FrameRepair 12771 scalarRow12771 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12771Cells j).1 (repair12771Cells j).2.1
  endpoint_upper := fun j => ((repair12771Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12771Cells j).2.2

theorem repair12772Cells (j : Fin 43) :
    0 ≤ (scalarRow12772.table (sourceIndex j)).upper ∧
    (scalarRow12772.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12772.table (sourceIndex j)).centre) /
      (scalarRow12772.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12772.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12772,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12772,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12772,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12772,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12772,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12772,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12772,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12772,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12772,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12772,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12772,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12772,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12772,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12772,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12772,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12772,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12772,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12772,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12772,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12772,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12772,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12772,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12772,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12772,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12772,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12772,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12772,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12772,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12772,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12772,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12772,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12772,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12772,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12772,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12772,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12772,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12772,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12772,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12772,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12772,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12772,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12772,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12772,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12772,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12772,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12772,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12772,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12772,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12772,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12772,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12772,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12772,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12772,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12772,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12772,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12772,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12772,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12772,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12772,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12772,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12772,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12772,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12772,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12772,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12772,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12772,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12772,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12772,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12772,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12772,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12772,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12772,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12772,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12772,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12772,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12772,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12772,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12772,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12772,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12772,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12772,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12772,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12772,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12772,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12772,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12772,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12772 : FrameRepair 12772 scalarRow12772 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12772Cells j).1 (repair12772Cells j).2.1
  endpoint_upper := fun j => ((repair12772Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12772Cells j).2.2

theorem repair12773Cells (j : Fin 43) :
    0 ≤ (scalarRow12773.table (sourceIndex j)).upper ∧
    (scalarRow12773.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12773.table (sourceIndex j)).centre) /
      (scalarRow12773.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12773.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12773,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12773,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12773,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12773,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12773,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12773,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12773,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12773,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12773,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12773,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12773,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12773,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12773,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12773,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12773,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12773,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12773,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12773,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12773,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12773,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12773,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12773,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12773,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12773,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12773,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12773,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12773,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12773,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12773,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12773,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12773,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12773,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12773,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12773,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12773,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12773,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12773,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12773,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12773,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12773,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12773,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12773,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12773,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12773,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12773,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12773,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12773,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12773,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12773,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12773,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12773,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12773,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12773,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12773,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12773,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12773,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12773,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12773,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12773,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12773,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12773,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12773,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12773,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12773,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12773,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12773,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12773,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12773,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12773,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12773,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12773,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12773,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12773,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12773,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12773,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12773,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12773,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12773,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12773,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12773,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12773,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12773,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12773,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12773,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12773,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12773,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12773 : FrameRepair 12773 scalarRow12773 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12773Cells j).1 (repair12773Cells j).2.1
  endpoint_upper := fun j => ((repair12773Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12773Cells j).2.2

theorem repair12774Cells (j : Fin 43) :
    0 ≤ (scalarRow12774.table (sourceIndex j)).upper ∧
    (scalarRow12774.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12774.table (sourceIndex j)).centre) /
      (scalarRow12774.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12774.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12774,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12774,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12774,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12774,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12774,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12774,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12774,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12774,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12774,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12774,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12774,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12774,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12774,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12774,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12774,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12774,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12774,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12774,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12774,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12774,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12774,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12774,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12774,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12774,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12774,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12774,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12774,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12774,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12774,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12774,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12774,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12774,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12774,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12774,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12774,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12774,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12774,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12774,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12774,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12774,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12774,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12774,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12774,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12774,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12774,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12774,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12774,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12774,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12774,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12774,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12774,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12774,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12774,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12774,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12774,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12774,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12774,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12774,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12774,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12774,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12774,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12774,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12774,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12774,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12774,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12774,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12774,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12774,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12774,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12774,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12774,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12774,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12774,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12774,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12774,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12774,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12774,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12774,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12774,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12774,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12774,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12774,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12774,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12774,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12774,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12774,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12774 : FrameRepair 12774 scalarRow12774 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12774Cells j).1 (repair12774Cells j).2.1
  endpoint_upper := fun j => ((repair12774Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12774Cells j).2.2

end BstLean.Part269
