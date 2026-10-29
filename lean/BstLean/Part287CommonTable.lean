import BstLean.Part287TableCells0
import BstLean.Part287TableCells1
import BstLean.Part287TableCells2
import BstLean.Part287TableCells3
import BstLean.Part287TableCells4
import BstLean.Part287TableCells5
import BstLean.Part287TableFrames0
import BstLean.Part287TableFrames1
import BstLean.Part287TableFrames2
import BstLean.Part287TableFrames3

namespace BstLean.Part287.CommonTable
open Real Set BstLean.Part263 BstLean.Part271.R4

theorem certificates (i : Fin 60) :
    BstLean.Part271.R4.CellCertificate 13225 13234 (8639390951/100000000000) (794107922495109/500000000000000000) (3353042747/100000000000) (table i) := by
  match i with
  | ⟨0,_⟩ => exact certificate0
  | ⟨1,_⟩ => exact certificate1
  | ⟨2,_⟩ => exact certificate2
  | ⟨3,_⟩ => exact certificate3
  | ⟨4,_⟩ => exact certificate4
  | ⟨5,_⟩ => exact certificate5
  | ⟨6,_⟩ => exact certificate6
  | ⟨7,_⟩ => exact certificate7
  | ⟨8,_⟩ => exact certificate8
  | ⟨9,_⟩ => exact certificate9
  | ⟨10,_⟩ => exact certificate10
  | ⟨11,_⟩ => exact certificate11
  | ⟨12,_⟩ => exact certificate12
  | ⟨13,_⟩ => exact certificate13
  | ⟨14,_⟩ => exact certificate14
  | ⟨15,_⟩ => exact certificate15
  | ⟨16,_⟩ => exact certificate16
  | ⟨17,_⟩ => exact certificate17
  | ⟨18,_⟩ => exact certificate18
  | ⟨19,_⟩ => exact certificate19
  | ⟨20,_⟩ => exact certificate20
  | ⟨21,_⟩ => exact certificate21
  | ⟨22,_⟩ => exact certificate22
  | ⟨23,_⟩ => exact certificate23
  | ⟨24,_⟩ => exact certificate24
  | ⟨25,_⟩ => exact certificate25
  | ⟨26,_⟩ => exact certificate26
  | ⟨27,_⟩ => exact certificate27
  | ⟨28,_⟩ => exact certificate28
  | ⟨29,_⟩ => exact certificate29
  | ⟨30,_⟩ => exact certificate30
  | ⟨31,_⟩ => exact certificate31
  | ⟨32,_⟩ => exact certificate32
  | ⟨33,_⟩ => exact certificate33
  | ⟨34,_⟩ => exact certificate34
  | ⟨35,_⟩ => exact certificate35
  | ⟨36,_⟩ => exact certificate36
  | ⟨37,_⟩ => exact certificate37
  | ⟨38,_⟩ => exact certificate38
  | ⟨39,_⟩ => exact certificate39
  | ⟨40,_⟩ => exact certificate40
  | ⟨41,_⟩ => exact certificate41
  | ⟨42,_⟩ => exact certificate42
  | ⟨43,_⟩ => exact certificate43
  | ⟨44,_⟩ => exact certificate44
  | ⟨45,_⟩ => exact certificate45
  | ⟨46,_⟩ => exact certificate46
  | ⟨47,_⟩ => exact certificate47
  | ⟨48,_⟩ => exact certificate48
  | ⟨49,_⟩ => exact certificate49
  | ⟨50,_⟩ => exact certificate50
  | ⟨51,_⟩ => exact certificate51
  | ⟨52,_⟩ => exact certificate52
  | ⟨53,_⟩ => exact certificate53
  | ⟨54,_⟩ => exact certificate54
  | ⟨55,_⟩ => exact certificate55
  | ⟨56,_⟩ => exact certificate56
  | ⟨57,_⟩ => exact certificate57
  | ⟨58,_⟩ => exact certificate58
  | ⟨59,_⟩ => exact certificate59
  | ⟨j+60,h⟩ => exact False.elim (by omega)

noncomputable def tableCertificate : TableCertificate 13225 13234 where
  M := (8639390951/100000000000)
  H := (794107922495109/500000000000000000)
  xi := (3353042747/100000000000)
  targetFrame := (728206725421151407/500000000000000000)
  gridCertificate := gridCertificate
  table := table
  certificates := certificates
  energy := by norm_num [energyBound, layerBound]
  frame := by
    intro i hi
    fin_cases i <;> simp at hi
    all_goals norm_num [table]
  containment := by
    intro i
    fin_cases i <;> norm_num [table, gridCertificate, noiseNode]

theorem repairCells (j : Fin 43) :
    0 ≤ cap j ∧
    envelope 13225 (BstLean.Part255.parameters j)
      (table (BstLean.Part255.sourceIndex j)).upper ≤ cap j ∧
    (table (BstLean.Part255.sourceIndex j)).upper ∈ Icc (0 : ℝ) (528/1000) ∧
    (cap j + (table (BstLean.Part255.sourceIndex j)).centre) /
      (table (BstLean.Part255.sourceIndex j)).cutoff + 11/1000 ≤ (728206725421151407/500000000000000000) := by
  match j with
  | ⟨0,_⟩ => exact repairCell0
  | ⟨1,_⟩ => exact repairCell1
  | ⟨2,_⟩ => exact repairCell2
  | ⟨3,_⟩ => exact repairCell3
  | ⟨4,_⟩ => exact repairCell4
  | ⟨5,_⟩ => exact repairCell5
  | ⟨6,_⟩ => exact repairCell6
  | ⟨7,_⟩ => exact repairCell7
  | ⟨8,_⟩ => exact repairCell8
  | ⟨9,_⟩ => exact repairCell9
  | ⟨10,_⟩ => exact repairCell10
  | ⟨11,_⟩ => exact repairCell11
  | ⟨12,_⟩ => exact repairCell12
  | ⟨13,_⟩ => exact repairCell13
  | ⟨14,_⟩ => exact repairCell14
  | ⟨15,_⟩ => exact repairCell15
  | ⟨16,_⟩ => exact repairCell16
  | ⟨17,_⟩ => exact repairCell17
  | ⟨18,_⟩ => exact repairCell18
  | ⟨19,_⟩ => exact repairCell19
  | ⟨20,_⟩ => exact repairCell20
  | ⟨21,_⟩ => exact repairCell21
  | ⟨22,_⟩ => exact repairCell22
  | ⟨23,_⟩ => exact repairCell23
  | ⟨24,_⟩ => exact repairCell24
  | ⟨25,_⟩ => exact repairCell25
  | ⟨26,_⟩ => exact repairCell26
  | ⟨27,_⟩ => exact repairCell27
  | ⟨28,_⟩ => exact repairCell28
  | ⟨29,_⟩ => exact repairCell29
  | ⟨30,_⟩ => exact repairCell30
  | ⟨31,_⟩ => exact repairCell31
  | ⟨32,_⟩ => exact repairCell32
  | ⟨33,_⟩ => exact repairCell33
  | ⟨34,_⟩ => exact repairCell34
  | ⟨35,_⟩ => exact repairCell35
  | ⟨36,_⟩ => exact repairCell36
  | ⟨37,_⟩ => exact repairCell37
  | ⟨38,_⟩ => exact repairCell38
  | ⟨39,_⟩ => exact repairCell39
  | ⟨40,_⟩ => exact repairCell40
  | ⟨41,_⟩ => exact repairCell41
  | ⟨42,_⟩ => exact repairCell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def frameCertificate : FrameCertificate tableCertificate where
  dimension := by norm_num
  cap := cap
  cap_nonneg := fun j => (repairCells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap])
  endpoint := fun j => (repairCells j).2.1
  endpoint_range := fun j => (repairCells j).2.2.1
  frame := fun j => (repairCells j).2.2.2


end BstLean.Part287.CommonTable
