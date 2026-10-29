import BstLean.Part255Covariance
namespace BstLean.Part255
open Real Set

theorem localCap_grid (j : Fin 43) : ∃ q : ℕ, localCap j = (q : ℝ)/10^9 := by
  match j with
  | ⟨0,_⟩ => exact ⟨275952734,by norm_num [localCap]⟩
  | ⟨1,_⟩ => exact ⟨276356006,by norm_num [localCap]⟩
  | ⟨2,_⟩ => exact ⟨276758283,by norm_num [localCap]⟩
  | ⟨3,_⟩ => exact ⟨277159561,by norm_num [localCap]⟩
  | ⟨4,_⟩ => exact ⟨277559849,by norm_num [localCap]⟩
  | ⟨5,_⟩ => exact ⟨277959145,by norm_num [localCap]⟩
  | ⟨6,_⟩ => exact ⟨278356980,by norm_num [localCap]⟩
  | ⟨7,_⟩ => exact ⟨278754308,by norm_num [localCap]⟩
  | ⟨8,_⟩ => exact ⟨279150659,by norm_num [localCap]⟩
  | ⟨9,_⟩ => exact ⟨279546037,by norm_num [localCap]⟩
  | ⟨10,_⟩ => exact ⟨279940443,by norm_num [localCap]⟩
  | ⟨11,_⟩ => exact ⟨280333399,by norm_num [localCap]⟩
  | ⟨12,_⟩ => exact ⟨280725878,by norm_num [localCap]⟩
  | ⟨13,_⟩ => exact ⟨281116908,by norm_num [localCap]⟩
  | ⟨14,_⟩ => exact ⟨281507870,by norm_num [localCap]⟩
  | ⟨15,_⟩ => exact ⟨281897732,by norm_num [localCap]⟩
  | ⟨16,_⟩ => exact ⟨282286650,by norm_num [localCap]⟩
  | ⟨17,_⟩ => exact ⟨282674636,by norm_num [localCap]⟩
  | ⟨18,_⟩ => exact ⟨283061682,by norm_num [localCap]⟩
  | ⟨19,_⟩ => exact ⟨283447798,by norm_num [localCap]⟩
  | ⟨20,_⟩ => exact ⟨283832987,by norm_num [localCap]⟩
  | ⟨21,_⟩ => exact ⟨284217258,by norm_num [localCap]⟩
  | ⟨22,_⟩ => exact ⟨284600604,by norm_num [localCap]⟩
  | ⟨23,_⟩ => exact ⟨284982539,by norm_num [localCap]⟩
  | ⟨24,_⟩ => exact ⟨285364060,by norm_num [localCap]⟩
  | ⟨25,_⟩ => exact ⟨285744219,by norm_num [localCap]⟩
  | ⟨26,_⟩ => exact ⟨286123973,by norm_num [localCap]⟩
  | ⟨27,_⟩ => exact ⟨286502327,by norm_num [localCap]⟩
  | ⟨28,_⟩ => exact ⟨286879783,by norm_num [localCap]⟩
  | ⟨29,_⟩ => exact ⟨287256343,by norm_num [localCap]⟩
  | ⟨30,_⟩ => exact ⟨287631508,by norm_num [localCap]⟩
  | ⟨31,_⟩ => exact ⟨288006288,by norm_num [localCap]⟩
  | ⟨32,_⟩ => exact ⟨288380186,by norm_num [localCap]⟩
  | ⟨33,_⟩ => exact ⟨288752694,by norm_num [localCap]⟩
  | ⟨34,_⟩ => exact ⟨289124325,by norm_num [localCap]⟩
  | ⟨35,_⟩ => exact ⟨289495084,by norm_num [localCap]⟩
  | ⟨36,_⟩ => exact ⟨289864965,by norm_num [localCap]⟩
  | ⟨37,_⟩ => exact ⟨290233986,by norm_num [localCap]⟩
  | ⟨38,_⟩ => exact ⟨290602141,by norm_num [localCap]⟩
  | ⟨39,_⟩ => exact ⟨290968923,by norm_num [localCap]⟩
  | ⟨40,_⟩ => exact ⟨291334845,by norm_num [localCap]⟩
  | ⟨41,_⟩ => exact ⟨291699915,by norm_num [localCap]⟩
  | ⟨42,_⟩ => exact ⟨291823659,by norm_num [localCap]⟩
  | ⟨j+43,h⟩ => exact False.elim (by omega)

theorem least_grid_envelope_cap (j : Fin 43) (q : ℕ)
    (hq : envelope (parameters j) (BstLean.Part254.cellUpper (sourceIndex j)) ≤
      (q : ℝ)/10^9) : localCap j ≤ (q : ℝ)/10^9 := by
  obtain ⟨p,hp⟩ := localCap_grid j
  by_contra h
  have hqp : (q : ℝ) < p := by rw [hp] at h; linarith
  have hqpN : q < p := by exact_mod_cast hqp
  have hs : (q : ℝ)+1 ≤ p := by exact_mod_cast (Nat.succ_le_iff.mpr hqpN)
  have hr : (q : ℝ)/10^9 ≤ localCap j-1/10^9 := by rw [hp]; linarith
  exact (not_lt_of_ge (hq.trans hr)) (grid j).2.1

theorem paperComparison0 :
    (BstLean.Part251.rowCellAudit (sourceIndex ⟨0,by decide⟩)).covarianceCap <
      localCap ⟨0,by decide⟩ := by
  change (BstLean.Part251.auditCell10).covarianceCap < localCap ⟨0,by decide⟩
  norm_num [BstLean.Part251.auditCell10,localCap]

theorem paperComparison1 :
    (BstLean.Part251.rowCellAudit (sourceIndex ⟨1,by decide⟩)).covarianceCap <
      localCap ⟨1,by decide⟩ := by
  change (BstLean.Part251.auditCell11).covarianceCap < localCap ⟨1,by decide⟩
  norm_num [BstLean.Part251.auditCell11,localCap]

theorem paperComparison2 :
    (BstLean.Part251.rowCellAudit (sourceIndex ⟨2,by decide⟩)).covarianceCap <
      localCap ⟨2,by decide⟩ := by
  change (BstLean.Part251.auditCell12).covarianceCap < localCap ⟨2,by decide⟩
  norm_num [BstLean.Part251.auditCell12,localCap]

theorem paperComparison3 :
    (BstLean.Part251.rowCellAudit (sourceIndex ⟨3,by decide⟩)).covarianceCap <
      localCap ⟨3,by decide⟩ := by
  change (BstLean.Part251.auditCell13).covarianceCap < localCap ⟨3,by decide⟩
  norm_num [BstLean.Part251.auditCell13,localCap]

theorem paperComparison4 :
    (BstLean.Part251.rowCellAudit (sourceIndex ⟨4,by decide⟩)).covarianceCap <
      localCap ⟨4,by decide⟩ := by
  change (BstLean.Part251.auditCell14).covarianceCap < localCap ⟨4,by decide⟩
  norm_num [BstLean.Part251.auditCell14,localCap]

theorem paperComparison5 :
    (BstLean.Part251.rowCellAudit (sourceIndex ⟨5,by decide⟩)).covarianceCap <
      localCap ⟨5,by decide⟩ := by
  change (BstLean.Part251.auditCell15).covarianceCap < localCap ⟨5,by decide⟩
  norm_num [BstLean.Part251.auditCell15,localCap]

theorem paperComparison6 :
    (BstLean.Part251.rowCellAudit (sourceIndex ⟨6,by decide⟩)).covarianceCap <
      localCap ⟨6,by decide⟩ := by
  change (BstLean.Part251.auditCell16).covarianceCap < localCap ⟨6,by decide⟩
  norm_num [BstLean.Part251.auditCell16,localCap]

theorem paperComparison7 :
    (BstLean.Part251.rowCellAudit (sourceIndex ⟨7,by decide⟩)).covarianceCap <
      localCap ⟨7,by decide⟩ := by
  change (BstLean.Part251.auditCell17).covarianceCap < localCap ⟨7,by decide⟩
  norm_num [BstLean.Part251.auditCell17,localCap]

theorem paperComparison8 :
    (BstLean.Part251.rowCellAudit (sourceIndex ⟨8,by decide⟩)).covarianceCap <
      localCap ⟨8,by decide⟩ := by
  change (BstLean.Part251.auditCell18).covarianceCap < localCap ⟨8,by decide⟩
  norm_num [BstLean.Part251.auditCell18,localCap]

theorem paperComparison9 :
    (BstLean.Part251.rowCellAudit (sourceIndex ⟨9,by decide⟩)).covarianceCap <
      localCap ⟨9,by decide⟩ := by
  change (BstLean.Part251.auditCell19).covarianceCap < localCap ⟨9,by decide⟩
  norm_num [BstLean.Part251.auditCell19,localCap]

theorem paperComparison10 :
    (BstLean.Part251.rowCellAudit (sourceIndex ⟨10,by decide⟩)).covarianceCap <
      localCap ⟨10,by decide⟩ := by
  change (BstLean.Part251.auditCell20).covarianceCap < localCap ⟨10,by decide⟩
  norm_num [BstLean.Part251.auditCell20,localCap]

theorem paperComparison11 :
    (BstLean.Part251.rowCellAudit (sourceIndex ⟨11,by decide⟩)).covarianceCap <
      localCap ⟨11,by decide⟩ := by
  change (BstLean.Part251.auditCell21).covarianceCap < localCap ⟨11,by decide⟩
  norm_num [BstLean.Part251.auditCell21,localCap]

theorem paperComparison12 :
    (BstLean.Part251.rowCellAudit (sourceIndex ⟨12,by decide⟩)).covarianceCap <
      localCap ⟨12,by decide⟩ := by
  change (BstLean.Part251.auditCell22).covarianceCap < localCap ⟨12,by decide⟩
  norm_num [BstLean.Part251.auditCell22,localCap]

theorem paperComparison13 :
    (BstLean.Part251.rowCellAudit (sourceIndex ⟨13,by decide⟩)).covarianceCap <
      localCap ⟨13,by decide⟩ := by
  change (BstLean.Part251.auditCell23).covarianceCap < localCap ⟨13,by decide⟩
  norm_num [BstLean.Part251.auditCell23,localCap]

theorem paperComparison14 :
    (BstLean.Part251.rowCellAudit (sourceIndex ⟨14,by decide⟩)).covarianceCap <
      localCap ⟨14,by decide⟩ := by
  change (BstLean.Part251.auditCell24).covarianceCap < localCap ⟨14,by decide⟩
  norm_num [BstLean.Part251.auditCell24,localCap]

theorem paperComparison15 :
    (BstLean.Part251.rowCellAudit (sourceIndex ⟨15,by decide⟩)).covarianceCap <
      localCap ⟨15,by decide⟩ := by
  change (BstLean.Part251.auditCell25).covarianceCap < localCap ⟨15,by decide⟩
  norm_num [BstLean.Part251.auditCell25,localCap]

theorem paperComparison16 :
    (BstLean.Part251.rowCellAudit (sourceIndex ⟨16,by decide⟩)).covarianceCap <
      localCap ⟨16,by decide⟩ := by
  change (BstLean.Part251.auditCell26).covarianceCap < localCap ⟨16,by decide⟩
  norm_num [BstLean.Part251.auditCell26,localCap]

theorem paperComparison17 :
    (BstLean.Part251.rowCellAudit (sourceIndex ⟨17,by decide⟩)).covarianceCap <
      localCap ⟨17,by decide⟩ := by
  change (BstLean.Part251.auditCell27).covarianceCap < localCap ⟨17,by decide⟩
  norm_num [BstLean.Part251.auditCell27,localCap]

theorem paperComparison18 :
    (BstLean.Part251.rowCellAudit (sourceIndex ⟨18,by decide⟩)).covarianceCap <
      localCap ⟨18,by decide⟩ := by
  change (BstLean.Part251.auditCell28).covarianceCap < localCap ⟨18,by decide⟩
  norm_num [BstLean.Part251.auditCell28,localCap]

theorem paperComparison19 :
    (BstLean.Part251.rowCellAudit (sourceIndex ⟨19,by decide⟩)).covarianceCap <
      localCap ⟨19,by decide⟩ := by
  change (BstLean.Part251.auditCell29).covarianceCap < localCap ⟨19,by decide⟩
  norm_num [BstLean.Part251.auditCell29,localCap]

theorem paperComparison20 :
    (BstLean.Part251.rowCellAudit (sourceIndex ⟨20,by decide⟩)).covarianceCap <
      localCap ⟨20,by decide⟩ := by
  change (BstLean.Part251.auditCell30).covarianceCap < localCap ⟨20,by decide⟩
  norm_num [BstLean.Part251.auditCell30,localCap]

theorem paperComparison21 :
    (BstLean.Part251.rowCellAudit (sourceIndex ⟨21,by decide⟩)).covarianceCap <
      localCap ⟨21,by decide⟩ := by
  change (BstLean.Part251.auditCell31).covarianceCap < localCap ⟨21,by decide⟩
  norm_num [BstLean.Part251.auditCell31,localCap]

theorem paperComparison22 :
    (BstLean.Part251.rowCellAudit (sourceIndex ⟨22,by decide⟩)).covarianceCap <
      localCap ⟨22,by decide⟩ := by
  change (BstLean.Part251.auditCell32).covarianceCap < localCap ⟨22,by decide⟩
  norm_num [BstLean.Part251.auditCell32,localCap]

theorem paperComparison23 :
    (BstLean.Part251.rowCellAudit (sourceIndex ⟨23,by decide⟩)).covarianceCap <
      localCap ⟨23,by decide⟩ := by
  change (BstLean.Part251.auditCell33).covarianceCap < localCap ⟨23,by decide⟩
  norm_num [BstLean.Part251.auditCell33,localCap]

theorem paperComparison24 :
    (BstLean.Part251.rowCellAudit (sourceIndex ⟨24,by decide⟩)).covarianceCap <
      localCap ⟨24,by decide⟩ := by
  change (BstLean.Part251.auditCell34).covarianceCap < localCap ⟨24,by decide⟩
  norm_num [BstLean.Part251.auditCell34,localCap]

theorem paperComparison25 :
    (BstLean.Part251.rowCellAudit (sourceIndex ⟨25,by decide⟩)).covarianceCap <
      localCap ⟨25,by decide⟩ := by
  change (BstLean.Part251.auditCell35).covarianceCap < localCap ⟨25,by decide⟩
  norm_num [BstLean.Part251.auditCell35,localCap]

theorem paperComparison26 :
    (BstLean.Part251.rowCellAudit (sourceIndex ⟨26,by decide⟩)).covarianceCap <
      localCap ⟨26,by decide⟩ := by
  change (BstLean.Part251.auditCell36).covarianceCap < localCap ⟨26,by decide⟩
  norm_num [BstLean.Part251.auditCell36,localCap]

theorem paperComparison27 :
    (BstLean.Part251.rowCellAudit (sourceIndex ⟨27,by decide⟩)).covarianceCap <
      localCap ⟨27,by decide⟩ := by
  change (BstLean.Part251.auditCell37).covarianceCap < localCap ⟨27,by decide⟩
  norm_num [BstLean.Part251.auditCell37,localCap]

theorem paperComparison28 :
    (BstLean.Part251.rowCellAudit (sourceIndex ⟨28,by decide⟩)).covarianceCap <
      localCap ⟨28,by decide⟩ := by
  change (BstLean.Part251.auditCell38).covarianceCap < localCap ⟨28,by decide⟩
  norm_num [BstLean.Part251.auditCell38,localCap]

theorem paperComparison29 :
    (BstLean.Part251.rowCellAudit (sourceIndex ⟨29,by decide⟩)).covarianceCap <
      localCap ⟨29,by decide⟩ := by
  change (BstLean.Part251.auditCell39).covarianceCap < localCap ⟨29,by decide⟩
  norm_num [BstLean.Part251.auditCell39,localCap]

theorem paperComparison30 :
    (BstLean.Part251.rowCellAudit (sourceIndex ⟨30,by decide⟩)).covarianceCap <
      localCap ⟨30,by decide⟩ := by
  change (BstLean.Part251.auditCell40).covarianceCap < localCap ⟨30,by decide⟩
  norm_num [BstLean.Part251.auditCell40,localCap]

theorem paperComparison31 :
    (BstLean.Part251.rowCellAudit (sourceIndex ⟨31,by decide⟩)).covarianceCap <
      localCap ⟨31,by decide⟩ := by
  change (BstLean.Part251.auditCell41).covarianceCap < localCap ⟨31,by decide⟩
  norm_num [BstLean.Part251.auditCell41,localCap]

theorem paperComparison32 :
    (BstLean.Part251.rowCellAudit (sourceIndex ⟨32,by decide⟩)).covarianceCap <
      localCap ⟨32,by decide⟩ := by
  change (BstLean.Part251.auditCell42).covarianceCap < localCap ⟨32,by decide⟩
  norm_num [BstLean.Part251.auditCell42,localCap]

theorem paperComparison33 :
    (BstLean.Part251.rowCellAudit (sourceIndex ⟨33,by decide⟩)).covarianceCap <
      localCap ⟨33,by decide⟩ := by
  change (BstLean.Part251.auditCell43).covarianceCap < localCap ⟨33,by decide⟩
  norm_num [BstLean.Part251.auditCell43,localCap]

theorem paperComparison34 :
    (BstLean.Part251.rowCellAudit (sourceIndex ⟨34,by decide⟩)).covarianceCap <
      localCap ⟨34,by decide⟩ := by
  change (BstLean.Part251.auditCell44).covarianceCap < localCap ⟨34,by decide⟩
  norm_num [BstLean.Part251.auditCell44,localCap]

theorem paperComparison35 :
    (BstLean.Part251.rowCellAudit (sourceIndex ⟨35,by decide⟩)).covarianceCap <
      localCap ⟨35,by decide⟩ := by
  change (BstLean.Part251.auditCell45).covarianceCap < localCap ⟨35,by decide⟩
  norm_num [BstLean.Part251.auditCell45,localCap]

theorem paperComparison36 :
    (BstLean.Part251.rowCellAudit (sourceIndex ⟨36,by decide⟩)).covarianceCap <
      localCap ⟨36,by decide⟩ := by
  change (BstLean.Part251.auditCell46).covarianceCap < localCap ⟨36,by decide⟩
  norm_num [BstLean.Part251.auditCell46,localCap]

theorem paperComparison37 :
    (BstLean.Part251.rowCellAudit (sourceIndex ⟨37,by decide⟩)).covarianceCap <
      localCap ⟨37,by decide⟩ := by
  change (BstLean.Part251.auditCell47).covarianceCap < localCap ⟨37,by decide⟩
  norm_num [BstLean.Part251.auditCell47,localCap]

theorem paperComparison38 :
    (BstLean.Part251.rowCellAudit (sourceIndex ⟨38,by decide⟩)).covarianceCap <
      localCap ⟨38,by decide⟩ := by
  change (BstLean.Part251.auditCell48).covarianceCap < localCap ⟨38,by decide⟩
  norm_num [BstLean.Part251.auditCell48,localCap]

theorem paperComparison39 :
    (BstLean.Part251.rowCellAudit (sourceIndex ⟨39,by decide⟩)).covarianceCap <
      localCap ⟨39,by decide⟩ := by
  change (BstLean.Part251.auditCell49).covarianceCap < localCap ⟨39,by decide⟩
  norm_num [BstLean.Part251.auditCell49,localCap]

theorem paperComparison40 :
    (BstLean.Part251.rowCellAudit (sourceIndex ⟨40,by decide⟩)).covarianceCap <
      localCap ⟨40,by decide⟩ := by
  change (BstLean.Part251.auditCell50).covarianceCap < localCap ⟨40,by decide⟩
  norm_num [BstLean.Part251.auditCell50,localCap]

theorem paperComparison41 :
    (BstLean.Part251.rowCellAudit (sourceIndex ⟨41,by decide⟩)).covarianceCap <
      localCap ⟨41,by decide⟩ := by
  change (BstLean.Part251.auditCell51).covarianceCap < localCap ⟨41,by decide⟩
  norm_num [BstLean.Part251.auditCell51,localCap]

theorem paperComparison42 :
    (BstLean.Part251.rowCellAudit (sourceIndex ⟨42,by decide⟩)).covarianceCap ≥
      localCap ⟨42,by decide⟩ := by
  change (BstLean.Part251.auditCell52).covarianceCap ≥ localCap ⟨42,by decide⟩
  norm_num [BstLean.Part251.auditCell52,localCap]

theorem paper_caps_exceeded (j : Fin 43) (hj : j.val < 42) :
    (BstLean.Part251.rowCellAudit (sourceIndex j)).covarianceCap < localCap j := by
  match j with
  | ⟨0,_⟩ => exact paperComparison0
  | ⟨1,_⟩ => exact paperComparison1
  | ⟨2,_⟩ => exact paperComparison2
  | ⟨3,_⟩ => exact paperComparison3
  | ⟨4,_⟩ => exact paperComparison4
  | ⟨5,_⟩ => exact paperComparison5
  | ⟨6,_⟩ => exact paperComparison6
  | ⟨7,_⟩ => exact paperComparison7
  | ⟨8,_⟩ => exact paperComparison8
  | ⟨9,_⟩ => exact paperComparison9
  | ⟨10,_⟩ => exact paperComparison10
  | ⟨11,_⟩ => exact paperComparison11
  | ⟨12,_⟩ => exact paperComparison12
  | ⟨13,_⟩ => exact paperComparison13
  | ⟨14,_⟩ => exact paperComparison14
  | ⟨15,_⟩ => exact paperComparison15
  | ⟨16,_⟩ => exact paperComparison16
  | ⟨17,_⟩ => exact paperComparison17
  | ⟨18,_⟩ => exact paperComparison18
  | ⟨19,_⟩ => exact paperComparison19
  | ⟨20,_⟩ => exact paperComparison20
  | ⟨21,_⟩ => exact paperComparison21
  | ⟨22,_⟩ => exact paperComparison22
  | ⟨23,_⟩ => exact paperComparison23
  | ⟨24,_⟩ => exact paperComparison24
  | ⟨25,_⟩ => exact paperComparison25
  | ⟨26,_⟩ => exact paperComparison26
  | ⟨27,_⟩ => exact paperComparison27
  | ⟨28,_⟩ => exact paperComparison28
  | ⟨29,_⟩ => exact paperComparison29
  | ⟨30,_⟩ => exact paperComparison30
  | ⟨31,_⟩ => exact paperComparison31
  | ⟨32,_⟩ => exact paperComparison32
  | ⟨33,_⟩ => exact paperComparison33
  | ⟨34,_⟩ => exact paperComparison34
  | ⟨35,_⟩ => exact paperComparison35
  | ⟨36,_⟩ => exact paperComparison36
  | ⟨37,_⟩ => exact paperComparison37
  | ⟨38,_⟩ => exact paperComparison38
  | ⟨39,_⟩ => exact paperComparison39
  | ⟨40,_⟩ => exact paperComparison40
  | ⟨41,_⟩ => exact paperComparison41
  | ⟨j+42,h⟩ => exact False.elim (by have hj2 : j+42 < 42 := hj; omega)

theorem paperEnvelopeFailure0 :
    (BstLean.Part251.rowCellAudit (sourceIndex ⟨0,by decide⟩)).covarianceCap <
      envelope (parameters ⟨0,by decide⟩)
        (BstLean.Part254.cellUpper (sourceIndex ⟨0,by decide⟩)) := by
  have h : (BstLean.Part251.rowCellAudit (sourceIndex ⟨0,by decide⟩)).covarianceCap <
      localCap ⟨0,by decide⟩-1/10^9 := by
    change (BstLean.Part251.auditCell10).covarianceCap < localCap ⟨0,by decide⟩-1/10^9
    norm_num [BstLean.Part251.auditCell10,localCap]
  exact h.trans (grid ⟨0,by decide⟩).2.1

theorem paperEnvelopeFailure1 :
    (BstLean.Part251.rowCellAudit (sourceIndex ⟨1,by decide⟩)).covarianceCap <
      envelope (parameters ⟨1,by decide⟩)
        (BstLean.Part254.cellUpper (sourceIndex ⟨1,by decide⟩)) := by
  have h : (BstLean.Part251.rowCellAudit (sourceIndex ⟨1,by decide⟩)).covarianceCap <
      localCap ⟨1,by decide⟩-1/10^9 := by
    change (BstLean.Part251.auditCell11).covarianceCap < localCap ⟨1,by decide⟩-1/10^9
    norm_num [BstLean.Part251.auditCell11,localCap]
  exact h.trans (grid ⟨1,by decide⟩).2.1

theorem paperEnvelopeFailure2 :
    (BstLean.Part251.rowCellAudit (sourceIndex ⟨2,by decide⟩)).covarianceCap <
      envelope (parameters ⟨2,by decide⟩)
        (BstLean.Part254.cellUpper (sourceIndex ⟨2,by decide⟩)) := by
  have h : (BstLean.Part251.rowCellAudit (sourceIndex ⟨2,by decide⟩)).covarianceCap <
      localCap ⟨2,by decide⟩-1/10^9 := by
    change (BstLean.Part251.auditCell12).covarianceCap < localCap ⟨2,by decide⟩-1/10^9
    norm_num [BstLean.Part251.auditCell12,localCap]
  exact h.trans (grid ⟨2,by decide⟩).2.1

theorem paperEnvelopeFailure3 :
    (BstLean.Part251.rowCellAudit (sourceIndex ⟨3,by decide⟩)).covarianceCap <
      envelope (parameters ⟨3,by decide⟩)
        (BstLean.Part254.cellUpper (sourceIndex ⟨3,by decide⟩)) := by
  have h : (BstLean.Part251.rowCellAudit (sourceIndex ⟨3,by decide⟩)).covarianceCap <
      localCap ⟨3,by decide⟩-1/10^9 := by
    change (BstLean.Part251.auditCell13).covarianceCap < localCap ⟨3,by decide⟩-1/10^9
    norm_num [BstLean.Part251.auditCell13,localCap]
  exact h.trans (grid ⟨3,by decide⟩).2.1

theorem paperEnvelopeFailure4 :
    (BstLean.Part251.rowCellAudit (sourceIndex ⟨4,by decide⟩)).covarianceCap <
      envelope (parameters ⟨4,by decide⟩)
        (BstLean.Part254.cellUpper (sourceIndex ⟨4,by decide⟩)) := by
  have h : (BstLean.Part251.rowCellAudit (sourceIndex ⟨4,by decide⟩)).covarianceCap <
      localCap ⟨4,by decide⟩-1/10^9 := by
    change (BstLean.Part251.auditCell14).covarianceCap < localCap ⟨4,by decide⟩-1/10^9
    norm_num [BstLean.Part251.auditCell14,localCap]
  exact h.trans (grid ⟨4,by decide⟩).2.1

theorem paperEnvelopeFailure5 :
    (BstLean.Part251.rowCellAudit (sourceIndex ⟨5,by decide⟩)).covarianceCap <
      envelope (parameters ⟨5,by decide⟩)
        (BstLean.Part254.cellUpper (sourceIndex ⟨5,by decide⟩)) := by
  have h : (BstLean.Part251.rowCellAudit (sourceIndex ⟨5,by decide⟩)).covarianceCap <
      localCap ⟨5,by decide⟩-1/10^9 := by
    change (BstLean.Part251.auditCell15).covarianceCap < localCap ⟨5,by decide⟩-1/10^9
    norm_num [BstLean.Part251.auditCell15,localCap]
  exact h.trans (grid ⟨5,by decide⟩).2.1

theorem paperEnvelopeFailure6 :
    (BstLean.Part251.rowCellAudit (sourceIndex ⟨6,by decide⟩)).covarianceCap <
      envelope (parameters ⟨6,by decide⟩)
        (BstLean.Part254.cellUpper (sourceIndex ⟨6,by decide⟩)) := by
  have h : (BstLean.Part251.rowCellAudit (sourceIndex ⟨6,by decide⟩)).covarianceCap <
      localCap ⟨6,by decide⟩-1/10^9 := by
    change (BstLean.Part251.auditCell16).covarianceCap < localCap ⟨6,by decide⟩-1/10^9
    norm_num [BstLean.Part251.auditCell16,localCap]
  exact h.trans (grid ⟨6,by decide⟩).2.1

theorem paperEnvelopeFailure7 :
    (BstLean.Part251.rowCellAudit (sourceIndex ⟨7,by decide⟩)).covarianceCap <
      envelope (parameters ⟨7,by decide⟩)
        (BstLean.Part254.cellUpper (sourceIndex ⟨7,by decide⟩)) := by
  have h : (BstLean.Part251.rowCellAudit (sourceIndex ⟨7,by decide⟩)).covarianceCap <
      localCap ⟨7,by decide⟩-1/10^9 := by
    change (BstLean.Part251.auditCell17).covarianceCap < localCap ⟨7,by decide⟩-1/10^9
    norm_num [BstLean.Part251.auditCell17,localCap]
  exact h.trans (grid ⟨7,by decide⟩).2.1

theorem paperEnvelopeFailure8 :
    (BstLean.Part251.rowCellAudit (sourceIndex ⟨8,by decide⟩)).covarianceCap <
      envelope (parameters ⟨8,by decide⟩)
        (BstLean.Part254.cellUpper (sourceIndex ⟨8,by decide⟩)) := by
  have h : (BstLean.Part251.rowCellAudit (sourceIndex ⟨8,by decide⟩)).covarianceCap <
      localCap ⟨8,by decide⟩-1/10^9 := by
    change (BstLean.Part251.auditCell18).covarianceCap < localCap ⟨8,by decide⟩-1/10^9
    norm_num [BstLean.Part251.auditCell18,localCap]
  exact h.trans (grid ⟨8,by decide⟩).2.1

theorem paperEnvelopeFailure9 :
    (BstLean.Part251.rowCellAudit (sourceIndex ⟨9,by decide⟩)).covarianceCap <
      envelope (parameters ⟨9,by decide⟩)
        (BstLean.Part254.cellUpper (sourceIndex ⟨9,by decide⟩)) := by
  have h : (BstLean.Part251.rowCellAudit (sourceIndex ⟨9,by decide⟩)).covarianceCap <
      localCap ⟨9,by decide⟩-1/10^9 := by
    change (BstLean.Part251.auditCell19).covarianceCap < localCap ⟨9,by decide⟩-1/10^9
    norm_num [BstLean.Part251.auditCell19,localCap]
  exact h.trans (grid ⟨9,by decide⟩).2.1

theorem paperEnvelopeFailure10 :
    (BstLean.Part251.rowCellAudit (sourceIndex ⟨10,by decide⟩)).covarianceCap <
      envelope (parameters ⟨10,by decide⟩)
        (BstLean.Part254.cellUpper (sourceIndex ⟨10,by decide⟩)) := by
  have h : (BstLean.Part251.rowCellAudit (sourceIndex ⟨10,by decide⟩)).covarianceCap <
      localCap ⟨10,by decide⟩-1/10^9 := by
    change (BstLean.Part251.auditCell20).covarianceCap < localCap ⟨10,by decide⟩-1/10^9
    norm_num [BstLean.Part251.auditCell20,localCap]
  exact h.trans (grid ⟨10,by decide⟩).2.1

theorem paperEnvelopeFailure11 :
    (BstLean.Part251.rowCellAudit (sourceIndex ⟨11,by decide⟩)).covarianceCap <
      envelope (parameters ⟨11,by decide⟩)
        (BstLean.Part254.cellUpper (sourceIndex ⟨11,by decide⟩)) := by
  have h : (BstLean.Part251.rowCellAudit (sourceIndex ⟨11,by decide⟩)).covarianceCap <
      localCap ⟨11,by decide⟩-1/10^9 := by
    change (BstLean.Part251.auditCell21).covarianceCap < localCap ⟨11,by decide⟩-1/10^9
    norm_num [BstLean.Part251.auditCell21,localCap]
  exact h.trans (grid ⟨11,by decide⟩).2.1

theorem paperEnvelopeFailure12 :
    (BstLean.Part251.rowCellAudit (sourceIndex ⟨12,by decide⟩)).covarianceCap <
      envelope (parameters ⟨12,by decide⟩)
        (BstLean.Part254.cellUpper (sourceIndex ⟨12,by decide⟩)) := by
  have h : (BstLean.Part251.rowCellAudit (sourceIndex ⟨12,by decide⟩)).covarianceCap <
      localCap ⟨12,by decide⟩-1/10^9 := by
    change (BstLean.Part251.auditCell22).covarianceCap < localCap ⟨12,by decide⟩-1/10^9
    norm_num [BstLean.Part251.auditCell22,localCap]
  exact h.trans (grid ⟨12,by decide⟩).2.1

theorem paperEnvelopeFailure13 :
    (BstLean.Part251.rowCellAudit (sourceIndex ⟨13,by decide⟩)).covarianceCap <
      envelope (parameters ⟨13,by decide⟩)
        (BstLean.Part254.cellUpper (sourceIndex ⟨13,by decide⟩)) := by
  have h : (BstLean.Part251.rowCellAudit (sourceIndex ⟨13,by decide⟩)).covarianceCap <
      localCap ⟨13,by decide⟩-1/10^9 := by
    change (BstLean.Part251.auditCell23).covarianceCap < localCap ⟨13,by decide⟩-1/10^9
    norm_num [BstLean.Part251.auditCell23,localCap]
  exact h.trans (grid ⟨13,by decide⟩).2.1

theorem paperEnvelopeFailure14 :
    (BstLean.Part251.rowCellAudit (sourceIndex ⟨14,by decide⟩)).covarianceCap <
      envelope (parameters ⟨14,by decide⟩)
        (BstLean.Part254.cellUpper (sourceIndex ⟨14,by decide⟩)) := by
  have h : (BstLean.Part251.rowCellAudit (sourceIndex ⟨14,by decide⟩)).covarianceCap <
      localCap ⟨14,by decide⟩-1/10^9 := by
    change (BstLean.Part251.auditCell24).covarianceCap < localCap ⟨14,by decide⟩-1/10^9
    norm_num [BstLean.Part251.auditCell24,localCap]
  exact h.trans (grid ⟨14,by decide⟩).2.1

theorem paperEnvelopeFailure15 :
    (BstLean.Part251.rowCellAudit (sourceIndex ⟨15,by decide⟩)).covarianceCap <
      envelope (parameters ⟨15,by decide⟩)
        (BstLean.Part254.cellUpper (sourceIndex ⟨15,by decide⟩)) := by
  have h : (BstLean.Part251.rowCellAudit (sourceIndex ⟨15,by decide⟩)).covarianceCap <
      localCap ⟨15,by decide⟩-1/10^9 := by
    change (BstLean.Part251.auditCell25).covarianceCap < localCap ⟨15,by decide⟩-1/10^9
    norm_num [BstLean.Part251.auditCell25,localCap]
  exact h.trans (grid ⟨15,by decide⟩).2.1

theorem paperEnvelopeFailure16 :
    (BstLean.Part251.rowCellAudit (sourceIndex ⟨16,by decide⟩)).covarianceCap <
      envelope (parameters ⟨16,by decide⟩)
        (BstLean.Part254.cellUpper (sourceIndex ⟨16,by decide⟩)) := by
  have h : (BstLean.Part251.rowCellAudit (sourceIndex ⟨16,by decide⟩)).covarianceCap <
      localCap ⟨16,by decide⟩-1/10^9 := by
    change (BstLean.Part251.auditCell26).covarianceCap < localCap ⟨16,by decide⟩-1/10^9
    norm_num [BstLean.Part251.auditCell26,localCap]
  exact h.trans (grid ⟨16,by decide⟩).2.1

theorem paperEnvelopeFailure17 :
    (BstLean.Part251.rowCellAudit (sourceIndex ⟨17,by decide⟩)).covarianceCap <
      envelope (parameters ⟨17,by decide⟩)
        (BstLean.Part254.cellUpper (sourceIndex ⟨17,by decide⟩)) := by
  have h : (BstLean.Part251.rowCellAudit (sourceIndex ⟨17,by decide⟩)).covarianceCap <
      localCap ⟨17,by decide⟩-1/10^9 := by
    change (BstLean.Part251.auditCell27).covarianceCap < localCap ⟨17,by decide⟩-1/10^9
    norm_num [BstLean.Part251.auditCell27,localCap]
  exact h.trans (grid ⟨17,by decide⟩).2.1

theorem paperEnvelopeFailure18 :
    (BstLean.Part251.rowCellAudit (sourceIndex ⟨18,by decide⟩)).covarianceCap <
      envelope (parameters ⟨18,by decide⟩)
        (BstLean.Part254.cellUpper (sourceIndex ⟨18,by decide⟩)) := by
  have h : (BstLean.Part251.rowCellAudit (sourceIndex ⟨18,by decide⟩)).covarianceCap <
      localCap ⟨18,by decide⟩-1/10^9 := by
    change (BstLean.Part251.auditCell28).covarianceCap < localCap ⟨18,by decide⟩-1/10^9
    norm_num [BstLean.Part251.auditCell28,localCap]
  exact h.trans (grid ⟨18,by decide⟩).2.1

theorem paperEnvelopeFailure19 :
    (BstLean.Part251.rowCellAudit (sourceIndex ⟨19,by decide⟩)).covarianceCap <
      envelope (parameters ⟨19,by decide⟩)
        (BstLean.Part254.cellUpper (sourceIndex ⟨19,by decide⟩)) := by
  have h : (BstLean.Part251.rowCellAudit (sourceIndex ⟨19,by decide⟩)).covarianceCap <
      localCap ⟨19,by decide⟩-1/10^9 := by
    change (BstLean.Part251.auditCell29).covarianceCap < localCap ⟨19,by decide⟩-1/10^9
    norm_num [BstLean.Part251.auditCell29,localCap]
  exact h.trans (grid ⟨19,by decide⟩).2.1

theorem paperEnvelopeFailure20 :
    (BstLean.Part251.rowCellAudit (sourceIndex ⟨20,by decide⟩)).covarianceCap <
      envelope (parameters ⟨20,by decide⟩)
        (BstLean.Part254.cellUpper (sourceIndex ⟨20,by decide⟩)) := by
  have h : (BstLean.Part251.rowCellAudit (sourceIndex ⟨20,by decide⟩)).covarianceCap <
      localCap ⟨20,by decide⟩-1/10^9 := by
    change (BstLean.Part251.auditCell30).covarianceCap < localCap ⟨20,by decide⟩-1/10^9
    norm_num [BstLean.Part251.auditCell30,localCap]
  exact h.trans (grid ⟨20,by decide⟩).2.1

theorem paperEnvelopeFailure21 :
    (BstLean.Part251.rowCellAudit (sourceIndex ⟨21,by decide⟩)).covarianceCap <
      envelope (parameters ⟨21,by decide⟩)
        (BstLean.Part254.cellUpper (sourceIndex ⟨21,by decide⟩)) := by
  have h : (BstLean.Part251.rowCellAudit (sourceIndex ⟨21,by decide⟩)).covarianceCap <
      localCap ⟨21,by decide⟩-1/10^9 := by
    change (BstLean.Part251.auditCell31).covarianceCap < localCap ⟨21,by decide⟩-1/10^9
    norm_num [BstLean.Part251.auditCell31,localCap]
  exact h.trans (grid ⟨21,by decide⟩).2.1

theorem paperEnvelopeFailure22 :
    (BstLean.Part251.rowCellAudit (sourceIndex ⟨22,by decide⟩)).covarianceCap <
      envelope (parameters ⟨22,by decide⟩)
        (BstLean.Part254.cellUpper (sourceIndex ⟨22,by decide⟩)) := by
  have h : (BstLean.Part251.rowCellAudit (sourceIndex ⟨22,by decide⟩)).covarianceCap <
      localCap ⟨22,by decide⟩-1/10^9 := by
    change (BstLean.Part251.auditCell32).covarianceCap < localCap ⟨22,by decide⟩-1/10^9
    norm_num [BstLean.Part251.auditCell32,localCap]
  exact h.trans (grid ⟨22,by decide⟩).2.1

theorem paperEnvelopeFailure23 :
    (BstLean.Part251.rowCellAudit (sourceIndex ⟨23,by decide⟩)).covarianceCap <
      envelope (parameters ⟨23,by decide⟩)
        (BstLean.Part254.cellUpper (sourceIndex ⟨23,by decide⟩)) := by
  have h : (BstLean.Part251.rowCellAudit (sourceIndex ⟨23,by decide⟩)).covarianceCap <
      localCap ⟨23,by decide⟩-1/10^9 := by
    change (BstLean.Part251.auditCell33).covarianceCap < localCap ⟨23,by decide⟩-1/10^9
    norm_num [BstLean.Part251.auditCell33,localCap]
  exact h.trans (grid ⟨23,by decide⟩).2.1

theorem paperEnvelopeFailure24 :
    (BstLean.Part251.rowCellAudit (sourceIndex ⟨24,by decide⟩)).covarianceCap <
      envelope (parameters ⟨24,by decide⟩)
        (BstLean.Part254.cellUpper (sourceIndex ⟨24,by decide⟩)) := by
  have h : (BstLean.Part251.rowCellAudit (sourceIndex ⟨24,by decide⟩)).covarianceCap <
      localCap ⟨24,by decide⟩-1/10^9 := by
    change (BstLean.Part251.auditCell34).covarianceCap < localCap ⟨24,by decide⟩-1/10^9
    norm_num [BstLean.Part251.auditCell34,localCap]
  exact h.trans (grid ⟨24,by decide⟩).2.1

theorem paperEnvelopeFailure25 :
    (BstLean.Part251.rowCellAudit (sourceIndex ⟨25,by decide⟩)).covarianceCap <
      envelope (parameters ⟨25,by decide⟩)
        (BstLean.Part254.cellUpper (sourceIndex ⟨25,by decide⟩)) := by
  have h : (BstLean.Part251.rowCellAudit (sourceIndex ⟨25,by decide⟩)).covarianceCap <
      localCap ⟨25,by decide⟩-1/10^9 := by
    change (BstLean.Part251.auditCell35).covarianceCap < localCap ⟨25,by decide⟩-1/10^9
    norm_num [BstLean.Part251.auditCell35,localCap]
  exact h.trans (grid ⟨25,by decide⟩).2.1

theorem paperEnvelopeFailure26 :
    (BstLean.Part251.rowCellAudit (sourceIndex ⟨26,by decide⟩)).covarianceCap <
      envelope (parameters ⟨26,by decide⟩)
        (BstLean.Part254.cellUpper (sourceIndex ⟨26,by decide⟩)) := by
  have h : (BstLean.Part251.rowCellAudit (sourceIndex ⟨26,by decide⟩)).covarianceCap <
      localCap ⟨26,by decide⟩-1/10^9 := by
    change (BstLean.Part251.auditCell36).covarianceCap < localCap ⟨26,by decide⟩-1/10^9
    norm_num [BstLean.Part251.auditCell36,localCap]
  exact h.trans (grid ⟨26,by decide⟩).2.1

theorem paperEnvelopeFailure27 :
    (BstLean.Part251.rowCellAudit (sourceIndex ⟨27,by decide⟩)).covarianceCap <
      envelope (parameters ⟨27,by decide⟩)
        (BstLean.Part254.cellUpper (sourceIndex ⟨27,by decide⟩)) := by
  have h : (BstLean.Part251.rowCellAudit (sourceIndex ⟨27,by decide⟩)).covarianceCap <
      localCap ⟨27,by decide⟩-1/10^9 := by
    change (BstLean.Part251.auditCell37).covarianceCap < localCap ⟨27,by decide⟩-1/10^9
    norm_num [BstLean.Part251.auditCell37,localCap]
  exact h.trans (grid ⟨27,by decide⟩).2.1

theorem paperEnvelopeFailure28 :
    (BstLean.Part251.rowCellAudit (sourceIndex ⟨28,by decide⟩)).covarianceCap <
      envelope (parameters ⟨28,by decide⟩)
        (BstLean.Part254.cellUpper (sourceIndex ⟨28,by decide⟩)) := by
  have h : (BstLean.Part251.rowCellAudit (sourceIndex ⟨28,by decide⟩)).covarianceCap <
      localCap ⟨28,by decide⟩-1/10^9 := by
    change (BstLean.Part251.auditCell38).covarianceCap < localCap ⟨28,by decide⟩-1/10^9
    norm_num [BstLean.Part251.auditCell38,localCap]
  exact h.trans (grid ⟨28,by decide⟩).2.1

theorem paperEnvelopeFailure29 :
    (BstLean.Part251.rowCellAudit (sourceIndex ⟨29,by decide⟩)).covarianceCap <
      envelope (parameters ⟨29,by decide⟩)
        (BstLean.Part254.cellUpper (sourceIndex ⟨29,by decide⟩)) := by
  have h : (BstLean.Part251.rowCellAudit (sourceIndex ⟨29,by decide⟩)).covarianceCap <
      localCap ⟨29,by decide⟩-1/10^9 := by
    change (BstLean.Part251.auditCell39).covarianceCap < localCap ⟨29,by decide⟩-1/10^9
    norm_num [BstLean.Part251.auditCell39,localCap]
  exact h.trans (grid ⟨29,by decide⟩).2.1

theorem paperEnvelopeFailure30 :
    (BstLean.Part251.rowCellAudit (sourceIndex ⟨30,by decide⟩)).covarianceCap <
      envelope (parameters ⟨30,by decide⟩)
        (BstLean.Part254.cellUpper (sourceIndex ⟨30,by decide⟩)) := by
  have h : (BstLean.Part251.rowCellAudit (sourceIndex ⟨30,by decide⟩)).covarianceCap <
      localCap ⟨30,by decide⟩-1/10^9 := by
    change (BstLean.Part251.auditCell40).covarianceCap < localCap ⟨30,by decide⟩-1/10^9
    norm_num [BstLean.Part251.auditCell40,localCap]
  exact h.trans (grid ⟨30,by decide⟩).2.1

theorem paperEnvelopeFailure31 :
    (BstLean.Part251.rowCellAudit (sourceIndex ⟨31,by decide⟩)).covarianceCap <
      envelope (parameters ⟨31,by decide⟩)
        (BstLean.Part254.cellUpper (sourceIndex ⟨31,by decide⟩)) := by
  have h : (BstLean.Part251.rowCellAudit (sourceIndex ⟨31,by decide⟩)).covarianceCap <
      localCap ⟨31,by decide⟩-1/10^9 := by
    change (BstLean.Part251.auditCell41).covarianceCap < localCap ⟨31,by decide⟩-1/10^9
    norm_num [BstLean.Part251.auditCell41,localCap]
  exact h.trans (grid ⟨31,by decide⟩).2.1

theorem paperEnvelopeFailure32 :
    (BstLean.Part251.rowCellAudit (sourceIndex ⟨32,by decide⟩)).covarianceCap <
      envelope (parameters ⟨32,by decide⟩)
        (BstLean.Part254.cellUpper (sourceIndex ⟨32,by decide⟩)) := by
  have h : (BstLean.Part251.rowCellAudit (sourceIndex ⟨32,by decide⟩)).covarianceCap <
      localCap ⟨32,by decide⟩-1/10^9 := by
    change (BstLean.Part251.auditCell42).covarianceCap < localCap ⟨32,by decide⟩-1/10^9
    norm_num [BstLean.Part251.auditCell42,localCap]
  exact h.trans (grid ⟨32,by decide⟩).2.1

theorem paperEnvelopeFailure33 :
    (BstLean.Part251.rowCellAudit (sourceIndex ⟨33,by decide⟩)).covarianceCap <
      envelope (parameters ⟨33,by decide⟩)
        (BstLean.Part254.cellUpper (sourceIndex ⟨33,by decide⟩)) := by
  have h : (BstLean.Part251.rowCellAudit (sourceIndex ⟨33,by decide⟩)).covarianceCap <
      localCap ⟨33,by decide⟩-1/10^9 := by
    change (BstLean.Part251.auditCell43).covarianceCap < localCap ⟨33,by decide⟩-1/10^9
    norm_num [BstLean.Part251.auditCell43,localCap]
  exact h.trans (grid ⟨33,by decide⟩).2.1

theorem paperEnvelopeFailure34 :
    (BstLean.Part251.rowCellAudit (sourceIndex ⟨34,by decide⟩)).covarianceCap <
      envelope (parameters ⟨34,by decide⟩)
        (BstLean.Part254.cellUpper (sourceIndex ⟨34,by decide⟩)) := by
  have h : (BstLean.Part251.rowCellAudit (sourceIndex ⟨34,by decide⟩)).covarianceCap <
      localCap ⟨34,by decide⟩-1/10^9 := by
    change (BstLean.Part251.auditCell44).covarianceCap < localCap ⟨34,by decide⟩-1/10^9
    norm_num [BstLean.Part251.auditCell44,localCap]
  exact h.trans (grid ⟨34,by decide⟩).2.1

theorem paperEnvelopeFailure35 :
    (BstLean.Part251.rowCellAudit (sourceIndex ⟨35,by decide⟩)).covarianceCap <
      envelope (parameters ⟨35,by decide⟩)
        (BstLean.Part254.cellUpper (sourceIndex ⟨35,by decide⟩)) := by
  have h : (BstLean.Part251.rowCellAudit (sourceIndex ⟨35,by decide⟩)).covarianceCap <
      localCap ⟨35,by decide⟩-1/10^9 := by
    change (BstLean.Part251.auditCell45).covarianceCap < localCap ⟨35,by decide⟩-1/10^9
    norm_num [BstLean.Part251.auditCell45,localCap]
  exact h.trans (grid ⟨35,by decide⟩).2.1

theorem paperEnvelopeFailure36 :
    (BstLean.Part251.rowCellAudit (sourceIndex ⟨36,by decide⟩)).covarianceCap <
      envelope (parameters ⟨36,by decide⟩)
        (BstLean.Part254.cellUpper (sourceIndex ⟨36,by decide⟩)) := by
  have h : (BstLean.Part251.rowCellAudit (sourceIndex ⟨36,by decide⟩)).covarianceCap <
      localCap ⟨36,by decide⟩-1/10^9 := by
    change (BstLean.Part251.auditCell46).covarianceCap < localCap ⟨36,by decide⟩-1/10^9
    norm_num [BstLean.Part251.auditCell46,localCap]
  exact h.trans (grid ⟨36,by decide⟩).2.1

theorem paperEnvelopeFailure37 :
    (BstLean.Part251.rowCellAudit (sourceIndex ⟨37,by decide⟩)).covarianceCap <
      envelope (parameters ⟨37,by decide⟩)
        (BstLean.Part254.cellUpper (sourceIndex ⟨37,by decide⟩)) := by
  have h : (BstLean.Part251.rowCellAudit (sourceIndex ⟨37,by decide⟩)).covarianceCap <
      localCap ⟨37,by decide⟩-1/10^9 := by
    change (BstLean.Part251.auditCell47).covarianceCap < localCap ⟨37,by decide⟩-1/10^9
    norm_num [BstLean.Part251.auditCell47,localCap]
  exact h.trans (grid ⟨37,by decide⟩).2.1

theorem paperEnvelopeFailure38 :
    (BstLean.Part251.rowCellAudit (sourceIndex ⟨38,by decide⟩)).covarianceCap <
      envelope (parameters ⟨38,by decide⟩)
        (BstLean.Part254.cellUpper (sourceIndex ⟨38,by decide⟩)) := by
  have h : (BstLean.Part251.rowCellAudit (sourceIndex ⟨38,by decide⟩)).covarianceCap <
      localCap ⟨38,by decide⟩-1/10^9 := by
    change (BstLean.Part251.auditCell48).covarianceCap < localCap ⟨38,by decide⟩-1/10^9
    norm_num [BstLean.Part251.auditCell48,localCap]
  exact h.trans (grid ⟨38,by decide⟩).2.1

theorem paperEnvelopeFailure39 :
    (BstLean.Part251.rowCellAudit (sourceIndex ⟨39,by decide⟩)).covarianceCap <
      envelope (parameters ⟨39,by decide⟩)
        (BstLean.Part254.cellUpper (sourceIndex ⟨39,by decide⟩)) := by
  have h : (BstLean.Part251.rowCellAudit (sourceIndex ⟨39,by decide⟩)).covarianceCap <
      localCap ⟨39,by decide⟩-1/10^9 := by
    change (BstLean.Part251.auditCell49).covarianceCap < localCap ⟨39,by decide⟩-1/10^9
    norm_num [BstLean.Part251.auditCell49,localCap]
  exact h.trans (grid ⟨39,by decide⟩).2.1

theorem paperEnvelopeFailure40 :
    (BstLean.Part251.rowCellAudit (sourceIndex ⟨40,by decide⟩)).covarianceCap <
      envelope (parameters ⟨40,by decide⟩)
        (BstLean.Part254.cellUpper (sourceIndex ⟨40,by decide⟩)) := by
  have h : (BstLean.Part251.rowCellAudit (sourceIndex ⟨40,by decide⟩)).covarianceCap <
      localCap ⟨40,by decide⟩-1/10^9 := by
    change (BstLean.Part251.auditCell50).covarianceCap < localCap ⟨40,by decide⟩-1/10^9
    norm_num [BstLean.Part251.auditCell50,localCap]
  exact h.trans (grid ⟨40,by decide⟩).2.1

theorem paperEnvelopeFailure41 :
    (BstLean.Part251.rowCellAudit (sourceIndex ⟨41,by decide⟩)).covarianceCap <
      envelope (parameters ⟨41,by decide⟩)
        (BstLean.Part254.cellUpper (sourceIndex ⟨41,by decide⟩)) := by
  have h : (BstLean.Part251.rowCellAudit (sourceIndex ⟨41,by decide⟩)).covarianceCap <
      localCap ⟨41,by decide⟩-1/10^9 := by
    change (BstLean.Part251.auditCell51).covarianceCap < localCap ⟨41,by decide⟩-1/10^9
    norm_num [BstLean.Part251.auditCell51,localCap]
  exact h.trans (grid ⟨41,by decide⟩).2.1

theorem paper_envelope_failure (j : Fin 43) (hj : j.val < 42) :
    (BstLean.Part251.rowCellAudit (sourceIndex j)).covarianceCap <
      envelope (parameters j) (BstLean.Part254.cellUpper (sourceIndex j)) := by
  match j with
  | ⟨0,_⟩ => exact paperEnvelopeFailure0
  | ⟨1,_⟩ => exact paperEnvelopeFailure1
  | ⟨2,_⟩ => exact paperEnvelopeFailure2
  | ⟨3,_⟩ => exact paperEnvelopeFailure3
  | ⟨4,_⟩ => exact paperEnvelopeFailure4
  | ⟨5,_⟩ => exact paperEnvelopeFailure5
  | ⟨6,_⟩ => exact paperEnvelopeFailure6
  | ⟨7,_⟩ => exact paperEnvelopeFailure7
  | ⟨8,_⟩ => exact paperEnvelopeFailure8
  | ⟨9,_⟩ => exact paperEnvelopeFailure9
  | ⟨10,_⟩ => exact paperEnvelopeFailure10
  | ⟨11,_⟩ => exact paperEnvelopeFailure11
  | ⟨12,_⟩ => exact paperEnvelopeFailure12
  | ⟨13,_⟩ => exact paperEnvelopeFailure13
  | ⟨14,_⟩ => exact paperEnvelopeFailure14
  | ⟨15,_⟩ => exact paperEnvelopeFailure15
  | ⟨16,_⟩ => exact paperEnvelopeFailure16
  | ⟨17,_⟩ => exact paperEnvelopeFailure17
  | ⟨18,_⟩ => exact paperEnvelopeFailure18
  | ⟨19,_⟩ => exact paperEnvelopeFailure19
  | ⟨20,_⟩ => exact paperEnvelopeFailure20
  | ⟨21,_⟩ => exact paperEnvelopeFailure21
  | ⟨22,_⟩ => exact paperEnvelopeFailure22
  | ⟨23,_⟩ => exact paperEnvelopeFailure23
  | ⟨24,_⟩ => exact paperEnvelopeFailure24
  | ⟨25,_⟩ => exact paperEnvelopeFailure25
  | ⟨26,_⟩ => exact paperEnvelopeFailure26
  | ⟨27,_⟩ => exact paperEnvelopeFailure27
  | ⟨28,_⟩ => exact paperEnvelopeFailure28
  | ⟨29,_⟩ => exact paperEnvelopeFailure29
  | ⟨30,_⟩ => exact paperEnvelopeFailure30
  | ⟨31,_⟩ => exact paperEnvelopeFailure31
  | ⟨32,_⟩ => exact paperEnvelopeFailure32
  | ⟨33,_⟩ => exact paperEnvelopeFailure33
  | ⟨34,_⟩ => exact paperEnvelopeFailure34
  | ⟨35,_⟩ => exact paperEnvelopeFailure35
  | ⟨36,_⟩ => exact paperEnvelopeFailure36
  | ⟨37,_⟩ => exact paperEnvelopeFailure37
  | ⟨38,_⟩ => exact paperEnvelopeFailure38
  | ⟨39,_⟩ => exact paperEnvelopeFailure39
  | ⟨40,_⟩ => exact paperEnvelopeFailure40
  | ⟨41,_⟩ => exact paperEnvelopeFailure41
  | ⟨j+42,h⟩ => exact False.elim (by have hj2 : j+42 < 42 := hj; omega)

theorem paper_cap_last : localCap ⟨42,by decide⟩ ≤
    (BstLean.Part251.rowCellAudit (sourceIndex ⟨42,by decide⟩)).covarianceCap :=
  paperComparison42

end BstLean.Part255
