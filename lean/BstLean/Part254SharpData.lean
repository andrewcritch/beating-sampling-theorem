import BstLean.Part254GaussianEnclosure

/-! Rational caps for the Gaussian Option B envelope; these exceed the paper caps. -/
namespace BstLean.Part254
open Real BstLean.Part251

theorem gaussianGrid10 : SharpGridCertificate ⟨10, by decide⟩ (286736645 / 10 ^ 9 : ℝ) := by
  constructor <;>
    norm_num [gaussianEnvelope, radiusEnvelope, cellUpper, worldUpper,
      noiseNode, proposedThetaUpper, min_def, rowCellAudit, auditCell10]

theorem gaussianGrid11 : SharpGridCertificate ⟨11, by decide⟩ (287461677 / 10 ^ 9 : ℝ) := by
  constructor <;>
    norm_num [gaussianEnvelope, radiusEnvelope, cellUpper, worldUpper,
      noiseNode, proposedThetaUpper, min_def, rowCellAudit, auditCell11]

theorem gaussianGrid12 : SharpGridCertificate ⟨12, by decide⟩ (288186711 / 10 ^ 9 : ℝ) := by
  constructor <;>
    norm_num [gaussianEnvelope, radiusEnvelope, cellUpper, worldUpper,
      noiseNode, proposedThetaUpper, min_def, rowCellAudit, auditCell12]

theorem gaussianGrid13 : SharpGridCertificate ⟨13, by decide⟩ (288911746 / 10 ^ 9 : ℝ) := by
  constructor <;>
    norm_num [gaussianEnvelope, radiusEnvelope, cellUpper, worldUpper,
      noiseNode, proposedThetaUpper, min_def, rowCellAudit, auditCell13]

theorem gaussianGrid14 : SharpGridCertificate ⟨14, by decide⟩ (289636784 / 10 ^ 9 : ℝ) := by
  constructor <;>
    norm_num [gaussianEnvelope, radiusEnvelope, cellUpper, worldUpper,
      noiseNode, proposedThetaUpper, min_def, rowCellAudit, auditCell14]

theorem gaussianGrid15 : SharpGridCertificate ⟨15, by decide⟩ (290361824 / 10 ^ 9 : ℝ) := by
  constructor <;>
    norm_num [gaussianEnvelope, radiusEnvelope, cellUpper, worldUpper,
      noiseNode, proposedThetaUpper, min_def, rowCellAudit, auditCell15]

theorem gaussianGrid16 : SharpGridCertificate ⟨16, by decide⟩ (291086866 / 10 ^ 9 : ℝ) := by
  constructor <;>
    norm_num [gaussianEnvelope, radiusEnvelope, cellUpper, worldUpper,
      noiseNode, proposedThetaUpper, min_def, rowCellAudit, auditCell16]

theorem gaussianGrid17 : SharpGridCertificate ⟨17, by decide⟩ (291811910 / 10 ^ 9 : ℝ) := by
  constructor <;>
    norm_num [gaussianEnvelope, radiusEnvelope, cellUpper, worldUpper,
      noiseNode, proposedThetaUpper, min_def, rowCellAudit, auditCell17]

theorem gaussianGrid18 : SharpGridCertificate ⟨18, by decide⟩ (292536955 / 10 ^ 9 : ℝ) := by
  constructor <;>
    norm_num [gaussianEnvelope, radiusEnvelope, cellUpper, worldUpper,
      noiseNode, proposedThetaUpper, min_def, rowCellAudit, auditCell18]

theorem gaussianGrid19 : SharpGridCertificate ⟨19, by decide⟩ (293262003 / 10 ^ 9 : ℝ) := by
  constructor <;>
    norm_num [gaussianEnvelope, radiusEnvelope, cellUpper, worldUpper,
      noiseNode, proposedThetaUpper, min_def, rowCellAudit, auditCell19]

theorem gaussianGrid20 : SharpGridCertificate ⟨20, by decide⟩ (293987052 / 10 ^ 9 : ℝ) := by
  constructor <;>
    norm_num [gaussianEnvelope, radiusEnvelope, cellUpper, worldUpper,
      noiseNode, proposedThetaUpper, min_def, rowCellAudit, auditCell20]

theorem gaussianGrid21 : SharpGridCertificate ⟨21, by decide⟩ (294712104 / 10 ^ 9 : ℝ) := by
  constructor <;>
    norm_num [gaussianEnvelope, radiusEnvelope, cellUpper, worldUpper,
      noiseNode, proposedThetaUpper, min_def, rowCellAudit, auditCell21]

theorem gaussianGrid22 : SharpGridCertificate ⟨22, by decide⟩ (295437157 / 10 ^ 9 : ℝ) := by
  constructor <;>
    norm_num [gaussianEnvelope, radiusEnvelope, cellUpper, worldUpper,
      noiseNode, proposedThetaUpper, min_def, rowCellAudit, auditCell22]

theorem gaussianGrid23 : SharpGridCertificate ⟨23, by decide⟩ (296162212 / 10 ^ 9 : ℝ) := by
  constructor <;>
    norm_num [gaussianEnvelope, radiusEnvelope, cellUpper, worldUpper,
      noiseNode, proposedThetaUpper, min_def, rowCellAudit, auditCell23]

theorem gaussianGrid24 : SharpGridCertificate ⟨24, by decide⟩ (296887270 / 10 ^ 9 : ℝ) := by
  constructor <;>
    norm_num [gaussianEnvelope, radiusEnvelope, cellUpper, worldUpper,
      noiseNode, proposedThetaUpper, min_def, rowCellAudit, auditCell24]

theorem gaussianGrid25 : SharpGridCertificate ⟨25, by decide⟩ (297612329 / 10 ^ 9 : ℝ) := by
  constructor <;>
    norm_num [gaussianEnvelope, radiusEnvelope, cellUpper, worldUpper,
      noiseNode, proposedThetaUpper, min_def, rowCellAudit, auditCell25]

theorem gaussianGrid26 : SharpGridCertificate ⟨26, by decide⟩ (298337390 / 10 ^ 9 : ℝ) := by
  constructor <;>
    norm_num [gaussianEnvelope, radiusEnvelope, cellUpper, worldUpper,
      noiseNode, proposedThetaUpper, min_def, rowCellAudit, auditCell26]

theorem gaussianGrid27 : SharpGridCertificate ⟨27, by decide⟩ (299062453 / 10 ^ 9 : ℝ) := by
  constructor <;>
    norm_num [gaussianEnvelope, radiusEnvelope, cellUpper, worldUpper,
      noiseNode, proposedThetaUpper, min_def, rowCellAudit, auditCell27]

theorem gaussianGrid28 : SharpGridCertificate ⟨28, by decide⟩ (299787518 / 10 ^ 9 : ℝ) := by
  constructor <;>
    norm_num [gaussianEnvelope, radiusEnvelope, cellUpper, worldUpper,
      noiseNode, proposedThetaUpper, min_def, rowCellAudit, auditCell28]

theorem gaussianGrid29 : SharpGridCertificate ⟨29, by decide⟩ (300512585 / 10 ^ 9 : ℝ) := by
  constructor <;>
    norm_num [gaussianEnvelope, radiusEnvelope, cellUpper, worldUpper,
      noiseNode, proposedThetaUpper, min_def, rowCellAudit, auditCell29]

theorem gaussianGrid30 : SharpGridCertificate ⟨30, by decide⟩ (301237654 / 10 ^ 9 : ℝ) := by
  constructor <;>
    norm_num [gaussianEnvelope, radiusEnvelope, cellUpper, worldUpper,
      noiseNode, proposedThetaUpper, min_def, rowCellAudit, auditCell30]

theorem gaussianGrid31 : SharpGridCertificate ⟨31, by decide⟩ (301962725 / 10 ^ 9 : ℝ) := by
  constructor <;>
    norm_num [gaussianEnvelope, radiusEnvelope, cellUpper, worldUpper,
      noiseNode, proposedThetaUpper, min_def, rowCellAudit, auditCell31]

theorem gaussianGrid32 : SharpGridCertificate ⟨32, by decide⟩ (302687798 / 10 ^ 9 : ℝ) := by
  constructor <;>
    norm_num [gaussianEnvelope, radiusEnvelope, cellUpper, worldUpper,
      noiseNode, proposedThetaUpper, min_def, rowCellAudit, auditCell32]

theorem gaussianGrid33 : SharpGridCertificate ⟨33, by decide⟩ (303412873 / 10 ^ 9 : ℝ) := by
  constructor <;>
    norm_num [gaussianEnvelope, radiusEnvelope, cellUpper, worldUpper,
      noiseNode, proposedThetaUpper, min_def, rowCellAudit, auditCell33]

theorem gaussianGrid34 : SharpGridCertificate ⟨34, by decide⟩ (304137950 / 10 ^ 9 : ℝ) := by
  constructor <;>
    norm_num [gaussianEnvelope, radiusEnvelope, cellUpper, worldUpper,
      noiseNode, proposedThetaUpper, min_def, rowCellAudit, auditCell34]

theorem gaussianGrid35 : SharpGridCertificate ⟨35, by decide⟩ (304863028 / 10 ^ 9 : ℝ) := by
  constructor <;>
    norm_num [gaussianEnvelope, radiusEnvelope, cellUpper, worldUpper,
      noiseNode, proposedThetaUpper, min_def, rowCellAudit, auditCell35]

theorem gaussianGrid36 : SharpGridCertificate ⟨36, by decide⟩ (305588109 / 10 ^ 9 : ℝ) := by
  constructor <;>
    norm_num [gaussianEnvelope, radiusEnvelope, cellUpper, worldUpper,
      noiseNode, proposedThetaUpper, min_def, rowCellAudit, auditCell36]

theorem gaussianGrid37 : SharpGridCertificate ⟨37, by decide⟩ (306313192 / 10 ^ 9 : ℝ) := by
  constructor <;>
    norm_num [gaussianEnvelope, radiusEnvelope, cellUpper, worldUpper,
      noiseNode, proposedThetaUpper, min_def, rowCellAudit, auditCell37]

theorem gaussianGrid38 : SharpGridCertificate ⟨38, by decide⟩ (307038276 / 10 ^ 9 : ℝ) := by
  constructor <;>
    norm_num [gaussianEnvelope, radiusEnvelope, cellUpper, worldUpper,
      noiseNode, proposedThetaUpper, min_def, rowCellAudit, auditCell38]

theorem gaussianGrid39 : SharpGridCertificate ⟨39, by decide⟩ (307763363 / 10 ^ 9 : ℝ) := by
  constructor <;>
    norm_num [gaussianEnvelope, radiusEnvelope, cellUpper, worldUpper,
      noiseNode, proposedThetaUpper, min_def, rowCellAudit, auditCell39]

theorem gaussianGrid40 : SharpGridCertificate ⟨40, by decide⟩ (308488451 / 10 ^ 9 : ℝ) := by
  constructor <;>
    norm_num [gaussianEnvelope, radiusEnvelope, cellUpper, worldUpper,
      noiseNode, proposedThetaUpper, min_def, rowCellAudit, auditCell40]

theorem gaussianGrid41 : SharpGridCertificate ⟨41, by decide⟩ (309213541 / 10 ^ 9 : ℝ) := by
  constructor <;>
    norm_num [gaussianEnvelope, radiusEnvelope, cellUpper, worldUpper,
      noiseNode, proposedThetaUpper, min_def, rowCellAudit, auditCell41]

theorem gaussianGrid42 : SharpGridCertificate ⟨42, by decide⟩ (309938634 / 10 ^ 9 : ℝ) := by
  constructor <;>
    norm_num [gaussianEnvelope, radiusEnvelope, cellUpper, worldUpper,
      noiseNode, proposedThetaUpper, min_def, rowCellAudit, auditCell42]

theorem gaussianGrid43 : SharpGridCertificate ⟨43, by decide⟩ (310663728 / 10 ^ 9 : ℝ) := by
  constructor <;>
    norm_num [gaussianEnvelope, radiusEnvelope, cellUpper, worldUpper,
      noiseNode, proposedThetaUpper, min_def, rowCellAudit, auditCell43]

theorem gaussianGrid44 : SharpGridCertificate ⟨44, by decide⟩ (311388824 / 10 ^ 9 : ℝ) := by
  constructor <;>
    norm_num [gaussianEnvelope, radiusEnvelope, cellUpper, worldUpper,
      noiseNode, proposedThetaUpper, min_def, rowCellAudit, auditCell44]

theorem gaussianGrid45 : SharpGridCertificate ⟨45, by decide⟩ (312113923 / 10 ^ 9 : ℝ) := by
  constructor <;>
    norm_num [gaussianEnvelope, radiusEnvelope, cellUpper, worldUpper,
      noiseNode, proposedThetaUpper, min_def, rowCellAudit, auditCell45]

theorem gaussianGrid46 : SharpGridCertificate ⟨46, by decide⟩ (312839023 / 10 ^ 9 : ℝ) := by
  constructor <;>
    norm_num [gaussianEnvelope, radiusEnvelope, cellUpper, worldUpper,
      noiseNode, proposedThetaUpper, min_def, rowCellAudit, auditCell46]

theorem gaussianGrid47 : SharpGridCertificate ⟨47, by decide⟩ (313564125 / 10 ^ 9 : ℝ) := by
  constructor <;>
    norm_num [gaussianEnvelope, radiusEnvelope, cellUpper, worldUpper,
      noiseNode, proposedThetaUpper, min_def, rowCellAudit, auditCell47]

theorem gaussianGrid48 : SharpGridCertificate ⟨48, by decide⟩ (314289229 / 10 ^ 9 : ℝ) := by
  constructor <;>
    norm_num [gaussianEnvelope, radiusEnvelope, cellUpper, worldUpper,
      noiseNode, proposedThetaUpper, min_def, rowCellAudit, auditCell48]

theorem gaussianGrid49 : SharpGridCertificate ⟨49, by decide⟩ (315014335 / 10 ^ 9 : ℝ) := by
  constructor <;>
    norm_num [gaussianEnvelope, radiusEnvelope, cellUpper, worldUpper,
      noiseNode, proposedThetaUpper, min_def, rowCellAudit, auditCell49]

theorem gaussianGrid50 : SharpGridCertificate ⟨50, by decide⟩ (315739443 / 10 ^ 9 : ℝ) := by
  constructor <;>
    norm_num [gaussianEnvelope, radiusEnvelope, cellUpper, worldUpper,
      noiseNode, proposedThetaUpper, min_def, rowCellAudit, auditCell50]

theorem gaussianGrid51 : SharpGridCertificate ⟨51, by decide⟩ (316464553 / 10 ^ 9 : ℝ) := by
  constructor <;>
    norm_num [gaussianEnvelope, radiusEnvelope, cellUpper, worldUpper,
      noiseNode, proposedThetaUpper, min_def, rowCellAudit, auditCell51]

theorem gaussianGrid52 : SharpGridCertificate ⟨52, by decide⟩ (316928423 / 10 ^ 9 : ℝ) := by
  constructor <;>
    norm_num [gaussianEnvelope, radiusEnvelope, cellUpper, worldUpper,
      noiseNode, proposedThetaUpper, min_def, rowCellAudit, auditCell52]

noncomputable def gaussianCapAt : Fin 43 → ℝ
  | ⟨0, _⟩ => 286736645 / 10 ^ 9
  | ⟨1, _⟩ => 287461677 / 10 ^ 9
  | ⟨2, _⟩ => 288186711 / 10 ^ 9
  | ⟨3, _⟩ => 288911746 / 10 ^ 9
  | ⟨4, _⟩ => 289636784 / 10 ^ 9
  | ⟨5, _⟩ => 290361824 / 10 ^ 9
  | ⟨6, _⟩ => 291086866 / 10 ^ 9
  | ⟨7, _⟩ => 291811910 / 10 ^ 9
  | ⟨8, _⟩ => 292536955 / 10 ^ 9
  | ⟨9, _⟩ => 293262003 / 10 ^ 9
  | ⟨10, _⟩ => 293987052 / 10 ^ 9
  | ⟨11, _⟩ => 294712104 / 10 ^ 9
  | ⟨12, _⟩ => 295437157 / 10 ^ 9
  | ⟨13, _⟩ => 296162212 / 10 ^ 9
  | ⟨14, _⟩ => 296887270 / 10 ^ 9
  | ⟨15, _⟩ => 297612329 / 10 ^ 9
  | ⟨16, _⟩ => 298337390 / 10 ^ 9
  | ⟨17, _⟩ => 299062453 / 10 ^ 9
  | ⟨18, _⟩ => 299787518 / 10 ^ 9
  | ⟨19, _⟩ => 300512585 / 10 ^ 9
  | ⟨20, _⟩ => 301237654 / 10 ^ 9
  | ⟨21, _⟩ => 301962725 / 10 ^ 9
  | ⟨22, _⟩ => 302687798 / 10 ^ 9
  | ⟨23, _⟩ => 303412873 / 10 ^ 9
  | ⟨24, _⟩ => 304137950 / 10 ^ 9
  | ⟨25, _⟩ => 304863028 / 10 ^ 9
  | ⟨26, _⟩ => 305588109 / 10 ^ 9
  | ⟨27, _⟩ => 306313192 / 10 ^ 9
  | ⟨28, _⟩ => 307038276 / 10 ^ 9
  | ⟨29, _⟩ => 307763363 / 10 ^ 9
  | ⟨30, _⟩ => 308488451 / 10 ^ 9
  | ⟨31, _⟩ => 309213541 / 10 ^ 9
  | ⟨32, _⟩ => 309938634 / 10 ^ 9
  | ⟨33, _⟩ => 310663728 / 10 ^ 9
  | ⟨34, _⟩ => 311388824 / 10 ^ 9
  | ⟨35, _⟩ => 312113923 / 10 ^ 9
  | ⟨36, _⟩ => 312839023 / 10 ^ 9
  | ⟨37, _⟩ => 313564125 / 10 ^ 9
  | ⟨38, _⟩ => 314289229 / 10 ^ 9
  | ⟨39, _⟩ => 315014335 / 10 ^ 9
  | ⟨40, _⟩ => 315739443 / 10 ^ 9
  | ⟨41, _⟩ => 316464553 / 10 ^ 9
  | ⟨42, _⟩ => 316928423 / 10 ^ 9
  | ⟨j + 43, h⟩ => False.elim (by omega)

noncomputable def capTable (i : Fin 60) : ℝ := by
  classical
  exact if h : Needed i then gaussianCapAt ⟨i.val - 10, by unfold Needed at h; omega⟩ else 0

theorem gaussianGridAt (j : Fin 43) :
    SharpGridCertificate ⟨j.val + 10, by omega⟩ (gaussianCapAt j) := by
  match j with
  | ⟨0, _⟩ => exact gaussianGrid10
  | ⟨1, _⟩ => exact gaussianGrid11
  | ⟨2, _⟩ => exact gaussianGrid12
  | ⟨3, _⟩ => exact gaussianGrid13
  | ⟨4, _⟩ => exact gaussianGrid14
  | ⟨5, _⟩ => exact gaussianGrid15
  | ⟨6, _⟩ => exact gaussianGrid16
  | ⟨7, _⟩ => exact gaussianGrid17
  | ⟨8, _⟩ => exact gaussianGrid18
  | ⟨9, _⟩ => exact gaussianGrid19
  | ⟨10, _⟩ => exact gaussianGrid20
  | ⟨11, _⟩ => exact gaussianGrid21
  | ⟨12, _⟩ => exact gaussianGrid22
  | ⟨13, _⟩ => exact gaussianGrid23
  | ⟨14, _⟩ => exact gaussianGrid24
  | ⟨15, _⟩ => exact gaussianGrid25
  | ⟨16, _⟩ => exact gaussianGrid26
  | ⟨17, _⟩ => exact gaussianGrid27
  | ⟨18, _⟩ => exact gaussianGrid28
  | ⟨19, _⟩ => exact gaussianGrid29
  | ⟨20, _⟩ => exact gaussianGrid30
  | ⟨21, _⟩ => exact gaussianGrid31
  | ⟨22, _⟩ => exact gaussianGrid32
  | ⟨23, _⟩ => exact gaussianGrid33
  | ⟨24, _⟩ => exact gaussianGrid34
  | ⟨25, _⟩ => exact gaussianGrid35
  | ⟨26, _⟩ => exact gaussianGrid36
  | ⟨27, _⟩ => exact gaussianGrid37
  | ⟨28, _⟩ => exact gaussianGrid38
  | ⟨29, _⟩ => exact gaussianGrid39
  | ⟨30, _⟩ => exact gaussianGrid40
  | ⟨31, _⟩ => exact gaussianGrid41
  | ⟨32, _⟩ => exact gaussianGrid42
  | ⟨33, _⟩ => exact gaussianGrid43
  | ⟨34, _⟩ => exact gaussianGrid44
  | ⟨35, _⟩ => exact gaussianGrid45
  | ⟨36, _⟩ => exact gaussianGrid46
  | ⟨37, _⟩ => exact gaussianGrid47
  | ⟨38, _⟩ => exact gaussianGrid48
  | ⟨39, _⟩ => exact gaussianGrid49
  | ⟨40, _⟩ => exact gaussianGrid50
  | ⟨41, _⟩ => exact gaussianGrid51
  | ⟨42, _⟩ => exact gaussianGrid52
  | ⟨j + 43, h⟩ => exact False.elim (by omega)

theorem capTable_certificate (i : Fin 60) (hi : Needed i) :
    SharpGridCertificate i (capTable i) := by
  let j : Fin 43 := ⟨i.val - 10, by unfold Needed at hi; omega⟩
  have he : (⟨j.val + 10, by omega⟩ : Fin 60) = i := by
    apply Fin.ext
    dsimp [j]
    have := hi.1
    omega
  have h := gaussianGridAt j
  rw [he] at h
  simpa only [capTable, dite_eq_left hi] using h

theorem gaussianCapAt_grid (j : Fin 43) :
    ∃ q : ℕ, gaussianCapAt j = (q : ℝ) / 10 ^ 9 := by
  match j with
  | ⟨0, _⟩ => exact ⟨286736645, rfl⟩
  | ⟨1, _⟩ => exact ⟨287461677, rfl⟩
  | ⟨2, _⟩ => exact ⟨288186711, rfl⟩
  | ⟨3, _⟩ => exact ⟨288911746, rfl⟩
  | ⟨4, _⟩ => exact ⟨289636784, rfl⟩
  | ⟨5, _⟩ => exact ⟨290361824, rfl⟩
  | ⟨6, _⟩ => exact ⟨291086866, rfl⟩
  | ⟨7, _⟩ => exact ⟨291811910, rfl⟩
  | ⟨8, _⟩ => exact ⟨292536955, rfl⟩
  | ⟨9, _⟩ => exact ⟨293262003, rfl⟩
  | ⟨10, _⟩ => exact ⟨293987052, rfl⟩
  | ⟨11, _⟩ => exact ⟨294712104, rfl⟩
  | ⟨12, _⟩ => exact ⟨295437157, rfl⟩
  | ⟨13, _⟩ => exact ⟨296162212, rfl⟩
  | ⟨14, _⟩ => exact ⟨296887270, rfl⟩
  | ⟨15, _⟩ => exact ⟨297612329, rfl⟩
  | ⟨16, _⟩ => exact ⟨298337390, rfl⟩
  | ⟨17, _⟩ => exact ⟨299062453, rfl⟩
  | ⟨18, _⟩ => exact ⟨299787518, rfl⟩
  | ⟨19, _⟩ => exact ⟨300512585, rfl⟩
  | ⟨20, _⟩ => exact ⟨301237654, rfl⟩
  | ⟨21, _⟩ => exact ⟨301962725, rfl⟩
  | ⟨22, _⟩ => exact ⟨302687798, rfl⟩
  | ⟨23, _⟩ => exact ⟨303412873, rfl⟩
  | ⟨24, _⟩ => exact ⟨304137950, rfl⟩
  | ⟨25, _⟩ => exact ⟨304863028, rfl⟩
  | ⟨26, _⟩ => exact ⟨305588109, rfl⟩
  | ⟨27, _⟩ => exact ⟨306313192, rfl⟩
  | ⟨28, _⟩ => exact ⟨307038276, rfl⟩
  | ⟨29, _⟩ => exact ⟨307763363, rfl⟩
  | ⟨30, _⟩ => exact ⟨308488451, rfl⟩
  | ⟨31, _⟩ => exact ⟨309213541, rfl⟩
  | ⟨32, _⟩ => exact ⟨309938634, rfl⟩
  | ⟨33, _⟩ => exact ⟨310663728, rfl⟩
  | ⟨34, _⟩ => exact ⟨311388824, rfl⟩
  | ⟨35, _⟩ => exact ⟨312113923, rfl⟩
  | ⟨36, _⟩ => exact ⟨312839023, rfl⟩
  | ⟨37, _⟩ => exact ⟨313564125, rfl⟩
  | ⟨38, _⟩ => exact ⟨314289229, rfl⟩
  | ⟨39, _⟩ => exact ⟨315014335, rfl⟩
  | ⟨40, _⟩ => exact ⟨315739443, rfl⟩
  | ⟨41, _⟩ => exact ⟨316464553, rfl⟩
  | ⟨42, _⟩ => exact ⟨316928423, rfl⟩
  | ⟨j + 43, h⟩ => exact False.elim (by omega)

theorem capTable_grid (i : Fin 60) (hi : Needed i) :
    ∃ q : ℕ, capTable i = (q : ℝ) / 10 ^ 9 := by
  simpa only [capTable, dite_eq_left hi] using
    gaussianCapAt_grid ⟨i.val - 10, by unfold Needed at hi; omega⟩

end BstLean.Part254
