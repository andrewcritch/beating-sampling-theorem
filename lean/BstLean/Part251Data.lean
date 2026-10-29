import BstLean.Part251Cells

/-! Proposed scalar data and kernel-checked incompatibility certificates. -/
namespace BstLean.Part251

noncomputable def auditCell0 : CellAudit (0 : Fin 60) where
  covarianceCap := 135905783377 / 500000000000
  centreCap := 42273779883 / 500000000000
  covariance_nonneg := by norm_num
  covariance_too_small := by norm_num [noiseNode, proposedThetaUpper]
  centre_too_large := by norm_num

noncomputable def auditCell1 : CellAudit (1 : Fin 60) where
  covarianceCap := 10888832149 / 40000000000
  centreCap := 42273779883 / 500000000000
  covariance_nonneg := by norm_num
  covariance_too_small := by norm_num [noiseNode, proposedThetaUpper]
  centre_too_large := by norm_num

noncomputable def auditCell2 : CellAudit (2 : Fin 60) where
  covarianceCap := 136314492499 / 500000000000
  centreCap := 42273779883 / 500000000000
  covariance_nonneg := by norm_num
  covariance_too_small := by norm_num [noiseNode, proposedThetaUpper]
  centre_too_large := by norm_num

noncomputable def auditCell3 : CellAudit (3 : Fin 60) where
  covarianceCap := 34129514037 / 125000000000
  centreCap := 42273779883 / 500000000000
  covariance_nonneg := by norm_num
  covariance_too_small := by norm_num [noiseNode, proposedThetaUpper]
  centre_too_large := by norm_num

noncomputable def auditCell4 : CellAudit (4 : Fin 60) where
  covarianceCap := 136721093667 / 500000000000
  centreCap := 42273779883 / 500000000000
  covariance_nonneg := by norm_num
  covariance_too_small := by norm_num [noiseNode, proposedThetaUpper]
  centre_too_large := by norm_num

noncomputable def auditCell5 : CellAudit (5 : Fin 60) where
  covarianceCap := 273847211823 / 1000000000000
  centreCap := 42273779883 / 500000000000
  covariance_nonneg := by norm_num
  covariance_too_small := by norm_num [noiseNode, proposedThetaUpper]
  centre_too_large := by norm_num

noncomputable def auditCell6 : CellAudit (6 : Fin 60) where
  covarianceCap := 137125593731 / 500000000000
  centreCap := 85520820403 / 1000000000000
  covariance_nonneg := by norm_num
  covariance_too_small := by norm_num [noiseNode, proposedThetaUpper]
  centre_too_large := by norm_num

noncomputable def auditCell7 : CellAudit (7 : Fin 60) where
  covarianceCap := 274657520549 / 1000000000000
  centreCap := 85520820403 / 1000000000000
  covariance_nonneg := by norm_num
  covariance_too_small := by norm_num [noiseNode, proposedThetaUpper]
  centre_too_large := by norm_num

noncomputable def auditCell8 : CellAudit (8 : Fin 60) where
  covarianceCap := 275063875967 / 1000000000000
  centreCap := 85520820403 / 1000000000000
  covariance_nonneg := by norm_num
  covariance_too_small := by norm_num [noiseNode, proposedThetaUpper]
  centre_too_large := by norm_num

noncomputable def auditCell9 : CellAudit (9 : Fin 60) where
  covarianceCap := 275469213113 / 1000000000000
  centreCap := 85520820403 / 1000000000000
  covariance_nonneg := by norm_num
  covariance_too_small := by norm_num [noiseNode, proposedThetaUpper]
  centre_too_large := by norm_num

noncomputable def auditCell10 : CellAudit (10 : Fin 60) where
  covarianceCap := 68968383441 / 250000000000
  centreCap := 85520820403 / 1000000000000
  covariance_nonneg := by norm_num
  covariance_too_small := by norm_num [noiseNode, proposedThetaUpper]
  centre_too_large := by norm_num

noncomputable def auditCell11 : CellAudit (11 : Fin 60) where
  covarianceCap := 138138419847 / 500000000000
  centreCap := 85520820403 / 1000000000000
  covariance_nonneg := by norm_num
  covariance_too_small := by norm_num [noiseNode, proposedThetaUpper]
  centre_too_large := by norm_num

noncomputable def auditCell12 : CellAudit (12 : Fin 60) where
  covarianceCap := 276679132669 / 1000000000000
  centreCap := 2702976851 / 31250000000
  covariance_nonneg := by norm_num
  covariance_too_small := by norm_num [noiseNode, proposedThetaUpper]
  centre_too_large := by norm_num

noncomputable def auditCell13 : CellAudit (13 : Fin 60) where
  covarianceCap := 17317525903 / 62500000000
  centreCap := 2702976851 / 31250000000
  covariance_nonneg := by norm_num
  covariance_too_small := by norm_num [noiseNode, proposedThetaUpper]
  centre_too_large := by norm_num

noncomputable def auditCell14 : CellAudit (14 : Fin 60) where
  covarianceCap := 138740343393 / 500000000000
  centreCap := 2702976851 / 31250000000
  covariance_nonneg := by norm_num
  covariance_too_small := by norm_num [noiseNode, proposedThetaUpper]
  centre_too_large := by norm_num

noncomputable def auditCell15 : CellAudit (15 : Fin 60) where
  covarianceCap := 27787995143 / 100000000000
  centreCap := 2702976851 / 31250000000
  covariance_nonneg := by norm_num
  covariance_too_small := by norm_num [noiseNode, proposedThetaUpper]
  centre_too_large := by norm_num

noncomputable def auditCell16 : CellAudit (16 : Fin 60) where
  covarianceCap := 278278210121 / 1000000000000
  centreCap := 2702976851 / 31250000000
  covariance_nonneg := by norm_num
  covariance_too_small := by norm_num [noiseNode, proposedThetaUpper]
  centre_too_large := by norm_num

noncomputable def auditCell17 : CellAudit (17 : Fin 60) where
  covarianceCap := 139337732297 / 500000000000
  centreCap := 2702976851 / 31250000000
  covariance_nonneg := by norm_num
  covariance_too_small := by norm_num [noiseNode, proposedThetaUpper]
  centre_too_large := by norm_num

noncomputable def auditCell18 : CellAudit (18 : Fin 60) where
  covarianceCap := 139535858289 / 500000000000
  centreCap := 43736504769 / 500000000000
  covariance_nonneg := by norm_num
  covariance_too_small := by norm_num [noiseNode, proposedThetaUpper]
  centre_too_large := by norm_num

noncomputable def auditCell19 : CellAudit (19 : Fin 60) where
  covarianceCap := 69866741949 / 250000000000
  centreCap := 43736504769 / 500000000000
  covariance_nonneg := by norm_num
  covariance_too_small := by norm_num [noiseNode, proposedThetaUpper]
  centre_too_large := by norm_num

noncomputable def auditCell20 : CellAudit (20 : Fin 60) where
  covarianceCap := 55972243993 / 200000000000
  centreCap := 43736504769 / 500000000000
  covariance_nonneg := by norm_num
  covariance_too_small := by norm_num [noiseNode, proposedThetaUpper]
  centre_too_large := by norm_num

noncomputable def auditCell21 : CellAudit (21 : Fin 60) where
  covarianceCap := 70063618699 / 250000000000
  centreCap := 43736504769 / 500000000000
  covariance_nonneg := by norm_num
  covariance_too_small := by norm_num [noiseNode, proposedThetaUpper]
  centre_too_large := by norm_num

noncomputable def auditCell22 : CellAudit (22 : Fin 60) where
  covarianceCap := 56129346799 / 200000000000
  centreCap := 43736504769 / 500000000000
  covariance_nonneg := by norm_num
  covariance_too_small := by norm_num [noiseNode, proposedThetaUpper]
  centre_too_large := by norm_num

noncomputable def auditCell23 : CellAudit (23 : Fin 60) where
  covarianceCap := 281037999259 / 1000000000000
  centreCap := 43736504769 / 500000000000
  covariance_nonneg := by norm_num
  covariance_too_small := by norm_num [noiseNode, proposedThetaUpper]
  centre_too_large := by norm_num

noncomputable def auditCell24 : CellAudit (24 : Fin 60) where
  covarianceCap := 281428677441 / 1000000000000
  centreCap := 88456634297 / 1000000000000
  covariance_nonneg := by norm_num
  covariance_too_small := by norm_num [noiseNode, proposedThetaUpper]
  centre_too_large := by norm_num

noncomputable def auditCell25 : CellAudit (25 : Fin 60) where
  covarianceCap := 11272748077 / 40000000000
  centreCap := 88456634297 / 1000000000000
  covariance_nonneg := by norm_num
  covariance_too_small := by norm_num [noiseNode, proposedThetaUpper]
  centre_too_large := by norm_num

noncomputable def auditCell26 : CellAudit (26 : Fin 60) where
  covarianceCap := 282207746011 / 1000000000000
  centreCap := 88456634297 / 1000000000000
  covariance_nonneg := by norm_num
  covariance_too_small := by norm_num [noiseNode, proposedThetaUpper]
  centre_too_large := by norm_num

noncomputable def auditCell27 : CellAudit (27 : Fin 60) where
  covarianceCap := 282595811443 / 1000000000000
  centreCap := 88456634297 / 1000000000000
  covariance_nonneg := by norm_num
  covariance_too_small := by norm_num [noiseNode, proposedThetaUpper]
  centre_too_large := by norm_num

noncomputable def auditCell28 : CellAudit (28 : Fin 60) where
  covarianceCap := 141491449979 / 500000000000
  centreCap := 88456634297 / 1000000000000
  covariance_nonneg := by norm_num
  covariance_too_small := by norm_num [noiseNode, proposedThetaUpper]
  centre_too_large := by norm_num

noncomputable def auditCell29 : CellAudit (29 : Fin 60) where
  covarianceCap := 35421126661 / 125000000000
  centreCap := 88456634297 / 1000000000000
  covariance_nonneg := by norm_num
  covariance_too_small := by norm_num [noiseNode, proposedThetaUpper]
  centre_too_large := by norm_num

noncomputable def auditCell30 : CellAudit (30 : Fin 60) where
  covarianceCap := 141877076581 / 500000000000
  centreCap := 89449187659 / 1000000000000
  covariance_nonneg := by norm_num
  covariance_too_small := by norm_num [noiseNode, proposedThetaUpper]
  centre_too_large := by norm_num

noncomputable def auditCell31 : CellAudit (31 : Fin 60) where
  covarianceCap := 284138321301 / 1000000000000
  centreCap := 89449187659 / 1000000000000
  covariance_nonneg := by norm_num
  covariance_too_small := by norm_num [noiseNode, proposedThetaUpper]
  centre_too_large := by norm_num

noncomputable def auditCell32 : CellAudit (32 : Fin 60) where
  covarianceCap := 142260759711 / 500000000000
  centreCap := 89449187659 / 1000000000000
  covariance_nonneg := by norm_num
  covariance_too_small := by norm_num [noiseNode, proposedThetaUpper]
  centre_too_large := by norm_num

noncomputable def auditCell33 : CellAudit (33 : Fin 60) where
  covarianceCap := 284903749239 / 1000000000000
  centreCap := 89449187659 / 1000000000000
  covariance_nonneg := by norm_num
  covariance_too_small := by norm_num [noiseNode, proposedThetaUpper]
  centre_too_large := by norm_num

noncomputable def auditCell34 : CellAudit (34 : Fin 60) where
  covarianceCap := 285285012459 / 1000000000000
  centreCap := 89449187659 / 1000000000000
  covariance_nonneg := by norm_num
  covariance_too_small := by norm_num [noiseNode, proposedThetaUpper]
  centre_too_large := by norm_num

noncomputable def auditCell35 : CellAudit (35 : Fin 60) where
  covarianceCap := 142832679263 / 500000000000
  centreCap := 89449187659 / 1000000000000
  covariance_nonneg := by norm_num
  covariance_too_small := by norm_num [noiseNode, proposedThetaUpper]
  centre_too_large := by norm_num

noncomputable def auditCell36 : CellAudit (36 : Fin 60) where
  covarianceCap := 286044743167 / 1000000000000
  centreCap := 90454281683 / 1000000000000
  covariance_nonneg := by norm_num
  covariance_too_small := by norm_num [noiseNode, proposedThetaUpper]
  centre_too_large := by norm_num

noncomputable def auditCell37 : CellAudit (37 : Fin 60) where
  covarianceCap := 143211583297 / 500000000000
  centreCap := 90454281683 / 1000000000000
  covariance_nonneg := by norm_num
  covariance_too_small := by norm_num [noiseNode, proposedThetaUpper]
  centre_too_large := by norm_num

noncomputable def auditCell38 : CellAudit (38 : Fin 60) where
  covarianceCap := 8962519703 / 31250000000
  centreCap := 90454281683 / 1000000000000
  covariance_nonneg := by norm_num
  covariance_too_small := by norm_num [noiseNode, proposedThetaUpper]
  centre_too_large := by norm_num

noncomputable def auditCell39 : CellAudit (39 : Fin 60) where
  covarianceCap := 287177136557 / 1000000000000
  centreCap := 90454281683 / 1000000000000
  covariance_nonneg := by norm_num
  covariance_too_small := by norm_num [noiseNode, proposedThetaUpper]
  centre_too_large := by norm_num

noncomputable def auditCell40 : CellAudit (40 : Fin 60) where
  covarianceCap := 14377634323 / 50000000000
  centreCap := 90454281683 / 1000000000000
  covariance_nonneg := by norm_num
  covariance_too_small := by norm_num [noiseNode, proposedThetaUpper]
  centre_too_large := by norm_num

noncomputable def auditCell41 : CellAudit (41 : Fin 60) where
  covarianceCap := 7198182047 / 25000000000
  centreCap := 90454281683 / 1000000000000
  covariance_nonneg := by norm_num
  covariance_too_small := by norm_num [noiseNode, proposedThetaUpper]
  centre_too_large := by norm_num

noncomputable def auditCell42 : CellAudit (42 : Fin 60) where
  covarianceCap := 288300924489 / 1000000000000
  centreCap := 91476158251 / 1000000000000
  covariance_nonneg := by norm_num
  covariance_too_small := by norm_num [noiseNode, proposedThetaUpper]
  centre_too_large := by norm_num

noncomputable def auditCell43 : CellAudit (43 : Fin 60) where
  covarianceCap := 288673615953 / 1000000000000
  centreCap := 91476158251 / 1000000000000
  covariance_nonneg := by norm_num
  covariance_too_small := by norm_num [noiseNode, proposedThetaUpper]
  centre_too_large := by norm_num

noncomputable def auditCell44 : CellAudit (44 : Fin 60) where
  covarianceCap := 18065334871 / 62500000000
  centreCap := 91476158251 / 1000000000000
  covariance_nonneg := by norm_num
  covariance_too_small := by norm_num [noiseNode, proposedThetaUpper]
  centre_too_large := by norm_num

noncomputable def auditCell45 : CellAudit (45 : Fin 60) where
  covarianceCap := 57883230419 / 200000000000
  centreCap := 91476158251 / 1000000000000
  covariance_nonneg := by norm_num
  covariance_too_small := by norm_num [noiseNode, proposedThetaUpper]
  centre_too_large := by norm_num

noncomputable def auditCell46 : CellAudit (46 : Fin 60) where
  covarianceCap := 57957200017 / 200000000000
  centreCap := 91476158251 / 1000000000000
  covariance_nonneg := by norm_num
  covariance_too_small := by norm_num [noiseNode, proposedThetaUpper]
  centre_too_large := by norm_num

noncomputable def auditCell47 : CellAudit (47 : Fin 60) where
  covarianceCap := 145077451777 / 500000000000
  centreCap := 91476158251 / 1000000000000
  covariance_nonneg := by norm_num
  covariance_too_small := by norm_num [noiseNode, proposedThetaUpper]
  centre_too_large := by norm_num

noncomputable def auditCell48 : CellAudit (48 : Fin 60) where
  covarianceCap := 290522864149 / 1000000000000
  centreCap := 2312994151 / 25000000000
  covariance_nonneg := by norm_num
  covariance_too_small := by norm_num [noiseNode, proposedThetaUpper]
  centre_too_large := by norm_num

noncomputable def auditCell49 : CellAudit (49 : Fin 60) where
  covarianceCap := 290889883511 / 1000000000000
  centreCap := 2312994151 / 25000000000
  covariance_nonneg := by norm_num
  covariance_too_small := by norm_num [noiseNode, proposedThetaUpper]
  centre_too_large := by norm_num

noncomputable def auditCell50 : CellAudit (50 : Fin 60) where
  covarianceCap := 11650238531 / 40000000000
  centreCap := 2312994151 / 25000000000
  covariance_nonneg := by norm_num
  covariance_too_small := by norm_num [noiseNode, proposedThetaUpper]
  centre_too_large := by norm_num

noncomputable def auditCell51 : CellAudit (51 : Fin 60) where
  covarianceCap := 145810552537 / 500000000000
  centreCap := 2312994151 / 25000000000
  covariance_nonneg := by norm_num
  covariance_too_small := by norm_num [noiseNode, proposedThetaUpper]
  centre_too_large := by norm_num

noncomputable def auditCell52 : CellAudit (52 : Fin 60) where
  covarianceCap := 145992655269 / 500000000000
  centreCap := 2312994151 / 25000000000
  covariance_nonneg := by norm_num
  covariance_too_small := by norm_num [noiseNode, proposedThetaUpper]
  centre_too_large := by norm_num

noncomputable def auditCell53 : CellAudit (53 : Fin 60) where
  covarianceCap := 29234858129 / 100000000000
  centreCap := 2312994151 / 25000000000
  covariance_nonneg := by norm_num
  covariance_too_small := by norm_num [noiseNode, proposedThetaUpper]
  centre_too_large := by norm_num

noncomputable def auditCell54 : CellAudit (54 : Fin 60) where
  covarianceCap := 292710918951 / 1000000000000
  centreCap := 9359084231 / 100000000000
  covariance_nonneg := by norm_num
  covariance_too_small := by norm_num [noiseNode, proposedThetaUpper]
  centre_too_large := by norm_num

noncomputable def auditCell55 : CellAudit (55 : Fin 60) where
  covarianceCap := 18317020321 / 62500000000
  centreCap := 9359084231 / 100000000000
  covariance_nonneg := by norm_num
  covariance_too_small := by norm_num [noiseNode, proposedThetaUpper]
  centre_too_large := by norm_num

noncomputable def auditCell56 : CellAudit (56 : Fin 60) where
  covarianceCap := 14671640073 / 50000000000
  centreCap := 9359084231 / 100000000000
  covariance_nonneg := by norm_num
  covariance_too_small := by norm_num [noiseNode, proposedThetaUpper]
  centre_too_large := by norm_num

noncomputable def auditCell57 : CellAudit (57 : Fin 60) where
  covarianceCap := 36724043691 / 125000000000
  centreCap := 9359084231 / 100000000000
  covariance_nonneg := by norm_num
  covariance_too_small := by norm_num [noiseNode, proposedThetaUpper]
  centre_too_large := by norm_num

noncomputable def auditCell58 : CellAudit (58 : Fin 60) where
  covarianceCap := 73537742737 / 250000000000
  centreCap := 9359084231 / 100000000000
  covariance_nonneg := by norm_num
  covariance_too_small := by norm_num [noiseNode, proposedThetaUpper]
  centre_too_large := by norm_num

noncomputable def auditCell59 : CellAudit (59 : Fin 60) where
  covarianceCap := 147254333659 / 500000000000
  centreCap := 9359084231 / 100000000000
  covariance_nonneg := by norm_num
  covariance_too_small := by norm_num [noiseNode, proposedThetaUpper]
  centre_too_large := by norm_num

noncomputable def rowCellAudit (i : Fin 60) : CellAudit i :=
  match i with
  | ⟨0, _⟩ => auditCell0
  | ⟨1, _⟩ => auditCell1
  | ⟨2, _⟩ => auditCell2
  | ⟨3, _⟩ => auditCell3
  | ⟨4, _⟩ => auditCell4
  | ⟨5, _⟩ => auditCell5
  | ⟨6, _⟩ => auditCell6
  | ⟨7, _⟩ => auditCell7
  | ⟨8, _⟩ => auditCell8
  | ⟨9, _⟩ => auditCell9
  | ⟨10, _⟩ => auditCell10
  | ⟨11, _⟩ => auditCell11
  | ⟨12, _⟩ => auditCell12
  | ⟨13, _⟩ => auditCell13
  | ⟨14, _⟩ => auditCell14
  | ⟨15, _⟩ => auditCell15
  | ⟨16, _⟩ => auditCell16
  | ⟨17, _⟩ => auditCell17
  | ⟨18, _⟩ => auditCell18
  | ⟨19, _⟩ => auditCell19
  | ⟨20, _⟩ => auditCell20
  | ⟨21, _⟩ => auditCell21
  | ⟨22, _⟩ => auditCell22
  | ⟨23, _⟩ => auditCell23
  | ⟨24, _⟩ => auditCell24
  | ⟨25, _⟩ => auditCell25
  | ⟨26, _⟩ => auditCell26
  | ⟨27, _⟩ => auditCell27
  | ⟨28, _⟩ => auditCell28
  | ⟨29, _⟩ => auditCell29
  | ⟨30, _⟩ => auditCell30
  | ⟨31, _⟩ => auditCell31
  | ⟨32, _⟩ => auditCell32
  | ⟨33, _⟩ => auditCell33
  | ⟨34, _⟩ => auditCell34
  | ⟨35, _⟩ => auditCell35
  | ⟨36, _⟩ => auditCell36
  | ⟨37, _⟩ => auditCell37
  | ⟨38, _⟩ => auditCell38
  | ⟨39, _⟩ => auditCell39
  | ⟨40, _⟩ => auditCell40
  | ⟨41, _⟩ => auditCell41
  | ⟨42, _⟩ => auditCell42
  | ⟨43, _⟩ => auditCell43
  | ⟨44, _⟩ => auditCell44
  | ⟨45, _⟩ => auditCell45
  | ⟨46, _⟩ => auditCell46
  | ⟨47, _⟩ => auditCell47
  | ⟨48, _⟩ => auditCell48
  | ⟨49, _⟩ => auditCell49
  | ⟨50, _⟩ => auditCell50
  | ⟨51, _⟩ => auditCell51
  | ⟨52, _⟩ => auditCell52
  | ⟨53, _⟩ => auditCell53
  | ⟨54, _⟩ => auditCell54
  | ⟨55, _⟩ => auditCell55
  | ⟨56, _⟩ => auditCell56
  | ⟨57, _⟩ => auditCell57
  | ⟨58, _⟩ => auditCell58
  | ⟨59, _⟩ => auditCell59
  | ⟨j + 60, h⟩ => False.elim (by omega)

end BstLean.Part251
