import BstLean.Part253Scalar
import BstLean.Part254Interface

/-! The supplied covariance contract has larger caps than the source proposals.
The fixed source-style cutoffs fail with those checked caps. -/
namespace BstLean.Part253
open Real

theorem supplied_covariance :
    LocalCovariance BstLean.Part254.cell BstLean.Part254.capTable :=
  BstLean.Part254.localCov_part253

noncomputable def certifiedFrameExpression (i : Fin 60) : ℝ :=
  (BstLean.Part254.capTable i + centreTable (centreGroup i)) / cutoffTable i + massTable i

theorem certifiedFrame10 : (1.489 : ℝ) ≤ certifiedFrameExpression 10 := by
  norm_num [certifiedFrameExpression, BstLean.Part254.capTable,
    BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed,
    centreTable, centreGroup, cutoffTable, massTable]

theorem certifiedFrame11 : (1.489 : ℝ) ≤ certifiedFrameExpression 11 := by
  norm_num [certifiedFrameExpression, BstLean.Part254.capTable,
    BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed,
    centreTable, centreGroup, cutoffTable, massTable]

theorem certifiedFrame12 : (1.489 : ℝ) ≤ certifiedFrameExpression 12 := by
  norm_num [certifiedFrameExpression, BstLean.Part254.capTable,
    BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed,
    centreTable, centreGroup, cutoffTable, massTable]

theorem certifiedFrame13 : (1.489 : ℝ) ≤ certifiedFrameExpression 13 := by
  norm_num [certifiedFrameExpression, BstLean.Part254.capTable,
    BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed,
    centreTable, centreGroup, cutoffTable, massTable]

theorem certifiedFrame14 : (1.489 : ℝ) ≤ certifiedFrameExpression 14 := by
  norm_num [certifiedFrameExpression, BstLean.Part254.capTable,
    BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed,
    centreTable, centreGroup, cutoffTable, massTable]

theorem certifiedFrame15 : (1.489 : ℝ) ≤ certifiedFrameExpression 15 := by
  norm_num [certifiedFrameExpression, BstLean.Part254.capTable,
    BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed,
    centreTable, centreGroup, cutoffTable, massTable]

theorem certifiedFrame16 : (1.489 : ℝ) ≤ certifiedFrameExpression 16 := by
  norm_num [certifiedFrameExpression, BstLean.Part254.capTable,
    BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed,
    centreTable, centreGroup, cutoffTable, massTable]

theorem certifiedFrame17 : (1.489 : ℝ) ≤ certifiedFrameExpression 17 := by
  norm_num [certifiedFrameExpression, BstLean.Part254.capTable,
    BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed,
    centreTable, centreGroup, cutoffTable, massTable]

theorem certifiedFrame18 : (1.489 : ℝ) ≤ certifiedFrameExpression 18 := by
  norm_num [certifiedFrameExpression, BstLean.Part254.capTable,
    BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed,
    centreTable, centreGroup, cutoffTable, massTable]

theorem certifiedFrame19 : (1.489 : ℝ) ≤ certifiedFrameExpression 19 := by
  norm_num [certifiedFrameExpression, BstLean.Part254.capTable,
    BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed,
    centreTable, centreGroup, cutoffTable, massTable]

theorem certifiedFrame20 : (1.489 : ℝ) ≤ certifiedFrameExpression 20 := by
  norm_num [certifiedFrameExpression, BstLean.Part254.capTable,
    BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed,
    centreTable, centreGroup, cutoffTable, massTable]

theorem certifiedFrame21 : (1.489 : ℝ) ≤ certifiedFrameExpression 21 := by
  norm_num [certifiedFrameExpression, BstLean.Part254.capTable,
    BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed,
    centreTable, centreGroup, cutoffTable, massTable]

theorem certifiedFrame22 : (1.489 : ℝ) ≤ certifiedFrameExpression 22 := by
  norm_num [certifiedFrameExpression, BstLean.Part254.capTable,
    BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed,
    centreTable, centreGroup, cutoffTable, massTable]

theorem certifiedFrame23 : (1.489 : ℝ) ≤ certifiedFrameExpression 23 := by
  norm_num [certifiedFrameExpression, BstLean.Part254.capTable,
    BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed,
    centreTable, centreGroup, cutoffTable, massTable]

theorem certifiedFrame24 : (1.489 : ℝ) ≤ certifiedFrameExpression 24 := by
  norm_num [certifiedFrameExpression, BstLean.Part254.capTable,
    BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed,
    centreTable, centreGroup, cutoffTable, massTable]

theorem certifiedFrame25 : (1.489 : ℝ) ≤ certifiedFrameExpression 25 := by
  norm_num [certifiedFrameExpression, BstLean.Part254.capTable,
    BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed,
    centreTable, centreGroup, cutoffTable, massTable]

theorem certifiedFrame26 : (1.489 : ℝ) ≤ certifiedFrameExpression 26 := by
  norm_num [certifiedFrameExpression, BstLean.Part254.capTable,
    BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed,
    centreTable, centreGroup, cutoffTable, massTable]

theorem certifiedFrame27 : (1.489 : ℝ) ≤ certifiedFrameExpression 27 := by
  norm_num [certifiedFrameExpression, BstLean.Part254.capTable,
    BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed,
    centreTable, centreGroup, cutoffTable, massTable]

theorem certifiedFrame28 : (1.489 : ℝ) ≤ certifiedFrameExpression 28 := by
  norm_num [certifiedFrameExpression, BstLean.Part254.capTable,
    BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed,
    centreTable, centreGroup, cutoffTable, massTable]

theorem certifiedFrame29 : (1.489 : ℝ) ≤ certifiedFrameExpression 29 := by
  norm_num [certifiedFrameExpression, BstLean.Part254.capTable,
    BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed,
    centreTable, centreGroup, cutoffTable, massTable]

theorem certifiedFrame30 : (1.489 : ℝ) ≤ certifiedFrameExpression 30 := by
  norm_num [certifiedFrameExpression, BstLean.Part254.capTable,
    BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed,
    centreTable, centreGroup, cutoffTable, massTable]

theorem certifiedFrame31 : (1.489 : ℝ) ≤ certifiedFrameExpression 31 := by
  norm_num [certifiedFrameExpression, BstLean.Part254.capTable,
    BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed,
    centreTable, centreGroup, cutoffTable, massTable]

theorem certifiedFrame32 : (1.489 : ℝ) ≤ certifiedFrameExpression 32 := by
  norm_num [certifiedFrameExpression, BstLean.Part254.capTable,
    BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed,
    centreTable, centreGroup, cutoffTable, massTable]

theorem certifiedFrame33 : (1.489 : ℝ) ≤ certifiedFrameExpression 33 := by
  norm_num [certifiedFrameExpression, BstLean.Part254.capTable,
    BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed,
    centreTable, centreGroup, cutoffTable, massTable]

theorem certifiedFrame34 : (1.489 : ℝ) ≤ certifiedFrameExpression 34 := by
  norm_num [certifiedFrameExpression, BstLean.Part254.capTable,
    BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed,
    centreTable, centreGroup, cutoffTable, massTable]

theorem certifiedFrame35 : (1.489 : ℝ) ≤ certifiedFrameExpression 35 := by
  norm_num [certifiedFrameExpression, BstLean.Part254.capTable,
    BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed,
    centreTable, centreGroup, cutoffTable, massTable]

theorem certifiedFrame36 : (1.489 : ℝ) ≤ certifiedFrameExpression 36 := by
  norm_num [certifiedFrameExpression, BstLean.Part254.capTable,
    BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed,
    centreTable, centreGroup, cutoffTable, massTable]

theorem certifiedFrame37 : (1.489 : ℝ) ≤ certifiedFrameExpression 37 := by
  norm_num [certifiedFrameExpression, BstLean.Part254.capTable,
    BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed,
    centreTable, centreGroup, cutoffTable, massTable]

theorem certifiedFrame38 : (1.489 : ℝ) ≤ certifiedFrameExpression 38 := by
  norm_num [certifiedFrameExpression, BstLean.Part254.capTable,
    BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed,
    centreTable, centreGroup, cutoffTable, massTable]

theorem certifiedFrame39 : (1.489 : ℝ) ≤ certifiedFrameExpression 39 := by
  norm_num [certifiedFrameExpression, BstLean.Part254.capTable,
    BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed,
    centreTable, centreGroup, cutoffTable, massTable]

theorem certifiedFrame40 : (1.489 : ℝ) ≤ certifiedFrameExpression 40 := by
  norm_num [certifiedFrameExpression, BstLean.Part254.capTable,
    BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed,
    centreTable, centreGroup, cutoffTable, massTable]

theorem certifiedFrame41 : (1.489 : ℝ) ≤ certifiedFrameExpression 41 := by
  norm_num [certifiedFrameExpression, BstLean.Part254.capTable,
    BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed,
    centreTable, centreGroup, cutoffTable, massTable]

theorem certifiedFrame42 : (1.489 : ℝ) ≤ certifiedFrameExpression 42 := by
  norm_num [certifiedFrameExpression, BstLean.Part254.capTable,
    BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed,
    centreTable, centreGroup, cutoffTable, massTable]

theorem certifiedFrame43 : (1.489 : ℝ) ≤ certifiedFrameExpression 43 := by
  norm_num [certifiedFrameExpression, BstLean.Part254.capTable,
    BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed,
    centreTable, centreGroup, cutoffTable, massTable]

theorem certifiedFrame44 : (1.489 : ℝ) ≤ certifiedFrameExpression 44 := by
  norm_num [certifiedFrameExpression, BstLean.Part254.capTable,
    BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed,
    centreTable, centreGroup, cutoffTable, massTable]

theorem certifiedFrame45 : (1.489 : ℝ) ≤ certifiedFrameExpression 45 := by
  norm_num [certifiedFrameExpression, BstLean.Part254.capTable,
    BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed,
    centreTable, centreGroup, cutoffTable, massTable]

theorem certifiedFrame46 : (1.489 : ℝ) ≤ certifiedFrameExpression 46 := by
  norm_num [certifiedFrameExpression, BstLean.Part254.capTable,
    BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed,
    centreTable, centreGroup, cutoffTable, massTable]

theorem certifiedFrame47 : (1.489 : ℝ) ≤ certifiedFrameExpression 47 := by
  norm_num [certifiedFrameExpression, BstLean.Part254.capTable,
    BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed,
    centreTable, centreGroup, cutoffTable, massTable]

theorem certifiedFrame48 : (1.489 : ℝ) ≤ certifiedFrameExpression 48 := by
  norm_num [certifiedFrameExpression, BstLean.Part254.capTable,
    BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed,
    centreTable, centreGroup, cutoffTable, massTable]

theorem certifiedFrame49 : (1.489 : ℝ) ≤ certifiedFrameExpression 49 := by
  norm_num [certifiedFrameExpression, BstLean.Part254.capTable,
    BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed,
    centreTable, centreGroup, cutoffTable, massTable]

theorem certifiedFrame50 : (1.489 : ℝ) ≤ certifiedFrameExpression 50 := by
  norm_num [certifiedFrameExpression, BstLean.Part254.capTable,
    BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed,
    centreTable, centreGroup, cutoffTable, massTable]

theorem certifiedFrame51 : (1.489 : ℝ) ≤ certifiedFrameExpression 51 := by
  norm_num [certifiedFrameExpression, BstLean.Part254.capTable,
    BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed,
    centreTable, centreGroup, cutoffTable, massTable]

theorem certifiedFrame52 : (1.489 : ℝ) ≤ certifiedFrameExpression 52 := by
  norm_num [certifiedFrameExpression, BstLean.Part254.capTable,
    BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed,
    centreTable, centreGroup, cutoffTable, massTable]

theorem certifiedFrameNeeded (j : Fin 43) :
    (1.489 : ℝ) ≤ certifiedFrameExpression ⟨j.val + 10, by omega⟩ := by
  match j with
  | ⟨0, _⟩ => exact certifiedFrame10
  | ⟨1, _⟩ => exact certifiedFrame11
  | ⟨2, _⟩ => exact certifiedFrame12
  | ⟨3, _⟩ => exact certifiedFrame13
  | ⟨4, _⟩ => exact certifiedFrame14
  | ⟨5, _⟩ => exact certifiedFrame15
  | ⟨6, _⟩ => exact certifiedFrame16
  | ⟨7, _⟩ => exact certifiedFrame17
  | ⟨8, _⟩ => exact certifiedFrame18
  | ⟨9, _⟩ => exact certifiedFrame19
  | ⟨10, _⟩ => exact certifiedFrame20
  | ⟨11, _⟩ => exact certifiedFrame21
  | ⟨12, _⟩ => exact certifiedFrame22
  | ⟨13, _⟩ => exact certifiedFrame23
  | ⟨14, _⟩ => exact certifiedFrame24
  | ⟨15, _⟩ => exact certifiedFrame25
  | ⟨16, _⟩ => exact certifiedFrame26
  | ⟨17, _⟩ => exact certifiedFrame27
  | ⟨18, _⟩ => exact certifiedFrame28
  | ⟨19, _⟩ => exact certifiedFrame29
  | ⟨20, _⟩ => exact certifiedFrame30
  | ⟨21, _⟩ => exact certifiedFrame31
  | ⟨22, _⟩ => exact certifiedFrame32
  | ⟨23, _⟩ => exact certifiedFrame33
  | ⟨24, _⟩ => exact certifiedFrame34
  | ⟨25, _⟩ => exact certifiedFrame35
  | ⟨26, _⟩ => exact certifiedFrame36
  | ⟨27, _⟩ => exact certifiedFrame37
  | ⟨28, _⟩ => exact certifiedFrame38
  | ⟨29, _⟩ => exact certifiedFrame39
  | ⟨30, _⟩ => exact certifiedFrame40
  | ⟨31, _⟩ => exact certifiedFrame41
  | ⟨32, _⟩ => exact certifiedFrame42
  | ⟨33, _⟩ => exact certifiedFrame43
  | ⟨34, _⟩ => exact certifiedFrame44
  | ⟨35, _⟩ => exact certifiedFrame45
  | ⟨36, _⟩ => exact certifiedFrame46
  | ⟨37, _⟩ => exact certifiedFrame47
  | ⟨38, _⟩ => exact certifiedFrame48
  | ⟨39, _⟩ => exact certifiedFrame49
  | ⟨40, _⟩ => exact certifiedFrame50
  | ⟨41, _⟩ => exact certifiedFrame51
  | ⟨42, _⟩ => exact certifiedFrame52
  | ⟨k + 43, h⟩ => omega

theorem certified_frame_lower {i : Fin 60} (hi : needed i) :
    (1.489 : ℝ) ≤ certifiedFrameExpression i := by
  let j : Fin 43 := ⟨i.val - 10, by have := hi.2; omega⟩
  have he : (⟨j.val + 10, by omega⟩ : Fin 60) = i := by
    apply Fin.ext
    dsimp [j]
    have := hi.1
    omega
  rw [← he]
  exact certifiedFrameNeeded j

theorem certified_fixed_frame_fails {i : Fin 60} (hi : needed i) :
    BstLean.Part249.optionBAgentFrame < certifiedFrameExpression i :=
  lt_of_lt_of_le (by norm_num [BstLean.Part249.optionBAgentFrame]) (certified_frame_lower hi)

theorem no_fixed_data_frame {c : BstLean.Part157.Ret 12225}
    (F : LocalFrameInputs BstLean.Part254.cell BstLean.Part254.capTable c
      BstLean.Part249.optionBAgentFrame)
    (hd : F.cutoff = cutoffTable) (hc : F.centreAllowance = centreTable)
    (hm : F.massAllowance = massTable) : False := by
  have h := F.frame_scalar
  rw [hd, hc, hm] at h
  exact (not_le_of_gt (certified_fixed_frame_fails F.index_needed)) h

end BstLean.Part253
