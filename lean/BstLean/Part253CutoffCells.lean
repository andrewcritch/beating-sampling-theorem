import BstLean.Part253CutoffCert10
import BstLean.Part253CutoffCert16
import BstLean.Part253CutoffCert22
import BstLean.Part253CutoffCert28
import BstLean.Part253CutoffCert34
import BstLean.Part253CutoffCert40
import BstLean.Part253CutoffCert46
import BstLean.Part253CutoffCert52

/-! All needed cells reject arbitrary cutoffs and mass allowances. -/
namespace BstLean.Part253
open Real

theorem allCutoffsNeeded (j : Fin 43) {d : ℝ} (hd : 0 < d)
    (hgap : 0 < √((1 - radiusCutoff) ^ 2 - d) -
      (√(energyTable ⟨j.val + 10, by omega⟩) + √(parallelCap / 12225))) :
    (1.4601 : ℝ) ≤ certifiedNumerator ⟨j.val + 10, by omega⟩ / d +
      BstLean.Part222.massBoundOrder 12225 12 directionCap energyCap parallelCap
        (energyTable ⟨j.val + 10, by omega⟩) radiusCutoff d := by
  match j with
  | ⟨0, _⟩ => exact allCutoffsCell10 hd hgap
  | ⟨1, _⟩ => exact allCutoffsCell11 hd hgap
  | ⟨2, _⟩ => exact allCutoffsCell12 hd hgap
  | ⟨3, _⟩ => exact allCutoffsCell13 hd hgap
  | ⟨4, _⟩ => exact allCutoffsCell14 hd hgap
  | ⟨5, _⟩ => exact allCutoffsCell15 hd hgap
  | ⟨6, _⟩ => exact allCutoffsCell16 hd hgap
  | ⟨7, _⟩ => exact allCutoffsCell17 hd hgap
  | ⟨8, _⟩ => exact allCutoffsCell18 hd hgap
  | ⟨9, _⟩ => exact allCutoffsCell19 hd hgap
  | ⟨10, _⟩ => exact allCutoffsCell20 hd hgap
  | ⟨11, _⟩ => exact allCutoffsCell21 hd hgap
  | ⟨12, _⟩ => exact allCutoffsCell22 hd hgap
  | ⟨13, _⟩ => exact allCutoffsCell23 hd hgap
  | ⟨14, _⟩ => exact allCutoffsCell24 hd hgap
  | ⟨15, _⟩ => exact allCutoffsCell25 hd hgap
  | ⟨16, _⟩ => exact allCutoffsCell26 hd hgap
  | ⟨17, _⟩ => exact allCutoffsCell27 hd hgap
  | ⟨18, _⟩ => exact allCutoffsCell28 hd hgap
  | ⟨19, _⟩ => exact allCutoffsCell29 hd hgap
  | ⟨20, _⟩ => exact allCutoffsCell30 hd hgap
  | ⟨21, _⟩ => exact allCutoffsCell31 hd hgap
  | ⟨22, _⟩ => exact allCutoffsCell32 hd hgap
  | ⟨23, _⟩ => exact allCutoffsCell33 hd hgap
  | ⟨24, _⟩ => exact allCutoffsCell34 hd hgap
  | ⟨25, _⟩ => exact allCutoffsCell35 hd hgap
  | ⟨26, _⟩ => exact allCutoffsCell36 hd hgap
  | ⟨27, _⟩ => exact allCutoffsCell37 hd hgap
  | ⟨28, _⟩ => exact allCutoffsCell38 hd hgap
  | ⟨29, _⟩ => exact allCutoffsCell39 hd hgap
  | ⟨30, _⟩ => exact allCutoffsCell40 hd hgap
  | ⟨31, _⟩ => exact allCutoffsCell41 hd hgap
  | ⟨32, _⟩ => exact allCutoffsCell42 hd hgap
  | ⟨33, _⟩ => exact allCutoffsCell43 hd hgap
  | ⟨34, _⟩ => exact allCutoffsCell44 hd hgap
  | ⟨35, _⟩ => exact allCutoffsCell45 hd hgap
  | ⟨36, _⟩ => exact allCutoffsCell46 hd hgap
  | ⟨37, _⟩ => exact allCutoffsCell47 hd hgap
  | ⟨38, _⟩ => exact allCutoffsCell48 hd hgap
  | ⟨39, _⟩ => exact allCutoffsCell49 hd hgap
  | ⟨40, _⟩ => exact allCutoffsCell50 hd hgap
  | ⟨41, _⟩ => exact allCutoffsCell51 hd hgap
  | ⟨42, _⟩ => exact allCutoffsCell52 hd hgap
  | ⟨k + 43, h⟩ => omega

theorem all_cutoffs_on_needed {i : Fin 60} (hi : needed i) {d : ℝ} (hd : 0 < d)
    (hgap : 0 < √((1 - radiusCutoff) ^ 2 - d) -
      (√(energyTable i) + √(parallelCap / 12225))) :
    (1.4601 : ℝ) ≤ certifiedNumerator i / d +
      BstLean.Part222.massBoundOrder 12225 12 directionCap energyCap parallelCap
        (energyTable i) radiusCutoff d := by
  let j : Fin 43 := ⟨i.val - 10, by have := hi.2; omega⟩
  have he : (⟨j.val + 10, by omega⟩ : Fin 60) = i := by
    apply Fin.ext
    dsimp [j]
    have := hi.1
    omega
  rw [← he] at *
  exact allCutoffsNeeded j hd hgap

/-- Any charged mass allowance fails, even when each cell chooses its cutoff. -/
theorem no_arbitrary_cutoff_frame {i : Fin 60} (hi : needed i) {d beta : ℝ}
    (hd : 0 < d)
    (hgap : 0 < √((1 - radiusCutoff) ^ 2 - d) -
      (√(energyTable i) + √(parallelCap / 12225)))
    (hmass : BstLean.Part222.massBoundOrder 12225 12 directionCap energyCap
      parallelCap (energyTable i) radiusCutoff d ≤ beta)
    (hframe : certifiedNumerator i / d + beta ≤ BstLean.Part249.optionBAgentFrame) :
    False := by
  have h := all_cutoffs_on_needed hi hd hgap
  norm_num [BstLean.Part249.optionBAgentFrame] at hframe
  linarith

end BstLean.Part253
