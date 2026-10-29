import BstLean.Part253Scalar

/-! A small cutoff reduction pays for a larger centre-energy allowance. -/
namespace BstLean.Part253
open Real

noncomputable def retunedEnergy (i : Fin 60) : ℝ := energyTable i + 0.0005
noncomputable def retunedCentre (g : Fin 10) : ℝ := centreTable g + 0.0015
noncomputable def retunedCutoff (i : Fin 60) : ℝ := cutoffTable i - 0.0007

theorem retuned_gap_le {E W xi : ℝ} (hE : 0.64 ≤ E) (hW : 0 ≤ W) (hW1 : W ≤ 1) :
    √W - (√E + √xi) ≤ √(W + 0.0007) - (√(E + 0.0005) + √xi) := by
  have hsW : √W ≤ 1 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hsW0 := sqrt_nonneg W
  have hsE : (0.8 : ℝ) ≤ √E := le_sqrt_of_sq_le (by linarith)
  have heqW := sq_sqrt hW
  have heqE := sq_sqrt (by linarith : 0 ≤ E)
  have h1 : √W + 0.00034 ≤ √(W + 0.0007) := le_sqrt_of_sq_le (by nlinarith)
  have h2 : √(E + 0.0005) ≤ √E + 0.000324 :=
    sqrt_le_iff.mpr ⟨by positivity, by nlinarith⟩
  linarith

theorem retuned_gap {i : Fin 60} (hi : needed i) (hE : 0.64 ≤ energyTable i) :
    √((1 - radiusCutoff) ^ 2 - cutoffTable i) - (√(energyTable i) + √(parallelCap / 12225)) ≤
      √((1 - radiusCutoff) ^ 2 - retunedCutoff i) -
        (√(retunedEnergy i) + √(parallelCap / 12225)) := by
  have S := scalar_on_needed hi
  have hW : 0 ≤ (1 - radiusCutoff) ^ 2 - cutoffTable i := by linarith [S.cutoff_lt]
  have hW1 : (1 - radiusCutoff) ^ 2 - cutoffTable i ≤ 1 := by
    have hd := S.cutoff_pos
    norm_num [radiusCutoff] at *
    linarith
  have h := retuned_gap_le (xi := parallelCap / 12225) hE hW hW1
  have he : (1 - radiusCutoff) ^ 2 - retunedCutoff i =
      ((1 - radiusCutoff) ^ 2 - cutoffTable i) + 0.0007 := by
    unfold retunedCutoff
    ring
  rw [he]
  exact h

theorem retuned_mass {i : Fin 60} (hi : needed i) (hE : 0.64 ≤ energyTable i) :
    BstLean.Part222.massBoundOrder 12225 12 directionCap energyCap parallelCap
      (retunedEnergy i) radiusCutoff (retunedCutoff i) ≤ massTable i := by
  have S := scalar_on_needed hi
  have hg := retuned_gap hi hE
  have hgap := S.gap_pos
  have hrot := BstLean.Part195.rotationConstant_nonneg 12
  apply le_trans ?_ S.mass_scalar
  unfold BstLean.Part222.massBoundOrder
  simp only [Nat.cast_ofNat, Nat.reduceMul]
  gcongr

structure RetunedDataCertificate (i : Fin 60) : Prop where
  energy_lower : 0.64 ≤ energyTable i
  energy_upper : retunedEnergy i ≤ 1
  cutoff_pos : 0 < retunedCutoff i
  frame_scalar : (capTable i + retunedCentre (centreGroup i)) / retunedCutoff i +
    massTable i ≤ BstLean.Part249.optionBAgentFrame

end BstLean.Part253
