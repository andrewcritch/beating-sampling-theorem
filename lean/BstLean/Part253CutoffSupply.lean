import BstLean.Part253CutoffCells

/-! Larger centre and energy allowances preserve the cutoff obstruction. -/
namespace BstLean.Part253
open Real

theorem mass_energy_mono {E E' d : ℝ} (hE : E ≤ E')
    (hgap : 0 < √((1 - radiusCutoff) ^ 2 - d) -
      (√E' + √(parallelCap / 12225))) :
    BstLean.Part222.massBoundOrder 12225 12 directionCap energyCap parallelCap
      E radiusCutoff d ≤
    BstLean.Part222.massBoundOrder 12225 12 directionCap energyCap parallelCap
      E' radiusCutoff d := by
  have hs := sqrt_le_sqrt hE
  have hg : 0 < √((1 - radiusCutoff) ^ 2 - d) -
      (√E + √(parallelCap / 12225)) := by linarith
  have hr := BstLean.Part195.rotationConstant_nonneg 12
  have hM : 0 ≤ directionCap := by norm_num [directionCap]
  unfold BstLean.Part222.massBoundOrder
  norm_num only [Nat.cast_ofNat, Nat.reduceMul]
  gcongr

/-- Cutoff and mass tables are arbitrary. The optimistic source allowances
already fail, so larger supplied allowances fail as well. -/
theorem no_supplied_frame_with_arbitrary_cutoffs
    {c : BstLean.Part157.Ret 12225}
    (F : LocalFrameInputs BstLean.Part254.cell BstLean.Part254.capTable c
      BstLean.Part249.optionBAgentFrame)
    (hp : F.order = 12) (hM : F.M = directionCap) (hH : F.H = energyCap)
    (hxi : F.xiP = parallelCap) (hu : F.u = radiusCutoff)
    (hE : energyTable F.index ≤ F.E)
    (hC : centreTable (centreGroup F.index) ≤ F.centreAllowance (centreGroup F.index)) :
    False := by
  have hgap := F.gap_pos
  rw [hu, hxi] at hgap
  have hs := sqrt_le_sqrt hE
  have hg : 0 < √((1 - radiusCutoff) ^ 2 - F.cutoff F.index) -
      (√(energyTable F.index) + √(parallelCap / 12225)) := by linarith
  have hm := F.mass_scalar
  rw [hp, hM, hH, hxi, hu] at hm
  have hm' := (mass_energy_mono hE hgap).trans hm
  have hquot : certifiedNumerator F.index / F.cutoff F.index ≤
      (BstLean.Part254.capTable F.index + F.centreAllowance (centreGroup F.index)) /
        F.cutoff F.index := by
    unfold certifiedNumerator
    exact div_le_div_of_nonneg_right (by linarith) F.cutoff_pos.le
  exact no_arbitrary_cutoff_frame F.index_needed F.cutoff_pos hg hm'
    (by have := F.frame_scalar; linarith)

end BstLean.Part253
