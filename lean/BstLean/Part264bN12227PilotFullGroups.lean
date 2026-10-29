import BstLean.Part264bN12227PilotGroups

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12227
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12227 cell12227)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.087013654173
  | 2 => 0.087987927416
  | 3 => 0.088965482886
  | 4 => 0.089948877288
  | 5 => 0.090941157477
  | 6 => 0.091945927073
  | 7 => 0.092967418271
  | 8 => 0.094010568682
  | _ => 0

theorem pilot_fullGroup1 :
    fullFormula 12227 12227 0.011 1.22 1.12 0.46 (groupTheta 1)
      (groupProfile 1) 1.22 ≤ pilotGroupCentre 1 := by
  apply pilot_full_formula_bound (X := (0.220639803866 : ℝ)) (T := (0.760762628683 : ℝ)) (R := (0.011177571944 : ℝ))
    <;> norm_num [groupTheta,groupProfile,pilotGroupCentre]

theorem pilot_fullGroup2 :
    fullFormula 12227 12227 0.011 1.22 1.12 0.46 (groupTheta 2)
      (groupProfile 2) 1.22 ≤ pilotGroupCentre 2 := by
  apply pilot_full_formula_bound (X := (0.222201701266 : ℝ)) (T := (0.766511359721 : ℝ)) (R := (0.011294751462 : ℝ))
    <;> norm_num [groupTheta,groupProfile,pilotGroupCentre]

theorem pilot_fullGroup3 :
    fullFormula 12227 12227 0.011 1.22 1.12 0.46 (groupTheta 3)
      (groupProfile 3) 1.22 ≤ pilotGroupCentre 3 := by
  apply pilot_full_formula_bound (X := (0.223743357533 : ℝ)) (T := (0.772217296608 : ℝ)) (R := (0.011411543944 : ℝ))
    <;> norm_num [groupTheta,groupProfile,pilotGroupCentre]

theorem pilot_fullGroup4 :
    fullFormula 12227 12227 0.011 1.22 1.12 0.46 (groupTheta 4)
      (groupProfile 4) 1.22 ≤ pilotGroupCentre 4 := by
  apply pilot_full_formula_bound (X := (0.225264972345 : ℝ)) (T := (0.777881379492 : ℝ)) (R := (0.011527957877 : ℝ))
    <;> norm_num [groupTheta,groupProfile,pilotGroupCentre]

theorem pilot_fullGroup5 :
    fullFormula 12227 12227 0.011 1.22 1.12 0.46 (groupTheta 5)
      (groupProfile 5) 1.22 ≤ pilotGroupCentre 5 := by
  apply pilot_full_formula_bound (X := (0.226766740586 : ℝ)) (T := (0.783504517639 : ℝ)) (R := (0.011644001502 : ℝ))
    <;> norm_num [groupTheta,groupProfile,pilotGroupCentre]

theorem pilot_fullGroup6 :
    fullFormula 12227 12227 0.011 1.22 1.12 0.46 (groupTheta 6)
      (groupProfile 6) 1.22 ≤ pilotGroupCentre 6 := by
  apply pilot_full_formula_bound (X := (0.228248850835 : ℝ)) (T := (0.789087584835 : ℝ)) (R := (0.011759682703 : ℝ))
    <;> norm_num [groupTheta,groupProfile,pilotGroupCentre]

theorem pilot_fullGroup7 :
    fullFormula 12227 12227 0.011 1.22 1.12 0.46 (groupTheta 7)
      (groupProfile 7) 1.22 ≤ pilotGroupCentre 7 := by
  apply pilot_full_formula_bound (X := (0.229711487216 : ℝ)) (T := (0.794631427230 : ℝ)) (R := (0.011875009153 : ℝ))
    <;> norm_num [groupTheta,groupProfile,pilotGroupCentre]

theorem pilot_fullGroup8 :
    fullFormula 12227 12227 0.011 1.22 1.12 0.46 (groupTheta 8)
      (groupProfile 8) 1.22 ≤ pilotGroupCentre 8 := by
  apply pilot_full_formula_bound (X := (0.231154827920 : ℝ)) (T := (0.800136858619 : ℝ)) (R := (0.011989988192 : ℝ))
    <;> norm_num [groupTheta,groupProfile,pilotGroupCentre]

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12227 12227 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => exact pilot_fullGroup1
  | ⟨2,h⟩ => exact pilot_fullGroup2
  | ⟨3,h⟩ => exact pilot_fullGroup3
  | ⟨4,h⟩ => exact pilot_fullGroup4
  | ⟨5,h⟩ => exact pilot_fullGroup5
  | ⟨6,h⟩ => exact pilot_fullGroup6
  | ⟨7,h⟩ => exact pilot_fullGroup7
  | ⟨8,h⟩ => exact pilot_fullGroup8
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part264b.N12227
