import BstLean.Part253CentreFormula
import BstLean.Part253Data

/-! The full-centre formula fits the enlarged local allowances. -/
namespace BstLean.Part253
open Real Set BstLean.Part211

theorem fullCentreGroup1 :
    fullFormula 12225 12225 0.011 1.22 1.12 0.46 0.474393260 0.161707182529 1.22 ≤
      centreTable 1 + 0.0015 := by
  apply full_formula_bound (X := (0.220639803866 : ℝ)) (T := (0.760762628683 : ℝ)) (R := (0.011177571944 : ℝ))
    <;> norm_num [centreTable]

theorem fullCentreGroup2 :
    fullFormula 12225 12225 0.011 1.22 1.12 0.46 0.481589889 0.164220346040 1.22 ≤
      centreTable 2 + 0.0015 := by
  apply full_formula_bound (X := (0.222201701266 : ℝ)) (T := (0.766511359721 : ℝ)) (R := (0.011294751462 : ℝ))
    <;> norm_num [centreTable]

theorem fullCentreGroup3 :
    fullFormula 12225 12225 0.011 1.22 1.12 0.46 0.488786519 0.166717763490 1.22 ≤
      centreTable 3 + 0.0015 := by
  apply full_formula_bound (X := (0.223743357533 : ℝ)) (T := (0.772217296608 : ℝ)) (R := (0.011411543944 : ℝ))
    <;> norm_num [centreTable]

theorem fullCentreGroup4 :
    fullFormula 12225 12225 0.011 1.22 1.12 0.46 0.495983148 0.169199068410 1.22 ≤
      centreTable 4 + 0.0015 := by
  apply full_formula_bound (X := (0.225264972345 : ℝ)) (T := (0.777881379492 : ℝ)) (R := (0.011527957877 : ℝ))
    <;> norm_num [centreTable]

theorem fullCentreGroup5 :
    fullFormula 12225 12225 0.011 1.22 1.12 0.46 0.503179778 0.171663904382 1.22 ≤
      centreTable 5 + 0.0015 := by
  apply full_formula_bound (X := (0.226766740586 : ℝ)) (T := (0.783504517639 : ℝ)) (R := (0.011644001502 : ℝ))
    <;> norm_num [centreTable]

theorem fullCentreGroup6 :
    fullFormula 12225 12225 0.011 1.22 1.12 0.46 0.510376407 0.174111921985 1.22 ≤
      centreTable 6 + 0.0015 := by
  apply full_formula_bound (X := (0.228248850835 : ℝ)) (T := (0.789087584835 : ℝ)) (R := (0.011759682703 : ℝ))
    <;> norm_num [centreTable]

theorem fullCentreGroup7 :
    fullFormula 12225 12225 0.011 1.22 1.12 0.46 0.517573037 0.176542781247 1.22 ≤
      centreTable 7 + 0.0015 := by
  apply full_formula_bound (X := (0.229711487216 : ℝ)) (T := (0.794631427230 : ℝ)) (R := (0.011875009153 : ℝ))
    <;> norm_num [centreTable]

theorem fullCentreGroup8 :
    fullFormula 12225 12225 0.011 1.22 1.12 0.46 0.524769666 0.178956148662 1.22 ≤
      centreTable 8 + 0.0015 := by
  apply full_formula_bound (X := (0.231154827920 : ℝ)) (T := (0.800136858619 : ℝ)) (R := (0.011989988192 : ℝ))
    <;> norm_num [centreTable]

end BstLean.Part253
