import BstLean.Part250Bounds
import BstLean.Part250Jfourth
/-! Generated rational certificate; every interval step is kernel checked. -/
namespace BstLean.Part250
open Real BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228
open BstLean.Part218 BstLean.Part205 BstLean.Part214
theorem covmean : Bounds (covarianceMeanBound 24450 (mW 12225)) (57847062917328758476210317/10000000000000000) (34710545408099487393704187/4000000000000000) := by
  let v1 : ℝ := 202009148155087
  have h1 : Bounds v1 202009148155087 202009148155087 := Bounds.point _
  let v22 : ℝ := 1
  have h22 : Bounds v22 1 1 := Bounds.point _
  let v41 : ℝ := 4
  have h41 : Bounds v41 4 4 := Bounds.point _
  let v203 : ℝ := v1*v41
  have h203 : Bounds v203 808036592620348 808036592620348 := Bounds.mul h1 h41 (by norm_num)
  let v204 : ℝ := -v22
  have h204 : Bounds v204 (-1) (-1) := by simpa only [neg_div, neg_neg, neg_zero] using Bounds.neg h22
  let v205 : ℝ := v1+v204
  have h205 : Bounds v205 202009148155086 202009148155086 := Bounds.add h1 h204 (by norm_num)
  let v206 : ℝ := v203*v205
  have h206 : Bounds v206 163230783753374749946623289000 163230783753374749946623290000 := Bounds.mul h203 h205 (by norm_num)
  let v207 : ℝ := v206*(angularJ2 24450 (angularOffset 24450))
  have h207 : Bounds v207 (57847062917328758476210317/10000000000000000) (34710545408099487393704187/4000000000000000) := Bounds.mul h206 jsecond (by norm_num)
  convert h207 using 1 <;>
    simp only [v1, v22, v41, v203, v204, v205, v206, v207, covarianceMeanBound, width] <;>
      norm_num [Finset.sum_range_succ, Finset.prod_range_succ, Nat.doubleFactorial, Nat.choose] <;> ring
end BstLean.Part250
#print axioms BstLean.Part250.covmean
