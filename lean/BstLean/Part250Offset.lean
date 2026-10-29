import BstLean.Part250Bounds
import BstLean.Part250Endpoint
/-! Generated rational certificate; every interval step is kernel checked. -/
namespace BstLean.Part250
open Real BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228
open BstLean.Part218 BstLean.Part205 BstLean.Part214
theorem offset : Bounds (angularOffset 24450) (-2662442073473513257221/10000000000000000000000000000000) (207201/10000000000000000000000000000000) := by
  let v0 : ℝ := 24450
  have h0 : Bounds v0 24450 24450 := Bounds.point _
  let v2 : ℝ := 2
  have h2 : Bounds v2 2 2 := Bounds.point _
  let v22 : ℝ := 1
  have h22 : Bounds v22 1 1 := Bounds.point _
  let v35 : ℝ := π*v2
  have h35 : Bounds v35 (157079632679489661923/25000000000000000000) (314159265358979323847/50000000000000000000) := Bounds.mul pi_bounds h2 (by norm_num)
  let v36 : ℝ := v35*v0
  have h36 : Bounds v36 (76811940380270444680347/500000000000000000) (153623880760540889361183/1000000000000000000) := Bounds.mul h35 h0 (by norm_num)
  let v37 : ℝ := 1/v36
  have h37 : Bounds v37 (6509404625435392055971823/1000000000000000000000000000000) (65094046254353920559925431/10000000000000000000000000000000) := Bounds.inv h36 (by norm_num)
  let v38 : ℝ := v22/v36
  have h38 : Bounds v38 (6509404625435392055971823/1000000000000000000000000000000) (65094046254353920559925431/10000000000000000000000000000000) := bounds_div h22 h37 (by norm_num)
  let v39 : ℝ := -(BstLean.Part137.cN 24450 ^ 2)
  have h39 : Bounds v39 (-65096708696427394072975451/10000000000000000000000000000000) (-6509404625435392055971823/1000000000000000000000000000000) := by simpa only [neg_div, neg_neg, neg_zero] using Bounds.neg cnsq_bounds
  let v40 : ℝ := v38+v39
  have h40 : Bounds v40 (-2662442073473513257221/10000000000000000000000000000000) (207201/10000000000000000000000000000000) := Bounds.add h38 h39 (by norm_num)
  convert h40 using 1 <;>
    simp only [v0, v2, v22, v35, v36, v38, v39, v40, angularOffset, width] <;>
      norm_num [Finset.sum_range_succ, Finset.prod_range_succ, Nat.doubleFactorial, Nat.choose] <;> ring
end BstLean.Part250
#print axioms BstLean.Part250.offset
