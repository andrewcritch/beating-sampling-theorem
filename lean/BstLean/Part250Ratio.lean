import BstLean.Part250Bounds
import BstLean.Part250Kernel
/-! Generated rational certificate; every interval step is kernel checked. -/
namespace BstLean.Part250
open Real BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228
open BstLean.Part218 BstLean.Part205 BstLean.Part214
theorem ratio : Bounds (firstRatio 24450) (4973591971621729242765971/15625000000000000000000000) (79580726381382489254212489/250000000000000000000000000) := by
  let v0 : ℝ := 24450
  have h0 : Bounds v0 24450 24450 := Bounds.point _
  let v2 : ℝ := 2
  have h2 : Bounds v2 2 2 := Bounds.point _
  let v3 : ℝ := v0*v2
  have h3 : Bounds v3 48900 48900 := Bounds.mul h0 h2 (by norm_num)
  let v4 : ℝ := v3*(BstLean.Part137.cN 24450 ^ 2)
  have h4 : Bounds v4 (4973591971621729242765971/15625000000000000000000000) (79580726381382489254212489/250000000000000000000000000) := Bounds.mul h3 cnsq_bounds (by norm_num)
  convert h4 using 1 <;>
    simp only [v0, v2, v3, v4, firstRatio, width] <;>
      norm_num [Finset.sum_range_succ, Finset.prod_range_succ, Nat.doubleFactorial, Nat.choose] <;> ring
end BstLean.Part250
#print axioms BstLean.Part250.ratio
