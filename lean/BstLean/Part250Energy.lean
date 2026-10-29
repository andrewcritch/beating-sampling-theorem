import BstLean.Part250Bounds
import BstLean.Part250Frob
/-! Generated rational certificate; every interval step is kernel checked. -/
namespace BstLean.Part250
open Real BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228
open BstLean.Part218 BstLean.Part205 BstLean.Part214
theorem energy : Bounds (e1EnergyLower 24450 (mW 12225) (1/10^6)) (82621245867459650271165643/10000000000000000) (165242491734919300542331291/20000000000000000) := by
  let v0 : ℝ := 24450
  have h0 : Bounds v0 24450 24450 := Bounds.point _
  let v1 : ℝ := 202009148155087
  have h1 : Bounds v1 202009148155087 202009148155087 := Bounds.point _
  let v22 : ℝ := 1
  have h22 : Bounds v22 1 1 := Bounds.point _
  let v242 : ℝ := (1/1000000)
  have h242 : Bounds v242 (1/1000000) (1/1000000) := Bounds.point _
  let v243 : ℝ := -v242
  have h243 : Bounds v243 (-1/1000000) (-1/1000000) := by simpa only [neg_div, neg_neg, neg_zero] using Bounds.neg h242
  let v244 : ℝ := v22+v243
  have h244 : Bounds v244 (999999/1000000) (999999/1000000) := Bounds.add h22 h243 (by norm_num)
  let v245 : ℝ := v244*v1
  have h245 : Bounds v245 (202008946145938844913/1000000) (202008946145938844913/1000000) := Bounds.mul h244 h1 (by norm_num)
  let v246 : ℝ := 1/v0
  have h246 : Bounds v246 (20449897750511247443762781/500000000000000000000000000000) (40899795501022494887525563/1000000000000000000000000000000) := Bounds.inv h0 (by norm_num)
  let v247 : ℝ := v245/v0
  have h247 : Bounds v247 (82621245867459650271165643/10000000000000000) (165242491734919300542331291/20000000000000000) := bounds_div h245 h246 (by norm_num)
  convert h247 using 1 <;>
    simp only [v0, v1, v22, v242, v243, v244, v245, v247, e1EnergyLower, width] <;>
      norm_num [Finset.sum_range_succ, Finset.prod_range_succ, Nat.doubleFactorial, Nat.choose] <;> ring
end BstLean.Part250
#print axioms BstLean.Part250.energy
