import BstLean.Part250Bounds
import BstLean.Part250Direction
/-! Generated rational certificate; every interval step is kernel checked. -/
namespace BstLean.Part250
open Real BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228
open BstLean.Part218 BstLean.Part205 BstLean.Part214
theorem inputvar : Bounds (e1InputVarianceBound 24450 (mW 12225) rowEps) (675996988178446678749440571/100000000000000000000) (168999247044611669687360159/25000000000000000000) := by
  let v0 : ℝ := 24450
  have h0 : Bounds v0 24450 24450 := Bounds.point _
  let v1 : ℝ := 202009148155087
  have h1 : Bounds v1 202009148155087 202009148155087 := Bounds.point _
  let v2 : ℝ := 2
  have h2 : Bounds v2 2 2 := Bounds.point _
  let v13 : ℝ := 3
  have h13 : Bounds v13 3 3 := Bounds.point _
  let v22 : ℝ := 1
  have h22 : Bounds v22 1 1 := Bounds.point _
  let v230 : ℝ := (1/1000)
  have h230 : Bounds v230 (1/1000) (1/1000) := Bounds.point _
  let v260 : ℝ := v230+v22
  have h260 : Bounds v260 (1001/1000) (1001/1000) := Bounds.add h230 h22 (by norm_num)
  let v261 : ℝ := v260+v13
  have h261 : Bounds v261 (4001/1000) (4001/1000) := Bounds.add h260 h13 (by norm_num)
  let v262 : ℝ := 5
  have h262 : Bounds v262 5 5 := Bounds.point _
  let v263 : ℝ := v1*v262
  have h263 : Bounds v263 1010045740775435 1010045740775435 := Bounds.mul h1 h262 (by norm_num)
  let v264 : ℝ := v0^2
  have h264 : Bounds v264 597802500 597802500 := Bounds.pow h0 2 (by norm_num)
  let v265 : ℝ := 1/v264
  have h265 : Bounds v265 (8363966360127299568001137/5000000000000000000000000000000000) (669117308810183965440091/400000000000000000000000000000000) := Bounds.inv h264 (by norm_num)
  let v266 : ℝ := v263/v264
  have h266 : Bounds v266 (6758390878428477632662961/4000000000000000000) (4223994299017798520414351/2500000000000000000) := bounds_div h263 h265 (by norm_num)
  let v267 : ℝ := v1*v2
  have h267 : Bounds v267 404018296310174 404018296310174 := Bounds.mul h1 h2 (by norm_num)
  let v268 : ℝ := v0^3
  have h268 : Bounds v268 14616271125000 14616271125000 := Bounds.pow h0 3 (by norm_num)
  let v269 : ℝ := 1/v268
  have h269 : Bounds v269 (68416902741327603828230163/1000000000000000000000000000000000000000) (17104225685331900957057541/250000000000000000000000000000000000000) := Bounds.inv h268 (by norm_num)
  let v270 : ℝ := v267/v268
  have h270 : Bounds v270 (1105667219374802066693327/40000000000000000000000) (138208402421850258336665879/5000000000000000000000000) := bounds_div h267 h269 (by norm_num)
  let v271 : ℝ := -v270
  have h271 : Bounds v271 (-138208402421850258336665879/5000000000000000000000000) (-1105667219374802066693327/40000000000000000000000) := by simpa only [neg_div, neg_neg, neg_zero] using Bounds.neg h270
  let v272 : ℝ := v266+v271
  have h272 : Bounds v272 (168957007792663503811407291/100000000000000000000) (168957007792663503811407307/100000000000000000000) := Bounds.add h266 h271 (by norm_num)
  let v273 : ℝ := v261*v272
  have h273 : Bounds v273 (675996988178446678749440571/100000000000000000000) (168999247044611669687360159/25000000000000000000) := Bounds.mul h261 h272 (by norm_num)
  convert h273 using 1 <;>
    simp only [v0, v1, v2, v13, v22, v230, v260, v261, v262, v263, v264, v266, v267, v268, v270, v271, v272, v273, e1InputVarianceBound, inputVarianceMean, rowEps, Matrix.cons_val_one, Matrix.cons_val_three, width] <;>
      norm_num [Finset.sum_range_succ, Finset.prod_range_succ, Nat.doubleFactorial, Nat.choose] <;> ring
end BstLean.Part250
#print axioms BstLean.Part250.inputvar
