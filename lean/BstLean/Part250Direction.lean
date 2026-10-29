import BstLean.Part250Bounds
import BstLean.Part250Energy
/-! Generated rational certificate; every interval step is kernel checked. -/
namespace BstLean.Part250
open Real BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228
open BstLean.Part218 BstLean.Part205 BstLean.Part214
theorem direction : Bounds (directionMean 24450 (mW 12225)) (73329320815573009917869563/1000000000000000000000) (4583357541592011931182071/62500000000000000000) := by
  let v0 : ℝ := 24450
  have h0 : Bounds v0 24450 24450 := Bounds.point _
  let v1 : ℝ := 202009148155087
  have h1 : Bounds v1 202009148155087 202009148155087 := Bounds.point _
  let v2 : ℝ := 2
  have h2 : Bounds v2 2 2 := Bounds.point _
  let v22 : ℝ := 1
  have h22 : Bounds v22 1 1 := Bounds.point _
  let v248 : ℝ := v1*v2
  have h248 : Bounds v248 404018296310174 404018296310174 := Bounds.mul h1 h2 (by norm_num)
  let v249 : ℝ := v248*(BstLean.Part137.cN 24450 ^ 2)
  have h249 : Bounds v249 (13149592833809867134177349/5000000000000000) (1643766333933142722768107/625000000000000) := Bounds.mul h248 cnsq_bounds (by norm_num)
  let v250 : ℝ := v0+v2
  have h250 : Bounds v250 24452 24452 := Bounds.add h0 h2 (by norm_num)
  let v251 : ℝ := v249*v250
  have h251 : Bounds v251 (25722707517785509693192363/400000000000) (16077349758933282342850301/250000000000) := Bounds.mul h249 h250 (by norm_num)
  let v252 : ℝ := v0^2
  have h252 : Bounds v252 597802500 597802500 := Bounds.pow h0 2 (by norm_num)
  let v253 : ℝ := 1/v252
  have h253 : Bounds v253 (8363966360127299568001137/5000000000000000000000000000000000) (669117308810183965440091/400000000000000000000000000000000) := Bounds.inv h252 (by norm_num)
  let v254 : ℝ := v251/v252
  have h254 : Bounds v254 (107571930185075797162074269/1000000000000000000000) (107576330034974978143117843/1000000000000000000000) := bounds_div h251 h253 (by norm_num)
  let v255 : ℝ := v0*v2
  have h255 : Bounds v255 48900 48900 := Bounds.mul h0 h2 (by norm_num)
  let v256 : ℝ := v255*(BstLean.Part137.cN 24450 ^ 2)
  have h256 : Bounds v256 (4973591971621729242765971/15625000000000000000000000) (79580726381382489254212489/250000000000000000000000000) := Bounds.mul h255 cnsq_bounds (by norm_num)
  let v257 : ℝ := -v256
  have h257 : Bounds v257 (-79580726381382489254212489/250000000000000000000000000) (-4973591971621729242765971/15625000000000000000000000) := by simpa only [neg_div, neg_neg, neg_zero] using Bounds.neg h256
  let v258 : ℝ := v22+v257
  have h258 : Bounds v258 (17041927361861751074578751/25000000000000000000000000) (34084505690810466423148893/50000000000000000000000000) := Bounds.add h22 h257 (by norm_num)
  let v259 : ℝ := v254*v258
  have h259 : Bounds v259 (73329320815573009917869563/1000000000000000000000) (4583357541592011931182071/62500000000000000000) := Bounds.mul h254 h258 (by norm_num)
  convert h259 using 1 <;>
    simp only [v0, v1, v2, v22, v248, v249, v250, v251, v252, v254, v255, v256, v257, v258, v259, directionMean, width] <;>
      norm_num [Finset.sum_range_succ, Finset.prod_range_succ, Nat.doubleFactorial, Nat.choose] <;> ring <;> simp
end BstLean.Part250
#print axioms BstLean.Part250.direction
