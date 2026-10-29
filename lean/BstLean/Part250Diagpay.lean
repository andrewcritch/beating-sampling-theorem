import BstLean.Part250Bounds
import BstLean.Part250Tracepay
/-! Generated rational certificate; every interval step is kernel checked. -/
namespace BstLean.Part250
open Real BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228
open BstLean.Part218 BstLean.Part205 BstLean.Part214
theorem diagpay : Bounds (8*(mW 12225 : ℝ)*24450*(24450+2)*(24450+3) / ((1/1000)*((mW 12225 : ℝ)*24450*(24450+2)))^2) (80989338415646251983470717/50000000000000000000000000000000000000) (126545841274447268724173/78125000000000000000000000000000000) := by
  let v0 : ℝ := 24450
  have h0 : Bounds v0 24450 24450 := Bounds.point _
  let v1 : ℝ := 202009148155087
  have h1 : Bounds v1 202009148155087 202009148155087 := Bounds.point _
  let v2 : ℝ := 2
  have h2 : Bounds v2 2 2 := Bounds.point _
  let v13 : ℝ := 3
  have h13 : Bounds v13 3 3 := Bounds.point _
  let v230 : ℝ := (1/1000)
  have h230 : Bounds v230 (1/1000) (1/1000) := Bounds.point _
  let v353 : ℝ := 8
  have h353 : Bounds v353 8 8 := Bounds.point _
  let v387 : ℝ := v1*v353
  have h387 : Bounds v387 1616073185240696 1616073185240696 := Bounds.mul h1 h353 (by norm_num)
  let v388 : ℝ := v387*v0
  have h388 : Bounds v388 39512989379135017200 39512989379135017200 := Bounds.mul h387 h0 (by norm_num)
  let v389 : ℝ := v0+v2
  have h389 : Bounds v389 24452 24452 := Bounds.add h0 h2 (by norm_num)
  let v390 : ℝ := v388*v389
  have h390 : Bounds v390 966171616298609440574400 966171616298609440574400 := Bounds.mul h388 h389 (by norm_num)
  let v391 : ℝ := v0+v13
  have h391 : Bounds v391 24453 24453 := Bounds.add h0 h13 (by norm_num)
  let v392 : ℝ := v390*v391
  have h392 : Bounds v392 23625794533349896650365803200 23625794533349896650365803200 := Bounds.mul h390 h391 (by norm_num)
  let v393 : ℝ := v1*v0
  have h393 : Bounds v393 4939123672391877150 4939123672391877150 := Bounds.mul h1 h0 (by norm_num)
  let v394 : ℝ := v0+v2
  have h394 : Bounds v394 24452 24452 := Bounds.add h0 h2 (by norm_num)
  let v395 : ℝ := v393*v394
  have h395 : Bounds v395 120771452037326180071800 120771452037326180071800 := Bounds.mul h393 h394 (by norm_num)
  let v396 : ℝ := v230*v395
  have h396 : Bounds v396 (603857260186630900359/5) (603857260186630900359/5) := Bounds.mul h230 h395 (by norm_num)
  let v397 : ℝ := v396^2
  have h397 : Bounds v397 14585743627204177931162744200000000000000 14585743627204177931162744300000000000000 := Bounds.pow h396 2 (by norm_num)
  let v398 : ℝ := 1/v397
  have h398 : Bounds v398 (13712019428819233025791091/200000000000000000000000000000000000000000000000000000000000000000) (68560097144096165128955457/1000000000000000000000000000000000000000000000000000000000000000000) := Bounds.inv h397 (by norm_num)
  let v399 : ℝ := v392/v397
  have h399 : Bounds v399 (80989338415646251983470717/50000000000000000000000000000000000000) (126545841274447268724173/78125000000000000000000000000000000) := bounds_div h392 h398 (by norm_num)
  convert h399 using 1 <;>
    simp only [v0, v1, v2, v13, v230, v353, v387, v388, v389, v390, v391, v392, v393, v394, v395, v396, v397, v399, rowEps, width] <;>
      norm_num [Finset.sum_range_succ, Finset.prod_range_succ, Nat.doubleFactorial, Nat.choose] <;> ring
end BstLean.Part250
#print axioms BstLean.Part250.diagpay
