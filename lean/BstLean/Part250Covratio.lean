import BstLean.Part250Bounds
import BstLean.Part250Meanvalue
/-! Generated rational certificate; every interval step is kernel checked. -/
namespace BstLean.Part250
open Real BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228
open BstLean.Part218 BstLean.Part205 BstLean.Part214
theorem covratio : Bounds (e1CovarianceRatio 24450 (mW 12225) (1/10^6) rowEps) (470430282183193256522945011/100000000000000000000000000000) (47074297432346290820683113/10000000000000000000000000000) := by
  let v22 : ℝ := 1
  have h22 : Bounds v22 1 1 := Bounds.point _
  let v302 : ℝ := -(firstRatio 24450)
  have h302 : Bounds v302 (-79580726381382489254212489/250000000000000000000000000) (-4973591971621729242765971/15625000000000000000000000) := by simpa only [neg_div, neg_neg, neg_zero] using Bounds.neg ratio
  let v303 : ℝ := v22+v302
  have h303 : Bounds v303 (17041927361861751074578751/25000000000000000000000000) (34084505690810466423148893/50000000000000000000000000) := Bounds.add h22 h302 (by norm_num)
  let v304 : ℝ := (e1EnergyLower 24450 (mW 12225) (1/10^6))*v303
  have h304 : Bounds v304 (11264202164958141927431899/2000000000000000) (281610432495127918112726077/50000000000000000) := Bounds.mul energy h303 (by norm_num)
  let v305 : ℝ := 1/v304
  have h305 : Bounds v305 (3551004808805514640195739/20000000000000000000000000000000000) (88776815734975405281657561/500000000000000000000000000000000000) := Bounds.inv h304 (by norm_num)
  let v306 : ℝ := (e1FrobBound 24450 (mW 12225) rowEps)/v304
  have h306 : Bounds v306 (470430282183193256522945011/100000000000000000000000000000) (47074297432346290820683113/10000000000000000000000000000) := bounds_div frob h305 (by norm_num)
  convert h306 using 1 <;>
    simp only [v22, v302, v303, v304, v306, e1CovarianceRatio, width] <;>
      norm_num [Finset.sum_range_succ, Finset.prod_range_succ, Nat.doubleFactorial, Nat.choose] <;> ring
end BstLean.Part250
#print axioms BstLean.Part250.covratio
