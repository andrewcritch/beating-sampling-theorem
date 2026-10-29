import BstLean.Part250Bounds
import BstLean.Part250Normpay
/-! Generated rational certificate; every interval step is kernel checked. -/
namespace BstLean.Part250
open Real BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228
open BstLean.Part218 BstLean.Part205 BstLean.Part214
theorem statpay : Bounds (statisticsPayment) (26792094341494262769059621/10000000000000000000000000000000) (8312686945223147217413191/2000000000000000000000000000000) := by
  let v488 : ℝ := (traceVariance 24450 (mW 12225) / ((1/10^5) * ((mW 12225 : ℝ)*24450*((mW 12225 : ℝ)+24450+1)))^2)+(8*(mW 12225 : ℝ)*24450*(24450+2)*(24450+3) / ((1/1000)*((mW 12225 : ℝ)*24450*(24450+2)))^2)
  have h488 : Bounds v488 (20248531328348872081787161/1250000000000000000000000000000000) (16198825062679097665429731/1000000000000000000000000000000000) := Bounds.add tracepay diagpay (by norm_num)
  let v489 : ℝ := v488+(covarianceVarianceBound 24450 (mW 12225) / ((1/1000)*covarianceMeanBound 24450 (mW 12225))^2)
  have h489 : Bounds v489 (3862029362699371759133971/15625000000000000000000000000000) (34486078353498142487395583/20000000000000000000000000000000) := Bounds.add h488 covpay (by norm_num)
  let v490 : ℝ := v489+(normVarianceBound 24450 (mW 12225) / (3*inputVarianceMean 24450 (mW 12225))^2)
  have h490 : Bounds v490 (26792094341494262769059621/10000000000000000000000000000000) (8312686945223147217413191/2000000000000000000000000000000) := Bounds.add h489 normpay (by norm_num)
  convert h490 using 1 <;>
    simp only [v488, v489, v490, statisticsPayment, width] <;>
      norm_num [Finset.sum_range_succ, Finset.prod_range_succ, Nat.doubleFactorial, Nat.choose] <;> ring
end BstLean.Part250
#print axioms BstLean.Part250.statpay
