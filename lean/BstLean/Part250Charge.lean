import BstLean.Part250Statpay
import BstLean.Part197Log

/-! Actual first-layer and direct-distance payments at dimension 12225. -/
namespace BstLean.Part250
open Real MeasureTheory BstLean.Part130 BstLean.Part137 BstLean.Part140
open BstLean.Part218 BstLean.Part227 BstLean.Part228

theorem logarithm_plus : (1/10^6 : ℝ) - log (1+1/10^6) ≥ 1/(3*10^12) := by
  have h := (abs_le.mp (BstLean.Part197.log_one_add_remainder
    (x := (1/10^6 : ℝ)) (by norm_num) 3)).2
  norm_num [BstLean.Part197.logOneAddSum, Finset.sum_range_succ] at h ⊢
  linarith

theorem logarithm_minus : -(1/10^6 : ℝ) - log (1-1/10^6) ≥ 1/(3*10^12) := by
  have h := (abs_le.mp (BstLean.Part197.log_one_add_remainder
    (x := -(1/10^6 : ℝ)) (by norm_num) 3)).2
  norm_num [BstLean.Part197.logOneAddSum, Finset.sum_range_succ] at h ⊢
  linarith

theorem norm_charge :
    exp (-((mW 12225 : ℝ)*24450)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12225 : ℝ)*24450)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12225 : ℝ)*24450)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12225 : ℝ)*24450)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24450 (mW 12225) i /
      (rowEps i * e1MeanBounds 24450 (mW 12225) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24450 (mW 12225) (1/10^6) (1/10^7) rowEps ≤ 2116714/10^12 := by
  have hr : 0 ≤ firstRatio 24450 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24450 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24450) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12225 (1/10^6) (1/10^7) (2116714/10^12)
      (712/10000) rowEps ≤ 110415/10^9 := by
  have hs : statisticsPayment ≤ 4156343472612/10^18 := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ 106158535396395/10^18 := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12225 (1/10^6) (1/10^7) (2116714/10^12)
      (712/10000) rowEps =
      exp (-((mW 12225 : ℝ)*24450)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12225 : ℝ)*24450)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12225) (mW 12225)).real
      (goodDist 12225 (712/10000))ᶜ ≤ 110415/10^9 := by
  apply le_trans (concrete_distance_charge (n := 12225) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := 2116714/10^12) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

end BstLean.Part250
#print axioms BstLean.Part250.mean_certificate
#print axioms BstLean.Part250.direct_payment
#print axioms BstLean.Part250.distance_charge
