import BstLean.Part250Bounds
import BstLean.Part184ISNum

/-! A rational polynomial majorant for the direct-distance Taylor coefficient. -/
namespace BstLean.Part250
open Real Set BstLean.Part130 BstLean.Part205
open BstLean.Part218

noncomputable def meanMajorantValue (N m : ℕ) (εω ph : ℝ) (ε : Fin 4 → ℝ) : ℝ :=
  let T := (e1FrobBound N m ε ^ 2 + 2 * (directionMean N m / ph)) /
    e1EnergyLower N m εω ^ 2
  let ν := √(e1InputVarianceBound N m ε) / e1EnergyLower N m εω
  (20474/100000 : ℝ) * (√T + √2*ν)^2 + 6*ν^2 + (√2+2)*ν*√T

noncomputable def conditionalValue : ℝ :=
  ((4 * (24450 : ℝ)^2 / (mW 12225 : ℝ)) * (1 + 1/10^6)^2 *
    √((2116714/10^12)/2) * ((1-firstRatio 24450) * √(1-firstRatio 24450) *
      sixthConstant (e1CovarianceRatio 24450 (mW 12225) (1/10^6) rowEps))) /
    (712/10000 - 24450*(1+1/10^6)*(2116714/10^12))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24450 (mW 12225) /
    ((1/10^5) * ((mW 12225 : ℝ)*24450*((mW 12225 : ℝ)+24450+1)))^2 +
  8*(mW 12225 : ℝ)*24450*(24450+2)*(24450+3) /
    ((1/1000)*((mW 12225 : ℝ)*24450*(24450+2)))^2 +
  covarianceVarianceBound 24450 (mW 12225) /
    ((1/1000)*covarianceMeanBound 24450 (mW 12225))^2 +
  normVarianceBound 24450 (mW 12225) / (3*inputVarianceMean 24450 (mW 12225))^2

noncomputable def endpointPolynomial (r : ℝ) : ℝ :=
  (π / 2 - (r + r^3/6 + 3*r^5/40) - √(1-r^2)) / π / (1-r)^2

theorem endpoint_polynomial {r : ℝ} (hr : 0 ≤ r) (hr' : r ≤ 3/4) :
    endpointK r ≤ endpointPolynomial r := by
  have he : endpointK r =
      (π/2 - Real.arcsin r - √(1-r^2)) / π / (1-r)^2 := by
    unfold endpointK slopeK
    rw [BstLean.Part184.IT.fsn_kappa_eq, Real.arccos_eq_pi_div_two_sub_arcsin]
    field_simp
    <;> ring
  rw [he]
  unfold endpointPolynomial
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  apply div_le_div_of_nonneg_right _ pi_pos.le
  linarith [BstLean.Part184.IT.fsn_arcsin_ge hr hr']

theorem mean_majorant {r T ν : ℝ} (hr : 0 ≤ r) (hr' : r ≤ 3/4)
    (hK : endpointPolynomial r ≤ 20474/100000) :
    meanBound r T ν ≤ (20474/100000 : ℝ) * (√T + √2*ν)^2 +
      6*ν^2 + (√2+2)*ν*√T := by
  have hk := (endpoint_polynomial hr hr').trans hK
  have hs : slopeK r ≤ 1 := by
    unfold slopeK
    rw [div_le_one pi_pos]
    linarith [Real.arccos_nonneg r]
  have hc : kappa r ≤ 1 := (kappa_mem (by linarith) (by linarith)).2
  unfold meanBound
  have h1 := mul_le_mul_of_nonneg_right hk (sq_nonneg (√T+√2*ν))
  have h2 := mul_le_mul_of_nonneg_right (show slopeK r + kappa r + 4 ≤ 6 by linarith)
    (sq_nonneg ν)
  linarith

end BstLean.Part250
#print axioms BstLean.Part250.endpoint_polynomial
#print axioms BstLean.Part250.mean_majorant
