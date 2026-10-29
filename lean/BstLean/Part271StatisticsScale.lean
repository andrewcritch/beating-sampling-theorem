import BstLean.Part271AngularScale

/-! Dimension factors in the four first-layer statistic payments. -/
namespace BstLean.Part271.R3
open Real BstLean.Part218 BstLean.Part214

noncomputable def traceCore (N m : ℕ) : ℝ :=
  (2*(1-1/(m : ℝ))*(2*(N : ℝ)/(m : ℝ)+6/(m : ℝ)) +
    8*(1-1/(m : ℝ))*(1-2/(m : ℝ)) +
    8*((N : ℝ)/(m : ℝ)+2/(m : ℝ))*((N : ℝ)/(m : ℝ)+3/(m : ℝ)) +
    16*(1-1/(m : ℝ))*((N : ℝ)/(m : ℝ)+2/(m : ℝ))) /
      ((1/10^5)*(1+(N : ℝ)/(m : ℝ)+1/(m : ℝ)))^2

noncomputable def diagonalCore (N : ℕ) : ℝ :=
  8*(1+3/(N : ℝ))/((1/1000)^2*(1+2/(N : ℝ)))

noncomputable def covariancePaymentCore (N m : ℕ) : ℝ :=
  (4+2/(m : ℝ))*(4*(1+2/(N : ℝ)))^2*j4Core N /
    ((1/1000)*4*(1-1/(m : ℝ))*j2Core N)^2

noncomputable def normCore (N : ℕ) : ℝ :=
  2*(4*(1+2/(N : ℝ)))^2*jbCore N/(3*(5-2/(N : ℝ)))^2

theorem trace_payment_scale {N m : ℕ} (hN : 0 < (N : ℝ)) (hm : 0 < (m : ℝ)) :
    traceVariance N m/((1/10^5)*((m : ℝ)*N*(m+N+1)))^2 =
      traceCore N m/((m : ℝ)*N) := by
  unfold traceVariance traceCore
  field_simp [ne_of_gt hN, ne_of_gt hm]
  <;> ring

theorem diagonal_payment_scale {N m : ℕ} (hN : 0 < (N : ℝ)) (hm : 0 < (m : ℝ)) :
    8*(m : ℝ)*N*(N+2)*(N+3)/((1/1000)*((m : ℝ)*N*(N+2)))^2 =
      diagonalCore N/((m : ℝ)*N) := by
  unfold diagonalCore
  field_simp [ne_of_gt hN, ne_of_gt hm]
  <;> ring

theorem covariance_payment_scale {N m : ℕ} (hN : 0 < (N : ℝ))
    (hm : 1 < (m : ℝ)) (hJ : 0 < j2Core N) :
    covarianceVarianceBound N m/((1/1000)*covarianceMeanBound N m)^2 =
      covariancePaymentCore N m/(m : ℝ) := by
  have hmp : 0 < (m : ℝ) := by linarith
  have hms : (m : ℝ)-1 ≠ 0 := by linarith
  have hmi : 1-1/(m : ℝ) ≠ 0 := by
    have h : 1/(m : ℝ) < 1 := (div_lt_one hmp).mpr hm
    linarith
  unfold covarianceVarianceBound covarianceMeanBound covariancePaymentCore
  rw [angularJ2_scale hN, angularJ4_scale hN]
  field_simp [ne_of_gt hN, ne_of_gt hmp, ne_of_gt hJ, hms, hmi]
  <;> ring

theorem norm_payment_scale {N m : ℕ} (hN : 1 ≤ (N : ℝ)) (hm : 0 < (m : ℝ)) :
    normVarianceBound N m/(3*inputVarianceMean N m)^2 = normCore N/(N : ℝ) := by
  have hNp : 0 < (N : ℝ) := by linarith
  have hd : 5*(N : ℝ)-2 ≠ 0 := by linarith
  have hd' : 5-2/(N : ℝ) ≠ 0 := by
    have h : 2/(N : ℝ) ≤ 2 := (div_le_iff₀ hNp).mpr (by linarith)
    linarith
  unfold normVarianceBound inputVarianceMean normCore
  rw [angularJb_scale hNp]
  field_simp [ne_of_gt hNp, ne_of_gt hm, hd, hd']
  <;> ring

end BstLean.Part271.R3
