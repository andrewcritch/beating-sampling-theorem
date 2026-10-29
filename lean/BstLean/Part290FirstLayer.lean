import BstLean.Part290Payment
import BstLean.Part250Charge
import BstLean.Part233Concrete

namespace BstLean.Part290
open Real MeasureTheory Set Matrix
open BstLean.Part130 BstLean.Part134 BstLean.Part136 BstLean.Part137
open BstLean.Part140 BstLean.Part157 BstLean.Part159 BstLean.Part205 BstLean.Part214
open BstLean.Part218 BstLean.Part227 BstLean.Part233
open BstLean.Part250 (meanMajorantValue mean_majorant endpointPolynomial)
open BstLean.Part271.R3 (traceCore diagonalCore covariancePaymentCore normCore j2Core
  trace_payment_scale diagonal_payment_scale)

noncomputable def meanAllowance : ℝ := 52141/10^6
noncomputable def worldMean : ℝ := (1+1/10^6)*meanAllowance
noncomputable def meanDelta (n : ℕ) : ℝ := meanAllowance/((2*n : ℕ) : ℝ)

theorem mean_certificate {n : ℕ} (ha : 8000 ≤ n) :
    e1MeanBound (2*n) (mW n) (1/10^6) (1/10^7) worldEps ≤ meanDelta n := by
  have hN : 0 < ((2*n : ℕ) : ℝ) := by exact_mod_cast (show 0 < 2*n by omega)
  have hm : 0 < (mW n : ℝ) := by have := width_positive ha; linarith
  have hr : 0 ≤ firstRatio (2*n) := le_trans (by norm_num) (ratio_window ha).1
  have hr' : firstRatio (2*n) ≤ 3/4 := (ratio_window ha).2.trans (by norm_num)
  have he : endpointPolynomial (firstRatio (2*n)) ≤ 20474/100000 :=
    (endpoint ha).2.trans (by norm_num)
  calc
    _ ≤ meanMajorantValue (2*n) (mW n) (1/10^6) (1/10^7) worldEps := mean_majorant hr hr' he
    _ = meanCore (2*n) (mW n)/((2*n : ℕ) : ℝ) := mean_scale hN hm
    _ ≤ _ := div_le_div_of_nonneg_right
      ((meanvalue ha).2.trans (by norm_num [meanAllowance])) hN.le

theorem mean_identity {n : ℕ} (ha : 8000 ≤ n) :
    ((2*n : ℕ) : ℝ)*(1+1/10^6)*meanDelta n = worldMean := by
  have hN : ((2*n : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show 2*n ≠ 0 by omega)
  unfold meanDelta worldMean
  field_simp [hN]

theorem mean_reserve : 0 ≤ worldMean ∧ worldMean < 525/10000 := by
  norm_num [worldMean, meanAllowance]

theorem norm_charge {n : ℕ} (ha : 8000 ≤ n) :
    exp (-((mW n : ℝ)*((2*n : ℕ) : ℝ))/2*((1/10^6)-log (1+1/10^6)))+
    exp (-((mW n : ℝ)*((2*n : ℕ) : ℝ))/2*(-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hm : (4398046511104 : ℝ) ≤ mW n := by
    exact_mod_cast mW_ge_pow42 (show 4096 ≤ n by omega)
  have hN : (16000 : ℝ) ≤ ((2*n : ℕ) : ℝ) := by exact_mod_cast (show 16000 ≤ 2*n by omega)
  have hp := mul_le_mul hm hN (by norm_num) (by positivity : (0 : ℝ) ≤ mW n)
  have hg : 0 ≤ (mW n : ℝ)*((2*n : ℕ) : ℝ)/2 := by positivity
  have hplus := mul_le_mul_of_nonneg_left BstLean.Part250.logarithm_plus hg
  have hminus := mul_le_mul_of_nonneg_left BstLean.Part250.logarithm_minus hg
  have h1 : -((mW n : ℝ)*((2*n : ℕ) : ℝ))/2*((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    nlinarith only [hp,hplus]
  have h2 : -((mW n : ℝ)*((2*n : ℕ) : ℝ))/2*(-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    nlinarith only [hp,hminus]
  calc
    _ ≤ exp (-100)+exp (-100) := add_le_add (exp_le_exp.mpr h1) (exp_le_exp.mpr h2)
    _ ≤ _ := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity (N m : ℕ) :
    (∑ i : Fin 4, e1Variances N m i/(worldEps i*e1MeanBounds N m i)^2) =
      traceVariance N m/((1/10^5)*((m : ℝ)*N*(m+N+1)))^2 +
      8*(m : ℝ)*N*(N+2)*(N+3)/((1/1000)*((m : ℝ)*N*(N+2)))^2 +
      covarianceVarianceBound N m/((4/1000)*covarianceMeanBound N m)^2 +
      normVarianceBound N m/(10*inputVarianceMean N m)^2 := by
  simp [Fin.sum_univ_succ,e1Variances,e1MeanBounds,worldEps]
  <;> ring

theorem statistics_payment {n : ℕ} (ha : 8000 ≤ n) :
    (∑ i : Fin 4, e1Variances (2*n) (mW n) i/
      (worldEps i*e1MeanBounds (2*n) (mW n) i)^2) ≤ 704/10^9 := by
  have hN : 1 ≤ ((2*n : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ 2*n by omega)
  have hNp : 0 < ((2*n : ℕ) : ℝ) := by linarith
  have hm := width_positive ha
  have hmp : 0 < (mW n : ℝ) := by linarith
  have hJ : 0 < j2Core (2*n) := lt_of_lt_of_le (by norm_num) (jsecond ha).1
  rw [statistics_identity, trace_payment_scale hNp hmp, diagonal_payment_scale hNp hmp,
    covariance_payment_scale hNp hm hJ, norm_payment_scale hN hmp]
  have h1 : traceCore (2*n) (mW n) ≤ 80000000070 := (tracepay ha).2.trans (by norm_num)
  have h2 : diagonalCore (2*n) ≤ 8001500 := (diagpay ha).2.trans (by norm_num)
  have h3 : covariancePaymentCore (2*n) (mW n) ≤ 188168351 := (covpay ha).2.trans (by norm_num)
  have h4 : normCore (2*n) ≤ 59912893/10^9 := (normpay ha).2.trans (by norm_num)
  calc
    _ ≤ (80000000070+8001500)/((mW n : ℝ)*((2*n : ℕ) : ℝ))+
        188168351/(16*(mW n : ℝ))+(9/100)*(59912893/10^9)/((2*n : ℕ) : ℝ) := by
      rw [add_div]
      gcongr
    _ = (80000000070+8001500)*(1/(mW n : ℝ))*(1/((2*n : ℕ) : ℝ))+
        (188168351/16)*(1/(mW n : ℝ))+(9/100)*(59912893/10^9)*(1/((2*n : ℕ) : ℝ)) := by ring
    _ ≤ (80000000070+8001500)*(1/45793280000000)*(1/16000)+
        (188168351/16)*(1/45793280000000)+(9/100)*(59912893/10^9)*(1/16000) := by
      have hi := (inverse_width ha).2
      have hj := (inverse_dimension ha).2
      gcongr
    _ ≤ _ := by norm_num

theorem first_layer_charge {n : ℕ} (ha : 8000 ≤ n) :
    e1Charge (2*n) (mW n) (1/10^6) (1/10^7) worldEps ≤ 804001/10^12 := by
  have h1 := norm_charge ha
  have h2 := statistics_payment ha
  unfold e1Charge
  linarith only [h1,h2]

theorem small_exp : exp (-100 : ℝ) ≤ 1/10^12 := by
  have h := BstLean.Part243.row_sampling
  unfold BstLean.Part243.rowSamplingAllowance at h
  linarith [exp_pos (-100 : ℝ)]

theorem cancellation_charge {n : ℕ} (ha : 8000 ≤ n) :
    cancellationPayment n (525/10000) worldMean (1/10^6) ≤ 1/10^12 := by
  have hn := n_positive ha
  have hm : 0 < (mW n : ℝ) := by have := width_positive ha; linarith
  have hN : 0 < ((2*n : ℕ) : ℝ) := by positivity
  have hratio := (dimension_width ha).2
  have hratio' : (2862080000 : ℝ)*((2*n : ℕ) : ℝ) ≤ mW n := by
    have := (div_le_iff₀ hm).mp hratio
    linarith only [this]
  have hs : (22912/10^5 : ℝ) ≤ √(525/10000 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have ht : √worldMean ≤ 22835/10^5 := sqrt_le_iff.mpr (by norm_num [worldMean,meanAllowance])
  have hgap : (7/10000 : ℝ)^2 ≤ (√(525/10000 : ℝ)-√worldMean)^2 := by nlinarith
  have hk : √(31835/100000 : ℝ) ≤ 565/1000 := sqrt_le_iff.mpr (by norm_num)
  have hk0 := sqrt_nonneg (31835/100000 : ℝ)
  have hd : (1+√(31835/100000 : ℝ))^2*(1+1/10^6) ≤ 3 := by nlinarith
  have hnum := mul_le_mul_of_nonneg_left hgap hm.le
  have hden := mul_le_mul_of_nonneg_right hd hN.le
  have he : 100 ≤ (mW n : ℝ)*(√(525/10000 : ℝ)-√worldMean)^2/
      ((1+√(31835/100000 : ℝ))^2*(1+1/10^6)*((2*n : ℕ) : ℝ)) := by
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith only [hnum,hden,hratio']
  unfold cancellationPayment
  exact (exp_le_exp.mpr (by linarith only [he])).trans small_exp

theorem output_norm_charge {n : ℕ} (ha : 8000 ≤ n) :
    outputNormPayment n (1/10^6) ≤ 1/10^12 := by
  let e : ℝ := (10 : ℝ)^8/(8*(1+1/10^6))-1
  have he : 1000 ≤ e := by norm_num [e]
  have hlog : log (1+e) ≤ 24 := by
    have h := log_le_log (by norm_num [e] : (0 : ℝ) < 1+e)
      (by norm_num [e] : 1+e ≤ (2 : ℝ)^24)
    rw [log_pow] at h
    have hh : log (2 : ℝ) ≤ 1 := by
      convert log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) using 1 <;> norm_num
    exact h.trans (by norm_num only [Nat.cast_ofNat]; linarith)
  have hm : 1 ≤ (mW n : ℝ) := (width_positive ha).le
  have hmul := mul_le_mul hm (show (976 : ℝ) ≤ e-log (1+e) by linarith)
    (by norm_num : (0 : ℝ) ≤ 976) (by positivity : (0 : ℝ) ≤ mW n)
  change exp (-(mW n : ℝ)*(e-log (1+e))/2) ≤ _
  apply (exp_le_exp.mpr ?_).trans small_exp
  calc
    -(mW n : ℝ)*(e-log (1+e))/2 = -((mW n : ℝ)*(e-log (1+e)))/2 := by ring
    _ ≤ -(1*976)/2 := div_le_div_of_nonneg_right (neg_le_neg hmul) (by norm_num)
    _ ≤ -100 := by norm_num

theorem group_payment {n : ℕ} (ha : 8000 ≤ n) :
    concreteGroupPayment n (1/10^6) (1/10^7) (meanDelta n) (525/10000) worldEps ≤ 805/10^9 := by
  unfold concreteGroupPayment
  rw [mean_identity ha]
  linarith only [first_layer_charge ha, cancellation_charge ha, output_norm_charge ha]

theorem group_charge {n : ℕ} (ha : 8000 ≤ n) :
    (hidGauss (2*n) (mW n)).real (distanceGroup n (525/10000))ᶜ ≤ 805/10^9 := by
  apply (concrete_distanceGroup_charge (show 4096 ≤ n by omega)
    (ε := worldEps) (Δ := meanDelta n)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [worldEps])
    (by unfold meanDelta meanAllowance; positivity) (mean_certificate ha) ?_).trans (group_payment ha)
  rw [mean_identity ha]
  exact mean_reserve.2

end BstLean.Part290
