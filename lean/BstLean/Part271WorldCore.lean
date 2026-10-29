import BstLean.Part271ScaledPayment
import BstLean.Part271FrameBand
import BstLean.Part271R3Package
import BstLean.Part250Charge

/-! Shared scalar supplies and the row arithmetic interface for the R0 World family. -/
namespace BstLean.Part271.R3
open Real MeasureTheory BstLean.Part130 BstLean.Part137 BstLean.Part140
open BstLean.Part157 BstLean.Part159 BstLean.Part192 BstLean.Part218 BstLean.Part227
open BstLean.Part250 (rowEps mean_majorant meanMajorantValue)

noncomputable def meanAllowance : ℝ := (1292780588231/25000000000000)

noncomputable def paymentBound (n : ℕ) (q : ℝ) : ℝ :=
  1/10^7+1/10^12+(279045642763226033/50000000000000)*(((2*n : ℕ) : ℝ)*q/(mW n : ℝ))+
    ((100000000024860904419623/1250000000000)+(800041348922962029453/100000000000000))/((mW n : ℝ)*((2*n : ℕ) : ℝ))+
      (34507377374543524728617/100000000000000)/(mW n : ℝ)+(1187885043021/20000000000000)/((2*n : ℕ) : ℝ)

noncomputable def frameEnvelope (n : ℕ) (r0 k0 k6 : ℝ) : ℝ :=
  (3017/20000+(138/1000)/(2*(n : ℝ))+
    (k0/(44945/10^6)+(1/1000)*(17321/20000)+(2/5)*k6)+(4450093486479903/125000000000000000))/(46727425/10^8)+
    (1787486734961/1000000000000000000)/(1118/100000)^2+(2235/100)*r0/((n : ℝ)*(4/10000)*(161/10000)^2)

noncomputable def momentEnvelope (n : ℕ) : ℝ :=
  ((n : ℝ)*(75935996087121/500000000000)+(9840972690524073/40000000000))/(mW n : ℝ)

noncomputable def parameters (hidden frame moment : ℝ) : WorldParameters where
  hiddenCharge := hidden
  frame := frame
  moment := moment
  productLo := 2
  productHi := 21/10
  noiseLo := 46/100
  noiseHi := 54/100

theorem mean_certificate {n : ℕ} (ha : 13225 ≤ n) (hb : n ≤ 16199) :
    e1MeanBound (2*n) (mW n) (1/10^6) (1/10^7) rowEps ≤
      meanAllowance/((2*n : ℕ) : ℝ) := by
  have hN : 0 < ((2*n : ℕ) : ℝ) := by exact_mod_cast (show 0 < 2*n by omega)
  have hm : 0 < (mW n : ℝ) := by have := Band.width_positive ha; linarith
  have hr : 0 ≤ firstRatio (2*n) := (by norm_num : (0 : ℝ) ≤
    100000000000000000000/314159265358979323847).trans (Band.ratio_window ha).1
  have hr' : firstRatio (2*n) ≤ 3/4 := (Band.ratio_window ha).2.trans (by norm_num)
  have he := (Band.endpoint ha hb).2.trans (by norm_num :
    _ ≤ (20474/100000 : ℝ))
  calc
    _ ≤ meanMajorantValue (2*n) (mW n) (1/10^6) (1/10^7) rowEps :=
      mean_majorant hr hr' he
    _ = meanCore (2*n) (mW n)/((2*n : ℕ) : ℝ) := mean_scale hN hm
    _ ≤ _ := div_le_div_of_nonneg_right
      ((Band.meanvalue ha hb).2.trans (by norm_num [meanAllowance])) hN.le

theorem mean_reserve {n : ℕ} (ha : 13225 ≤ n) :
    ((2*n : ℕ) : ℝ)*(1+1/10^6)*(meanAllowance/((2*n : ℕ) : ℝ)) < 712/10000 := by
  have hN : ((2*n : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show 2*n ≠ 0 by omega)
  have he : ((2*n : ℕ) : ℝ)*(1+1/10^6)*(meanAllowance/((2*n : ℕ) : ℝ)) =
      (1+1/10^6)*meanAllowance := by field_simp [hN] <;> ring
  rw [he]
  norm_num [meanAllowance]

theorem norm_charge {n : ℕ} (ha : 13225 ≤ n) :
    exp (-((mW n : ℝ)*((2*n : ℕ) : ℝ))/2*((1/10^6)-log (1+1/10^6)))+
    exp (-((mW n : ℝ)*((2*n : ℕ) : ℝ))/2*(-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hm : (4398046511104 : ℝ) ≤ mW n := by
    exact_mod_cast BstLean.Part137.mW_ge_pow42 (show 4096 ≤ n by omega)
  have hN : (26450 : ℝ) ≤ ((2*n : ℕ) : ℝ) := by exact_mod_cast (show 26450 ≤ 2*n by omega)
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
    (∑ i : Fin 4, e1Variances N m i/(rowEps i*e1MeanBounds N m i)^2) =
      traceVariance N m/((1/10^5)*((m : ℝ)*N*(m+N+1)))^2 +
      8*(m : ℝ)*N*(N+2)*(N+3)/((1/1000)*((m : ℝ)*N*(N+2)))^2 +
      covarianceVarianceBound N m/((1/1000)*covarianceMeanBound N m)^2 +
      normVarianceBound N m/(3*inputVarianceMean N m)^2 := by
  simp [Fin.sum_univ_succ,e1Variances,e1MeanBounds,rowEps]
  <;> ring

theorem statistics_payment {n : ℕ} (ha : 13225 ≤ n) (hb : n ≤ 16199) :
    (∑ i : Fin 4, e1Variances (2*n) (mW n) i/
      (rowEps i*e1MeanBounds (2*n) (mW n) i)^2) ≤
      ((100000000024860904419623/1250000000000)+(800041348922962029453/100000000000000))/((mW n : ℝ)*((2*n : ℕ) : ℝ))+(34507377374543524728617/100000000000000)/(mW n : ℝ)+(1187885043021/20000000000000)/((2*n : ℕ) : ℝ) := by
  have hN : 1 ≤ ((2*n : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ 2*n by omega)
  have hNp : 0 < ((2*n : ℕ) : ℝ) := by linarith
  have hm := Band.width_positive ha
  have hmp : 0 < (mW n : ℝ) := by linarith
  have hJ : 0 < j2Core (2*n) := lt_of_lt_of_le (by norm_num) (Band.jsecond ha hb).1
  have hi : (∑ i : Fin 4, e1Variances (2*n) (mW n) i/
      (rowEps i*e1MeanBounds (2*n) (mW n) i)^2) =
      traceCore (2*n) (mW n)/((mW n : ℝ)*((2*n : ℕ) : ℝ))+
      diagonalCore (2*n)/((mW n : ℝ)*((2*n : ℕ) : ℝ))+
      covariancePaymentCore (2*n) (mW n)/(mW n : ℝ)+normCore (2*n)/((2*n : ℕ) : ℝ) := by
    rw [statistics_identity, trace_payment_scale hNp hmp, diagonal_payment_scale hNp hmp,
      covariance_payment_scale hNp hm hJ, norm_payment_scale hN hmp]
    <;> ring
  rw [hi]
  have h1 := div_le_div_of_nonneg_right ((Band.tracepay ha hb).2.trans
    (by norm_num : _ ≤ ((100000000024860904419623/1250000000000) : ℝ))) (by positivity : 0 ≤ (mW n : ℝ)*((2*n : ℕ) : ℝ))
  have h2 := div_le_div_of_nonneg_right ((Band.diagpay ha hb).2.trans
    (by norm_num : _ ≤ ((800041348922962029453/100000000000000) : ℝ))) (by positivity : 0 ≤ (mW n : ℝ)*((2*n : ℕ) : ℝ))
  have h3 := div_le_div_of_nonneg_right ((Band.covpay ha hb).2.trans
    (by norm_num : _ ≤ ((34507377374543524728617/100000000000000) : ℝ))) hmp.le
  have h4 := div_le_div_of_nonneg_right ((Band.normpay ha hb).2.trans
    (by norm_num : _ ≤ ((1187885043021/20000000000000) : ℝ))) hNp.le
  conv_rhs => rw [add_div]
  linarith only [h1,h2,h3,h4]

theorem distance_payment {n : ℕ} (ha : 13225 ≤ n) (hb : n ≤ 16199) {q : ℝ}
    (hq : √((2*n : ℕ) : ℝ) ≤ q) :
    directDistancePayment n (1/10^6) (1/10^7) (meanAllowance/((2*n : ℕ) : ℝ))
      (712/10000) rowEps ≤ paymentBound n q := by
  have hN : 0 < ((2*n : ℕ) : ℝ) := by exact_mod_cast (show 0 < 2*n by omega)
  have hm : 0 < (mW n : ℝ) := by have := Band.width_positive ha; linarith
  have hC : conditionalCore (2*n) (mW n) meanAllowance ≤ (279045642763226033/50000000000000) :=
    (Band.conditional ha hb).2.trans (by norm_num [meanAllowance])
  have hc := mul_le_mul_of_nonneg_right hC
    (by positivity : 0 ≤ ((2*n : ℕ) : ℝ)*√((2*n : ℕ) : ℝ)/(mW n : ℝ))
  have hq' := mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hq hN.le) hm.le)
      (by norm_num : (0 : ℝ) ≤ (279045642763226033/50000000000000))
  unfold directDistancePayment e1Charge
  rw [conditional_scale hN hm meanAllowance]
  have hs := statistics_payment ha hb
  have he := norm_charge ha
  unfold paymentBound
  linarith only [hc,hq',hs,he]

structure RowArithmetic (n : ℕ) (hidden frame moment : ℝ) where
  r0 : ℝ
  k0 : ℝ
  k6 : ℝ
  q : ℝ
  r0_nonneg : 0 ≤ r0
  radius : 1 ≤ r0^2*(n : ℝ)^3
  k0_nonneg : 0 ≤ k0
  kernel : (2235/100)*r0 ≤ k0^2
  k6_nonneg : 0 ≤ k6
  sixth : 15/(8*(n : ℝ)) ≤ k6^2
  q_nonneg : 0 ≤ q
  q_square : ((2*n : ℕ) : ℝ) ≤ q^2
  hidden_payment : hiddenChargeWithDistance n (44945/10^6) (4/10000)
    (178/10^8) (1232/10^7) (paymentBound n q) ≤ hidden
  frame_payment : frameEnvelope n r0 k0 k6 ≤ frame
  moment_payment : momentEnvelope n ≤ moment

noncomputable def RowArithmetic.frameCertificate {n : ℕ} {h f v : ℝ}
    (row : RowArithmetic n h f v) (ha : 13225 ≤ n) (hb : n ≤ 16199) :
    FrameCertificate n (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := row.r0
  k0 := row.k0
  k6 := row.k6
  ε₁ := 161/10000
  ε₂ := 1118/100000
  s := 46727425/10^8
  r0_nonneg := row.r0_nonneg
  radius := row.radius
  k0_nonneg := row.k0_nonneg
  kernel := row.kernel
  k6_nonneg := row.k6_nonneg
  sixth := row.sixth
  ε₁_pos := by norm_num
  ε₂_pos := by norm_num
  s_pos := by norm_num
  norm_lower := (window_guards (show 4096 ≤ n by omega) (by norm_num)).1
  norm_separation := (window_guards (show 4096 ≤ n by omega) (by norm_num)).2.1
  denominator := (by norm_num : (46727425/10^8 : ℝ) ≤ _).trans (FrameBand.denominator ha hb).1

theorem RowArithmetic.frame_bound {n : ℕ} {h f v : ℝ}
    (row : RowArithmetic n h f v) (ha : 13225 ≤ n) (hb : n ≤ 16199) :
    frameValue (row.frameCertificate ha hb) ≤ f := by
  apply le_trans _ row.frame_payment
  have hd : centreDistance n (712/10000) ≤ (4450093486479903/125000000000000000) :=
    (FrameBand.distance ha hb).2.trans (by norm_num)
  have hf : centreFluctuation n (178/10^8) ≤ (1787486734961/1000000000000000000) :=
    (FrameBand.fluctuation ha hb).2.trans (by norm_num)
  unfold frameValue frameFormula RowArithmetic.frameCertificate frameEnvelope
  dsimp only
  have hd' := div_le_div_of_nonneg_right hd (by norm_num : (0 : ℝ) ≤ 46727425/10^8)
  have hf' := div_le_div_of_nonneg_right hf (by norm_num : (0 : ℝ) ≤ (1118/100000)^2)
  simp only [add_div]
  linarith only [hd',hf']

noncomputable def RowArithmetic.certificate {n : ℕ} {h f v : ℝ}
    (row : RowArithmetic n h f v) (ha : 13225 ≤ n) (hb : n ≤ 16199) :
    WorldCertificate n (parameters h f v) where
  frameCertificate := row.frameCertificate ha hb
  delta := meanAllowance/((2*n : ℕ) : ℝ)
  distance := paymentBound n row.q
  delta_nonneg := by unfold meanAllowance; positivity
  mean_bound := mean_certificate ha hb
  reserve := mean_reserve ha
  distance_bound := distance_payment ha hb ((Real.sqrt_le_iff).mpr ⟨row.q_nonneg,row.q_square⟩)
  product_lower := (by norm_num : (202225/100000 : ℝ) ≤ _).trans (FrameBand.productlo ha hb).1
  product_upper := (FrameBand.producthi ha hb).2.trans (by norm_num)
  hidden_bound := row.hidden_payment
  frame_bound := row.frame_bound ha hb
  moment_bound := (MomentBand.envelope ha hb).trans row.moment_payment
  productLo_bound := by norm_num [parameters]
  productHi_bound := by norm_num [parameters]
  noiseLo_bound := (by norm_num [parameters] : _ ≤ _).trans (FrameBand.noiselo ha hb).1
  noiseHi_bound := (FrameBand.noisehi ha hb).2.trans (by norm_num [parameters])

noncomputable def RowArithmetic.worldPackage {n : ℕ} {h f v : ℝ}
    (row : RowArithmetic n h f v) (ha : 13225 ≤ n) (hb : n ≤ 16199) :
    WorldPackage (paperProgram n) (parameters h f v) :=
  (row.certificate ha hb).toWorldPackage (by omega)

theorem RowArithmetic.angle_events {n : ℕ} {h f v : ℝ}
    (row : RowArithmetic n h f v) (ha : 13225 ≤ n) (hb : n ≤ 16199) :
    (row.worldPackage ha hb).lowerEvent = Ethm (paperProgram n).design.toCentres ∧
    (row.worldPackage ha hb).upperEvent = Ethp (paperProgram n).design.toCentres := ⟨rfl,rfl⟩

end BstLean.Part271.R3
