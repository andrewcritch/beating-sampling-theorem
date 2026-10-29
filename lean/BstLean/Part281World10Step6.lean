import BstLean.Part281World10Step5
namespace BstLean.Part281.WorldRow12109
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
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
    exp (-((mW 12109 : ℝ)*24218)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12109 : ℝ)*24218)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12109 : ℝ)*24218)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12109 : ℝ)*24218)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24218 (mW 12109) i /
      (rowEps i * e1MeanBounds 24218 (mW 12109) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24218 (mW 12109) (1/10^6) (1/10^7) rowEps ≤ (106861/50000000000) := by
  have hr : 0 ≤ firstRatio 24218 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24218 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24218) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12109 (1/10^6) (1/10^7) ((106861/50000000000))
      (712/10000) rowEps ≤ (112612359/1000000000000) := by
  have hs : statisticsPayment ≤ (4238676364891/1000000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (54136840384147/500000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12109 (1/10^6) (1/10^7) ((106861/50000000000))
      (712/10000) rowEps =
      exp (-((mW 12109 : ℝ)*24218)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12109 : ℝ)*24218)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12109) (mW 12109)).real
      (goodDist 12109 (712/10000))ᶜ ≤ (112612359/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 12109) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (106861/50000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12109 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (750477335799/1000000000000000000)
  k0 := (4095505885126727/1000000000000000000)
  k6 := (12443613013555081/1000000000000000000)
  ε₁ := 161/10000
  ε₂ := 1118/100000
  s := 46727425/10^8
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  ε₁_pos := by norm_num
  ε₂_pos := by norm_num
  s_pos := by norm_num
  norm_lower := (window_guards (n := 12109) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12109) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((112612359/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12109 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12109) internalParameters :=
  BstLean.Part227.worldPackage (n := 12109) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (112612359/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12109) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part281.world12109.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part281.world12109, width]

theorem frame_payment : internalParameters.frame ≤ Part281.world12109.frame := by
  exact frame.2.trans (by norm_num [Part281.world12109])

theorem moment_payment : internalParameters.moment ≤ Part281.world12109.moment := by
  exact moment.2.trans (by norm_num [Part281.world12109])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1199968109/1000000000000) ∧
    internalParameters.frame ≤ (634205304433/1000000000000) ∧
    internalParameters.moment ≤ (10672639871/1000000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12109) (Part281.world12109) where
  hidden := internalWorld.hidden
  hidden_measurable := internalWorld.hidden_measurable
  scale := internalWorld.scale
  scale_measurable := internalWorld.scale_measurable
  scale_eq := internalWorld.scale_eq
  calibration := internalWorld.calibration
  calibration_measurable := internalWorld.calibration_measurable
  hidden_charge := internalWorld.hidden_charge.trans hidden_payment
  product_window := by
    intro θ hθ
    obtain ⟨hl, hu⟩ := internalWorld.product_window θ hθ
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part281.world12109]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part281.world12109])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part281.world12109]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part281.world12109]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12109).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12109).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part281.WorldRow12109
namespace BstLean.Part281.WorldRow12110
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
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
    exp (-((mW 12110 : ℝ)*24220)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12110 : ℝ)*24220)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12110 : ℝ)*24220)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12110 : ℝ)*24220)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24220 (mW 12110) i /
      (rowEps i * e1MeanBounds 24220 (mW 12110) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24220 (mW 12110) (1/10^6) (1/10^7) rowEps ≤ (2137041/1000000000000) := by
  have hr : 0 ≤ firstRatio 24220 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24220 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24220) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12110 (1/10^6) (1/10^7) ((2137041/1000000000000))
      (712/10000) rowEps ≤ (56296489/500000000000) := by
  have hs : statisticsPayment ≤ (2118976880011/500000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (108255022248773/1000000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12110 (1/10^6) (1/10^7) ((2137041/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 12110 : ℝ)*24220)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12110 : ℝ)*24220)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12110) (mW 12110)).real
      (goodDist 12110 (712/10000))ᶜ ≤ (56296489/500000000000) := by
  apply le_trans (concrete_distance_charge (n := 12110) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (2137041/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12110 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (375192190081/500000000000000000)
  k0 := (4095252238461107/1000000000000000000)
  k6 := (12443099228670221/1000000000000000000)
  ε₁ := 161/10000
  ε₂ := 1118/100000
  s := 46727425/10^8
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  ε₁_pos := by norm_num
  ε₂_pos := by norm_num
  s_pos := by norm_num
  norm_lower := (window_guards (n := 12110) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12110) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((56296489/500000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12110 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12110) internalParameters :=
  BstLean.Part227.worldPackage (n := 12110) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (56296489/500000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12110) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part281.world12110.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part281.world12110, width]

theorem frame_payment : internalParameters.frame ≤ Part281.world12110.frame := by
  exact frame.2.trans (by norm_num [Part281.world12110])

theorem moment_payment : internalParameters.moment ≤ Part281.world12110.moment := by
  exact moment.2.trans (by norm_num [Part281.world12110])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (299979231/250000000000) ∧
    internalParameters.frame ≤ (158547505481/250000000000) ∧
    internalParameters.moment ≤ (10670331919/1000000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12110) (Part281.world12110) where
  hidden := internalWorld.hidden
  hidden_measurable := internalWorld.hidden_measurable
  scale := internalWorld.scale
  scale_measurable := internalWorld.scale_measurable
  scale_eq := internalWorld.scale_eq
  calibration := internalWorld.calibration
  calibration_measurable := internalWorld.calibration_measurable
  hidden_charge := internalWorld.hidden_charge.trans hidden_payment
  product_window := by
    intro θ hθ
    obtain ⟨hl, hu⟩ := internalWorld.product_window θ hθ
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part281.world12110]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part281.world12110])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part281.world12110]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part281.world12110]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12110).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12110).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part281.WorldRow12110
namespace BstLean.Part281.WorldRow12111
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
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
    exp (-((mW 12111 : ℝ)*24222)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12111 : ℝ)*24222)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12111 : ℝ)*24222)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12111 : ℝ)*24222)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24222 (mW 12111) i /
      (rowEps i * e1MeanBounds 24222 (mW 12111) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24222 (mW 12111) (1/10^6) (1/10^7) rowEps ≤ (2136863/1000000000000) := by
  have hr : 0 ≤ firstRatio 24222 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24222 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24222) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12111 (1/10^6) (1/10^7) ((2136863/1000000000000))
      (712/10000) rowEps ≤ (1758967/15625000000) := by
  have hs : statisticsPayment ≤ (1059307845509/250000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (54118327371443/500000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12111 (1/10^6) (1/10^7) ((2136863/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 12111 : ℝ)*24222)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12111 : ℝ)*24222)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12111) (mW 12111)).real
      (goodDist 12111 (712/10000))ᶜ ≤ (1758967/15625000000) := by
  apply le_trans (concrete_distance_charge (n := 12111) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (2136863/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12111 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (750291443713/1000000000000000000)
  k0 := (818999725689467/200000000000000000)
  k6 := (12442585507421167/1000000000000000000)
  ε₁ := 161/10000
  ε₂ := 1118/100000
  s := 46727425/10^8
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  ε₁_pos := by norm_num
  ε₂_pos := by norm_num
  s_pos := by norm_num
  norm_lower := (window_guards (n := 12111) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12111) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((1758967/15625000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12111 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12111) internalParameters :=
  BstLean.Part227.worldPackage (n := 12111) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (1758967/15625000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12111) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part281.world12111.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part281.world12111, width]

theorem frame_payment : internalParameters.frame ≤ Part281.world12111.frame := by
  exact frame.2.trans (by norm_num [Part281.world12111])

theorem moment_payment : internalParameters.moment ≤ Part281.world12111.moment := by
  exact moment.2.trans (by norm_num [Part281.world12111])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1199865753/1000000000000) ∧
    internalParameters.frame ≤ (634174742013/1000000000000) ∧
    internalParameters.moment ≤ (1333503083/125000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12111) (Part281.world12111) where
  hidden := internalWorld.hidden
  hidden_measurable := internalWorld.hidden_measurable
  scale := internalWorld.scale
  scale_measurable := internalWorld.scale_measurable
  scale_eq := internalWorld.scale_eq
  calibration := internalWorld.calibration
  calibration_measurable := internalWorld.calibration_measurable
  hidden_charge := internalWorld.hidden_charge.trans hidden_payment
  product_window := by
    intro θ hθ
    obtain ⟨hl, hu⟩ := internalWorld.product_window θ hθ
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part281.world12111]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part281.world12111])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part281.world12111]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part281.world12111]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12111).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12111).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part281.WorldRow12111
namespace BstLean.Part281.WorldRow12112
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
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
    exp (-((mW 12112 : ℝ)*24224)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12112 : ℝ)*24224)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12112 : ℝ)*24224)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12112 : ℝ)*24224)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24224 (mW 12112) i /
      (rowEps i * e1MeanBounds 24224 (mW 12112) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24224 (mW 12112) (1/10^6) (1/10^7) rowEps ≤ (534171/250000000000) := by
  have hr : 0 ≤ firstRatio 24224 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24224 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24224) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12112 (1/10^6) (1/10^7) ((534171/250000000000))
      (712/10000) rowEps ≤ (112554499/1000000000000) := by
  have hs : statisticsPayment ≤ (4236509230837/1000000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (108217988152273/1000000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12112 (1/10^6) (1/10^7) ((534171/250000000000))
      (712/10000) rowEps =
      exp (-((mW 12112 : ℝ)*24224)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12112 : ℝ)*24224)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12112) (mW 12112)).real
      (goodDist 12112 (712/10000))ᶜ ≤ (112554499/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 12112) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (534171/250000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12112 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (375099263223/500000000000000000)
  k0 := (4094745055075847/1000000000000000000)
  k6 := (6221035924897391/500000000000000000)
  ε₁ := 161/10000
  ε₂ := 1118/100000
  s := 46727425/10^8
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  ε₁_pos := by norm_num
  ε₂_pos := by norm_num
  s_pos := by norm_num
  norm_lower := (window_guards (n := 12112) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12112) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((112554499/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12112 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12112) internalParameters :=
  BstLean.Part227.worldPackage (n := 12112) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (112554499/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12112) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part281.world12112.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part281.world12112, width]

theorem frame_payment : internalParameters.frame ≤ Part281.world12112.frame := by
  exact frame.2.trans (by norm_num [Part281.world12112])

theorem moment_payment : internalParameters.moment ≤ Part281.world12112.moment := by
  exact moment.2.trans (by norm_num [Part281.world12112])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1199814597/1000000000000) ∧
    internalParameters.frame ≤ (6341594647/10000000000) ∧
    internalParameters.moment ≤ (5332859053/500000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12112) (Part281.world12112) where
  hidden := internalWorld.hidden
  hidden_measurable := internalWorld.hidden_measurable
  scale := internalWorld.scale
  scale_measurable := internalWorld.scale_measurable
  scale_eq := internalWorld.scale_eq
  calibration := internalWorld.calibration
  calibration_measurable := internalWorld.calibration_measurable
  hidden_charge := internalWorld.hidden_charge.trans hidden_payment
  product_window := by
    intro θ hθ
    obtain ⟨hl, hu⟩ := internalWorld.product_window θ hθ
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part281.world12112]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part281.world12112])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part281.world12112]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part281.world12112]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12112).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12112).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part281.WorldRow12112
namespace BstLean.Part281.WorldRow12113
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
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
    exp (-((mW 12113 : ℝ)*24226)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12113 : ℝ)*24226)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12113 : ℝ)*24226)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12113 : ℝ)*24226)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24226 (mW 12113) i /
      (rowEps i * e1MeanBounds 24226 (mW 12113) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24226 (mW 12113) (1/10^6) (1/10^7) rowEps ≤ (1068253/500000000000) := by
  have hr : 0 ≤ firstRatio 24226 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24226 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24226) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12113 (1/10^6) (1/10^7) ((1068253/500000000000))
      (712/10000) rowEps ≤ (112535401/1000000000000) := by
  have hs : statisticsPayment ≤ (4235787306329/1000000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (108199612527683/1000000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12113 (1/10^6) (1/10^7) ((1068253/500000000000))
      (712/10000) rowEps =
      exp (-((mW 12113 : ℝ)*24226)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12113 : ℝ)*24226)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12113) (mW 12113)).real
      (goodDist 12113 (712/10000))ᶜ ≤ (112535401/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 12113) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (1068253/500000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12113 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (187526407089/250000000000000000)
  k0 := (818898303667961/200000000000000000)
  k6 := (12441558255777937/1000000000000000000)
  ε₁ := 161/10000
  ε₂ := 1118/100000
  s := 46727425/10^8
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  ε₁_pos := by norm_num
  ε₂_pos := by norm_num
  s_pos := by norm_num
  norm_lower := (window_guards (n := 12113) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12113) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((112535401/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12113 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12113) internalParameters :=
  BstLean.Part227.worldPackage (n := 12113) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (112535401/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12113) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part281.world12113.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part281.world12113, width]

theorem frame_payment : internalParameters.frame ≤ Part281.world12113.frame := by
  exact frame.2.trans (by norm_num [Part281.world12113])

theorem moment_payment : internalParameters.moment ≤ Part281.world12113.moment := by
  exact moment.2.trans (by norm_num [Part281.world12113])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (239952691/200000000000) ∧
    internalParameters.frame ≤ (634144189983/1000000000000) ∧
    internalParameters.moment ≤ (2665853061/250000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12113) (Part281.world12113) where
  hidden := internalWorld.hidden
  hidden_measurable := internalWorld.hidden_measurable
  scale := internalWorld.scale
  scale_measurable := internalWorld.scale_measurable
  scale_eq := internalWorld.scale_eq
  calibration := internalWorld.calibration
  calibration_measurable := internalWorld.calibration_measurable
  hidden_charge := internalWorld.hidden_charge.trans hidden_payment
  product_window := by
    intro θ hθ
    obtain ⟨hl, hu⟩ := internalWorld.product_window θ hθ
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part281.world12113]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part281.world12113])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part281.world12113]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part281.world12113]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12113).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12113).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part281.WorldRow12113
namespace BstLean.Part281.WorldRow12114
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
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
    exp (-((mW 12114 : ℝ)*24228)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12114 : ℝ)*24228)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12114 : ℝ)*24228)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12114 : ℝ)*24228)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24228 (mW 12114) i /
      (rowEps i * e1MeanBounds 24228 (mW 12114) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24228 (mW 12114) (1/10^6) (1/10^7) rowEps ≤ (2136327/1000000000000) := by
  have hr : 0 ≤ firstRatio 24228 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24228 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24228) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12114 (1/10^6) (1/10^7) ((2136327/1000000000000))
      (712/10000) rowEps ≤ (22503201/200000000000) := by
  have hs : statisticsPayment ≤ (132345800263/31250000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (54090468938971/500000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12114 (1/10^6) (1/10^7) ((2136327/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 12114 : ℝ)*24228)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12114 : ℝ)*24228)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12114) (mW 12114)).real
      (goodDist 12114 (712/10000))ᶜ ≤ (22503201/200000000000) := by
  apply le_trans (concrete_distance_charge (n := 12114) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (2136327/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12114 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (750012749437/1000000000000000000)
  k0 := (2047119009114819/500000000000000000)
  k6 := (6220522362678751/500000000000000000)
  ε₁ := 161/10000
  ε₂ := 1118/100000
  s := 46727425/10^8
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  ε₁_pos := by norm_num
  ε₂_pos := by norm_num
  s_pos := by norm_num
  norm_lower := (window_guards (n := 12114) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12114) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((22503201/200000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12114 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12114) internalParameters :=
  BstLean.Part227.worldPackage (n := 12114) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (22503201/200000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12114) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part281.world12114.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part281.world12114, width]

theorem frame_payment : internalParameters.frame ≤ Part281.world12114.frame := by
  exact frame.2.trans (by norm_num [Part281.world12114])

theorem moment_payment : internalParameters.moment ≤ Part281.world12114.moment := by
  exact moment.2.trans (by norm_num [Part281.world12114])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1199712327/1000000000000) ∧
    internalParameters.frame ≤ (634128917861/1000000000000) ∧
    internalParameters.moment ≤ (10661107079/1000000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12114) (Part281.world12114) where
  hidden := internalWorld.hidden
  hidden_measurable := internalWorld.hidden_measurable
  scale := internalWorld.scale
  scale_measurable := internalWorld.scale_measurable
  scale_eq := internalWorld.scale_eq
  calibration := internalWorld.calibration
  calibration_measurable := internalWorld.calibration_measurable
  hidden_charge := internalWorld.hidden_charge.trans hidden_payment
  product_window := by
    intro θ hθ
    obtain ⟨hl, hu⟩ := internalWorld.product_window θ hθ
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part281.world12114]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part281.world12114])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part281.world12114]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part281.world12114]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12114).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12114).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part281.WorldRow12114
namespace BstLean.Part281.WorldRow12115
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
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
    exp (-((mW 12115 : ℝ)*24230)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12115 : ℝ)*24230)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12115 : ℝ)*24230)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12115 : ℝ)*24230)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24230 (mW 12115) i /
      (rowEps i * e1MeanBounds 24230 (mW 12115) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24230 (mW 12115) (1/10^6) (1/10^7) rowEps ≤ (2136149/1000000000000) := by
  have hr : 0 ≤ firstRatio 24230 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24230 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24230) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12115 (1/10^6) (1/10^7) ((2136149/1000000000000))
      (712/10000) rowEps ≤ (1124969/10000000000) := by
  have hs : statisticsPayment ≤ (4234344137001/1000000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (54081277073251/500000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12115 (1/10^6) (1/10^7) ((2136149/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 12115 : ℝ)*24230)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12115 : ℝ)*24230)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12115) (mW 12115)).real
      (goodDist 12115 (712/10000))ᶜ ≤ (1124969/10000000000) := by
  apply le_trans (concrete_distance_charge (n := 12115) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (2136149/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12115 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (187479972421/250000000000000000)
  k0 := (4093984554738501/1000000000000000000)
  k6 := (2488106251704071/200000000000000000)
  ε₁ := 161/10000
  ε₂ := 1118/100000
  s := 46727425/10^8
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  ε₁_pos := by norm_num
  ε₂_pos := by norm_num
  s_pos := by norm_num
  norm_lower := (window_guards (n := 12115) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12115) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((1124969/10000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12115 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12115) internalParameters :=
  BstLean.Part227.worldPackage (n := 12115) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (1124969/10000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12115) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part281.world12115.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part281.world12115, width]

theorem frame_payment : internalParameters.frame ≤ Part281.world12115.frame := by
  exact frame.2.trans (by norm_num [Part281.world12115])

theorem moment_payment : internalParameters.moment ≤ Part281.world12115.moment := by
  exact moment.2.trans (by norm_num [Part281.world12115])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (599830607/500000000000) ∧
    internalParameters.frame ≤ (126822729667/200000000000) ∧
    internalParameters.moment ≤ (1065880261/100000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12115) (Part281.world12115) where
  hidden := internalWorld.hidden
  hidden_measurable := internalWorld.hidden_measurable
  scale := internalWorld.scale
  scale_measurable := internalWorld.scale_measurable
  scale_eq := internalWorld.scale_eq
  calibration := internalWorld.calibration
  calibration_measurable := internalWorld.calibration_measurable
  hidden_charge := internalWorld.hidden_charge.trans hidden_payment
  product_window := by
    intro θ hθ
    obtain ⟨hl, hu⟩ := internalWorld.product_window θ hθ
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part281.world12115]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part281.world12115])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part281.world12115]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part281.world12115]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12115).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12115).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part281.WorldRow12115
namespace BstLean.Part281.WorldRow12116
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
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
    exp (-((mW 12116 : ℝ)*24232)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12116 : ℝ)*24232)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12116 : ℝ)*24232)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12116 : ℝ)*24232)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24232 (mW 12116) i /
      (rowEps i * e1MeanBounds 24232 (mW 12116) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24232 (mW 12116) (1/10^6) (1/10^7) rowEps ≤ (2135971/1000000000000) := by
  have hr : 0 ≤ firstRatio 24232 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24232 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24232) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12116 (1/10^6) (1/10^7) ((2135971/1000000000000))
      (712/10000) rowEps ≤ (112477791/1000000000000) := by
  have hs : statisticsPayment ≤ (4233622891989/1000000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (108144166352911/1000000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12116 (1/10^6) (1/10^7) ((2135971/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 12116 : ℝ)*24232)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12116 : ℝ)*24232)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12116) (mW 12116)).real
      (goodDist 12116 (712/10000))ᶜ ≤ (112477791/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 12116) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (2135971/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12116 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (749827049091/1000000000000000000)
  k0 := (2046865563928409/500000000000000000)
  k6 := (99520142842027/8000000000000000)
  ε₁ := 161/10000
  ε₂ := 1118/100000
  s := 46727425/10^8
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  ε₁_pos := by norm_num
  ε₂_pos := by norm_num
  s_pos := by norm_num
  norm_lower := (window_guards (n := 12116) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12116) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((112477791/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12116 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12116) internalParameters :=
  BstLean.Part227.worldPackage (n := 12116) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (112477791/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12116) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part281.world12116.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part281.world12116, width]

theorem frame_payment : internalParameters.frame ≤ Part281.world12116.frame := by
  exact frame.2.trans (by norm_num [Part281.world12116])

theorem moment_payment : internalParameters.moment ≤ Part281.world12116.moment := by
  exact moment.2.trans (by norm_num [Part281.world12116])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (599805057/500000000000) ∧
    internalParameters.frame ≤ (158524595351/250000000000) ∧
    internalParameters.moment ≤ (10656498837/1000000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12116) (Part281.world12116) where
  hidden := internalWorld.hidden
  hidden_measurable := internalWorld.hidden_measurable
  scale := internalWorld.scale
  scale_measurable := internalWorld.scale_measurable
  scale_eq := internalWorld.scale_eq
  calibration := internalWorld.calibration
  calibration_measurable := internalWorld.calibration_measurable
  hidden_charge := internalWorld.hidden_charge.trans hidden_payment
  product_window := by
    intro θ hθ
    obtain ⟨hl, hu⟩ := internalWorld.product_window θ hθ
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part281.world12116]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part281.world12116])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part281.world12116]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part281.world12116]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12116).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12116).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part281.WorldRow12116
namespace BstLean.Part281.WorldRow12117
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
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
    exp (-((mW 12117 : ℝ)*24234)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12117 : ℝ)*24234)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12117 : ℝ)*24234)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12117 : ℝ)*24234)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24234 (mW 12117) i /
      (rowEps i * e1MeanBounds 24234 (mW 12117) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24234 (mW 12117) (1/10^6) (1/10^7) rowEps ≤ (2135793/1000000000000) := by
  have hr : 0 ≤ firstRatio 24234 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24234 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24234) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12117 (1/10^6) (1/10^7) ((2135793/1000000000000))
      (712/10000) rowEps ≤ (56229339/500000000000) := by
  have hs : statisticsPayment ≤ (1058225468321/250000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (27031443625027/250000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12117 (1/10^6) (1/10^7) ((2135793/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 12117 : ℝ)*24234)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12117 : ℝ)*24234)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12117) (mW 12117)).real
      (goodDist 12117 (712/10000))ᶜ ≤ (56229339/500000000000) := by
  apply le_trans (concrete_distance_charge (n := 12117) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (2135793/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12117 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (749734227653/1000000000000000000)
  k0 := (2046738868788869/500000000000000000)
  k6 := (12439504515543447/1000000000000000000)
  ε₁ := 161/10000
  ε₂ := 1118/100000
  s := 46727425/10^8
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  ε₁_pos := by norm_num
  ε₂_pos := by norm_num
  s_pos := by norm_num
  norm_lower := (window_guards (n := 12117) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12117) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((56229339/500000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12117 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12117) internalParameters :=
  BstLean.Part227.worldPackage (n := 12117) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (56229339/500000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12117) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part281.world12117.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part281.world12117, width]

theorem frame_payment : internalParameters.frame ≤ Part281.world12117.frame := by
  exact frame.2.trans (by norm_num [Part281.world12117])

theorem moment_payment : internalParameters.moment ≤ Part281.world12117.moment := by
  exact moment.2.trans (by norm_num [Part281.world12117])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1199559029/1000000000000) ∧
    internalParameters.frame ≤ (317041558533/500000000000) ∧
    internalParameters.moment ≤ (10654195759/1000000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12117) (Part281.world12117) where
  hidden := internalWorld.hidden
  hidden_measurable := internalWorld.hidden_measurable
  scale := internalWorld.scale
  scale_measurable := internalWorld.scale_measurable
  scale_eq := internalWorld.scale_eq
  calibration := internalWorld.calibration
  calibration_measurable := internalWorld.calibration_measurable
  hidden_charge := internalWorld.hidden_charge.trans hidden_payment
  product_window := by
    intro θ hθ
    obtain ⟨hl, hu⟩ := internalWorld.product_window θ hθ
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part281.world12117]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part281.world12117])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part281.world12117]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part281.world12117]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12117).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12117).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part281.WorldRow12117
namespace BstLean.Part281.WorldRow12118
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
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
    exp (-((mW 12118 : ℝ)*24236)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12118 : ℝ)*24236)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12118 : ℝ)*24236)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12118 : ℝ)*24236)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24236 (mW 12118) i /
      (rowEps i * e1MeanBounds 24236 (mW 12118) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24236 (mW 12118) (1/10^6) (1/10^7) rowEps ≤ (1067807/500000000000) := by
  have hr : 0 ≤ firstRatio 24236 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24236 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24236) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12118 (1/10^6) (1/10^7) ((1067807/500000000000))
      (712/10000) rowEps ≤ (56219633/500000000000) := by
  have hs : statisticsPayment ≤ (4232181080789/1000000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (108107083740507/1000000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12118 (1/10^6) (1/10^7) ((1067807/500000000000))
      (712/10000) rowEps =
      exp (-((mW 12118 : ℝ)*24236)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12118 : ℝ)*24236)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12118) (mW 12118)).real
      (goodDist 12118 (712/10000))ᶜ ≤ (56219633/500000000000) := by
  apply le_trans (concrete_distance_charge (n := 12118) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (1067807/500000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12118 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (187410356341/250000000000000000)
  k0 := (2046612191945839/500000000000000000)
  k6 := (6219495619688729/500000000000000000)
  ε₁ := 161/10000
  ε₂ := 1118/100000
  s := 46727425/10^8
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  ε₁_pos := by norm_num
  ε₂_pos := by norm_num
  s_pos := by norm_num
  norm_lower := (window_guards (n := 12118) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12118) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((56219633/500000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12118 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12118) internalParameters :=
  BstLean.Part227.worldPackage (n := 12118) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (56219633/500000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12118) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part281.world12118.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part281.world12118, width]

theorem frame_payment : internalParameters.frame ≤ Part281.world12118.frame := by
  exact frame.2.trans (by norm_num [Part281.world12118])

theorem moment_payment : internalParameters.moment ≤ Part281.world12118.moment := by
  exact moment.2.trans (by norm_num [Part281.world12118])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (599753979/500000000000) ∧
    internalParameters.frame ≤ (634067855321/1000000000000) ∧
    internalParameters.moment ≤ (10651893377/1000000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12118) (Part281.world12118) where
  hidden := internalWorld.hidden
  hidden_measurable := internalWorld.hidden_measurable
  scale := internalWorld.scale
  scale_measurable := internalWorld.scale_measurable
  scale_eq := internalWorld.scale_eq
  calibration := internalWorld.calibration
  calibration_measurable := internalWorld.calibration_measurable
  hidden_charge := internalWorld.hidden_charge.trans hidden_payment
  product_window := by
    intro θ hθ
    obtain ⟨hl, hu⟩ := internalWorld.product_window θ hθ
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part281.world12118]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part281.world12118])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part281.world12118]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part281.world12118]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12118).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12118).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part281.WorldRow12118
namespace BstLean.Part281.WorldRow12119
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
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
    exp (-((mW 12119 : ℝ)*24238)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12119 : ℝ)*24238)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12119 : ℝ)*24238)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12119 : ℝ)*24238)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24238 (mW 12119) i /
      (rowEps i * e1MeanBounds 24238 (mW 12119) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24238 (mW 12119) (1/10^6) (1/10^7) rowEps ≤ (533859/250000000000) := by
  have hr : 0 ≤ firstRatio 24238 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24238 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24238) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12119 (1/10^6) (1/10^7) ((533859/250000000000))
      (712/10000) rowEps ≤ (56210073/500000000000) := by
  have hs : statisticsPayment ≤ (4231460514409/1000000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (108088683804533/1000000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12119 (1/10^6) (1/10^7) ((533859/250000000000))
      (712/10000) rowEps =
      exp (-((mW 12119 : ℝ)*24238)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12119 : ℝ)*24238)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12119) (mW 12119)).real
      (goodDist 12119 (712/10000))ᶜ ≤ (56210073/500000000000) := by
  apply le_trans (concrete_distance_charge (n := 12119) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (533859/250000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12119 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (374774321109/500000000000000000)
  k0 := (4092971066789051/1000000000000000000)
  k6 := (6219239013371149/500000000000000000)
  ε₁ := 161/10000
  ε₂ := 1118/100000
  s := 46727425/10^8
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  ε₁_pos := by norm_num
  ε₂_pos := by norm_num
  s_pos := by norm_num
  norm_lower := (window_guards (n := 12119) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12119) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((56210073/500000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12119 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12119) internalParameters :=
  BstLean.Part227.worldPackage (n := 12119) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (56210073/500000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12119) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part281.world12119.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part281.world12119, width]

theorem frame_payment : internalParameters.frame ≤ Part281.world12119.frame := by
  exact frame.2.trans (by norm_num [Part281.world12119])

theorem moment_payment : internalParameters.moment ≤ Part281.world12119.moment := by
  exact moment.2.trans (by norm_num [Part281.world12119])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1199456901/1000000000000) ∧
    internalParameters.frame ≤ (79256574521/125000000000) ∧
    internalParameters.moment ≤ (1064959169/100000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12119) (Part281.world12119) where
  hidden := internalWorld.hidden
  hidden_measurable := internalWorld.hidden_measurable
  scale := internalWorld.scale
  scale_measurable := internalWorld.scale_measurable
  scale_eq := internalWorld.scale_eq
  calibration := internalWorld.calibration
  calibration_measurable := internalWorld.calibration_measurable
  hidden_charge := internalWorld.hidden_charge.trans hidden_payment
  product_window := by
    intro θ hθ
    obtain ⟨hl, hu⟩ := internalWorld.product_window θ hθ
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part281.world12119]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part281.world12119])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part281.world12119]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part281.world12119]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12119).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12119).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part281.WorldRow12119
namespace BstLean.Part281.WorldRow12120
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
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
    exp (-((mW 12120 : ℝ)*24240)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12120 : ℝ)*24240)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12120 : ℝ)*24240)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12120 : ℝ)*24240)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24240 (mW 12120) i /
      (rowEps i * e1MeanBounds 24240 (mW 12120) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24240 (mW 12120) (1/10^6) (1/10^7) rowEps ≤ (1067629/500000000000) := by
  have hr : 0 ≤ firstRatio 24240 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24240 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24240) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12120 (1/10^6) (1/10^7) ((1067629/500000000000))
      (712/10000) rowEps ≤ (112401021/1000000000000) := by
  have hs : statisticsPayment ≤ (132210630439/31250000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (54035139909099/500000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12120 (1/10^6) (1/10^7) ((1067629/500000000000))
      (712/10000) rowEps =
      exp (-((mW 12120 : ℝ)*24240)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12120 : ℝ)*24240)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12120) (mW 12120)).real
      (goodDist 12120 (712/10000))ᶜ ≤ (112401021/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 12120) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (1067629/500000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12120 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (749455878211/1000000000000000000)
  k0 := (409271778626573/100000000000000000)
  k6 := (2487592975524973/200000000000000000)
  ε₁ := 161/10000
  ε₂ := 1118/100000
  s := 46727425/10^8
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  ε₁_pos := by norm_num
  ε₂_pos := by norm_num
  s_pos := by norm_num
  norm_lower := (window_guards (n := 12120) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12120) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((112401021/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12120 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12120) internalParameters :=
  BstLean.Part227.worldPackage (n := 12120) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (112401021/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12120) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part281.world12120.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part281.world12120, width]

theorem frame_payment : internalParameters.frame ≤ Part281.world12120.frame := by
  exact frame.2.trans (by norm_num [Part281.world12120])

theorem moment_payment : internalParameters.moment ≤ Part281.world12120.moment := by
  exact moment.2.trans (by norm_num [Part281.world12120])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1199405859/1000000000000) ∧
    internalParameters.frame ≤ (634037339607/1000000000000) ∧
    internalParameters.moment ≤ (10647290697/1000000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12120) (Part281.world12120) where
  hidden := internalWorld.hidden
  hidden_measurable := internalWorld.hidden_measurable
  scale := internalWorld.scale
  scale_measurable := internalWorld.scale_measurable
  scale_eq := internalWorld.scale_eq
  calibration := internalWorld.calibration
  calibration_measurable := internalWorld.calibration_measurable
  hidden_charge := internalWorld.hidden_charge.trans hidden_payment
  product_window := by
    intro θ hθ
    obtain ⟨hl, hu⟩ := internalWorld.product_window θ hθ
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part281.world12120]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part281.world12120])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part281.world12120]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part281.world12120]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12120).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12120).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part281.WorldRow12120
namespace BstLean.Part281.WorldRow12121
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
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
    exp (-((mW 12121 : ℝ)*24242)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12121 : ℝ)*24242)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12121 : ℝ)*24242)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12121 : ℝ)*24242)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24242 (mW 12121) i /
      (rowEps i * e1MeanBounds 24242 (mW 12121) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24242 (mW 12121) (1/10^6) (1/10^7) rowEps ≤ (53377/25000000000) := by
  have hr : 0 ≤ firstRatio 24242 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24242 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24242) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12121 (1/10^6) (1/10^7) ((53377/25000000000))
      (712/10000) rowEps ≤ (112381893/1000000000000) := by
  have hs : statisticsPayment ≤ (4230020059611/1000000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (54025935892223/500000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12121 (1/10^6) (1/10^7) ((53377/25000000000))
      (712/10000) rowEps =
      exp (-((mW 12121 : ℝ)*24242)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12121 : ℝ)*24242)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12121) (mW 12121)).real
      (goodDist 12121 (712/10000))ᶜ ≤ (112381893/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 12121) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (53377/25000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12121 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (93670391667/125000000000000000)
  k0 := (409246454230939/100000000000000000)
  k6 := (2487490358402411/200000000000000000)
  ε₁ := 161/10000
  ε₂ := 1118/100000
  s := 46727425/10^8
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  ε₁_pos := by norm_num
  ε₂_pos := by norm_num
  s_pos := by norm_num
  norm_lower := (window_guards (n := 12121) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12121) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((112381893/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12121 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12121) internalParameters :=
  BstLean.Part227.worldPackage (n := 12121) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (112381893/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12121) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part281.world12121.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part281.world12121, width]

theorem frame_payment : internalParameters.frame ≤ Part281.world12121.frame := by
  exact frame.2.trans (by norm_num [Part281.world12121])

theorem moment_payment : internalParameters.moment ≤ Part281.world12121.moment := by
  exact moment.2.trans (by norm_num [Part281.world12121])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (119935483/100000000000) ∧
    internalParameters.frame ≤ (634022085637/1000000000000) ∧
    internalParameters.moment ≤ (10644990399/1000000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12121) (Part281.world12121) where
  hidden := internalWorld.hidden
  hidden_measurable := internalWorld.hidden_measurable
  scale := internalWorld.scale
  scale_measurable := internalWorld.scale_measurable
  scale_eq := internalWorld.scale_eq
  calibration := internalWorld.calibration
  calibration_measurable := internalWorld.calibration_measurable
  hidden_charge := internalWorld.hidden_charge.trans hidden_payment
  product_window := by
    intro θ hθ
    obtain ⟨hl, hu⟩ := internalWorld.product_window θ hθ
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part281.world12121]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part281.world12121])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part281.world12121]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part281.world12121]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12121).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12121).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part281.WorldRow12121
namespace BstLean.Part281.WorldRow12122
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
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
    exp (-((mW 12122 : ℝ)*24244)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12122 : ℝ)*24244)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12122 : ℝ)*24244)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12122 : ℝ)*24244)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24244 (mW 12122) i /
      (rowEps i * e1MeanBounds 24244 (mW 12122) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24244 (mW 12122) (1/10^6) (1/10^7) rowEps ≤ (1067451/500000000000) := by
  have hr : 0 ≤ firstRatio 24244 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24244 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24244) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12122 (1/10^6) (1/10^7) ((1067451/500000000000))
      (712/10000) rowEps ≤ (112362761/1000000000000) := by
  have hs : statisticsPayment ≤ (4229300171001/1000000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (54016729853111/500000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12122 (1/10^6) (1/10^7) ((1067451/500000000000))
      (712/10000) rowEps =
      exp (-((mW 12122 : ℝ)*24244)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12122 : ℝ)*24244)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12122) (mW 12122)).real
      (goodDist 12122 (712/10000))ᶜ ≤ (112362761/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 12122) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (1067451/500000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12122 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (187317601897/250000000000000000)
  k0 := (4092211334913167/1000000000000000000)
  k6 := (12436938769890773/1000000000000000000)
  ε₁ := 161/10000
  ε₂ := 1118/100000
  s := 46727425/10^8
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  ε₁_pos := by norm_num
  ε₂_pos := by norm_num
  s_pos := by norm_num
  norm_lower := (window_guards (n := 12122) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12122) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((112362761/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12122 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12122) internalParameters :=
  BstLean.Part227.worldPackage (n := 12122) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (112362761/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12122) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part281.world12122.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part281.world12122, width]

theorem frame_payment : internalParameters.frame ≤ Part281.world12122.frame := by
  exact frame.2.trans (by norm_num [Part281.world12122])

theorem moment_payment : internalParameters.moment ≤ Part281.world12122.moment := by
  exact moment.2.trans (by norm_num [Part281.world12122])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (149912977/125000000000) ∧
    internalParameters.frame ≤ (634006834257/1000000000000) ∧
    internalParameters.moment ≤ (2660672699/250000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12122) (Part281.world12122) where
  hidden := internalWorld.hidden
  hidden_measurable := internalWorld.hidden_measurable
  scale := internalWorld.scale
  scale_measurable := internalWorld.scale_measurable
  scale_eq := internalWorld.scale_eq
  calibration := internalWorld.calibration
  calibration_measurable := internalWorld.calibration_measurable
  hidden_charge := internalWorld.hidden_charge.trans hidden_payment
  product_window := by
    intro θ hθ
    obtain ⟨hl, hu⟩ := internalWorld.product_window θ hθ
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part281.world12122]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part281.world12122])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part281.world12122]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part281.world12122]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12122).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12122).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part281.WorldRow12122
namespace BstLean.Part281.WorldRow12123
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
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
    exp (-((mW 12123 : ℝ)*24246)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12123 : ℝ)*24246)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12123 : ℝ)*24246)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12123 : ℝ)*24246)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24246 (mW 12123) i /
      (rowEps i * e1MeanBounds 24246 (mW 12123) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24246 (mW 12123) (1/10^6) (1/10^7) rowEps ≤ (533681/250000000000) := by
  have hr : 0 ≤ firstRatio 24246 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24246 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24246) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12123 (1/10^6) (1/10^7) ((533681/250000000000))
      (712/10000) rowEps ≤ (56171813/500000000000) := by
  have hs : statisticsPayment ≤ (2114290254061/500000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (13501880448309/125000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12123 (1/10^6) (1/10^7) ((533681/250000000000))
      (712/10000) rowEps =
      exp (-((mW 12123 : ℝ)*24246)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12123 : ℝ)*24246)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12123) (mW 12123)).real
      (goodDist 12123 (712/10000))ᶜ ≤ (56171813/500000000000) := by
  apply le_trans (concrete_distance_charge (n := 12123) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (533681/250000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12123 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (749177700961/1000000000000000000)
  k0 := (2045979082033731/500000000000000000)
  k6 := (497457032449917/40000000000000000)
  ε₁ := 161/10000
  ε₂ := 1118/100000
  s := 46727425/10^8
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  ε₁_pos := by norm_num
  ε₂_pos := by norm_num
  s_pos := by norm_num
  norm_lower := (window_guards (n := 12123) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12123) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((56171813/500000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12123 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12123) internalParameters :=
  BstLean.Part227.worldPackage (n := 12123) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (56171813/500000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12123) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part281.world12123.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part281.world12123, width]

theorem frame_payment : internalParameters.frame ≤ Part281.world12123.frame := by
  exact frame.2.trans (by norm_num [Part281.world12123])

theorem moment_payment : internalParameters.moment ≤ Part281.world12123.moment := by
  exact moment.2.trans (by norm_num [Part281.world12123])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (74953301/62500000000) ∧
    internalParameters.frame ≤ (633991585467/1000000000000) ∧
    internalParameters.moment ≤ (5320195943/500000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12123) (Part281.world12123) where
  hidden := internalWorld.hidden
  hidden_measurable := internalWorld.hidden_measurable
  scale := internalWorld.scale
  scale_measurable := internalWorld.scale_measurable
  scale_eq := internalWorld.scale_eq
  calibration := internalWorld.calibration
  calibration_measurable := internalWorld.calibration_measurable
  hidden_charge := internalWorld.hidden_charge.trans hidden_payment
  product_window := by
    intro θ hθ
    obtain ⟨hl, hu⟩ := internalWorld.product_window θ hθ
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part281.world12123]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part281.world12123])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part281.world12123]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part281.world12123]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12123).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12123).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part281.WorldRow12123
namespace BstLean.Part281.WorldRow12124
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
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
    exp (-((mW 12124 : ℝ)*24248)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12124 : ℝ)*24248)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12124 : ℝ)*24248)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12124 : ℝ)*24248)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24248 (mW 12124) i /
      (rowEps i * e1MeanBounds 24248 (mW 12124) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24248 (mW 12124) (1/10^6) (1/10^7) rowEps ≤ (1067273/500000000000) := by
  have hr : 0 ≤ firstRatio 24248 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24248 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24248) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12124 (1/10^6) (1/10^7) ((1067273/500000000000))
      (712/10000) rowEps ≤ (56162243/500000000000) := by
  have hs : statisticsPayment ≤ (26424131693/6250000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (107996623428143/1000000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12124 (1/10^6) (1/10^7) ((1067273/500000000000))
      (712/10000) rowEps =
      exp (-((mW 12124 : ℝ)*24248)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12124 : ℝ)*24248)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12124) (mW 12124)).real
      (goodDist 12124 (712/10000))ᶜ ≤ (56162243/500000000000) := by
  apply le_trans (concrete_distance_charge (n := 12124) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (1067273/500000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12124 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (749085013451/1000000000000000000)
  k0 := (818341005953627/200000000000000000)
  k6 := (12435912916070421/1000000000000000000)
  ε₁ := 161/10000
  ε₂ := 1118/100000
  s := 46727425/10^8
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  ε₁_pos := by norm_num
  ε₂_pos := by norm_num
  s_pos := by norm_num
  norm_lower := (window_guards (n := 12124) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12124) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((56162243/500000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12124 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12124) internalParameters :=
  BstLean.Part227.worldPackage (n := 12124) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (56162243/500000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12124) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part281.world12124.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part281.world12124, width]

theorem frame_payment : internalParameters.frame ≤ Part281.world12124.frame := by
  exact frame.2.trans (by norm_num [Part281.world12124])

theorem moment_payment : internalParameters.moment ≤ Part281.world12124.moment := by
  exact moment.2.trans (by norm_num [Part281.world12124])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (119920183/100000000000) ∧
    internalParameters.frame ≤ (126795267853/200000000000) ∧
    internalParameters.moment ≤ (1063809367/100000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12124) (Part281.world12124) where
  hidden := internalWorld.hidden
  hidden_measurable := internalWorld.hidden_measurable
  scale := internalWorld.scale
  scale_measurable := internalWorld.scale_measurable
  scale_eq := internalWorld.scale_eq
  calibration := internalWorld.calibration
  calibration_measurable := internalWorld.calibration_measurable
  hidden_charge := internalWorld.hidden_charge.trans hidden_payment
  product_window := by
    intro θ hθ
    obtain ⟨hl, hu⟩ := internalWorld.product_window θ hθ
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part281.world12124]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part281.world12124])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part281.world12124]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part281.world12124]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12124).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12124).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part281.WorldRow12124
namespace BstLean.Part281.WorldRow12125
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
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
    exp (-((mW 12125 : ℝ)*24250)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12125 : ℝ)*24250)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12125 : ℝ)*24250)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12125 : ℝ)*24250)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24250 (mW 12125) i /
      (rowEps i * e1MeanBounds 24250 (mW 12125) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24250 (mW 12125) (1/10^6) (1/10^7) rowEps ≤ (66699/31250000000) := by
  have hr : 0 ≤ firstRatio 24250 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24250 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24250) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12125 (1/10^6) (1/10^7) ((66699/31250000000))
      (712/10000) rowEps ≤ (112305343/1000000000000) := by
  have hs : statisticsPayment ≤ (2113570929589/500000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (21595639846837/200000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12125 (1/10^6) (1/10^7) ((66699/31250000000))
      (712/10000) rowEps =
      exp (-((mW 12125 : ℝ)*24250)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12125 : ℝ)*24250)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12125) (mW 12125)).real
      (goodDist 12125 (712/10000))ᶜ ≤ (112305343/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 12125) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (66699/31250000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12125 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (14979846901/20000000000000000)
  k0 := (4091451932000119/1000000000000000000)
  k6 := (6217700042172587/500000000000000000)
  ε₁ := 161/10000
  ε₂ := 1118/100000
  s := 46727425/10^8
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  ε₁_pos := by norm_num
  ε₂_pos := by norm_num
  s_pos := by norm_num
  norm_lower := (window_guards (n := 12125) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12125) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((112305343/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12125 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12125) internalParameters :=
  BstLean.Part227.worldPackage (n := 12125) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (112305343/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12125) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part281.world12125.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part281.world12125, width]

theorem frame_payment : internalParameters.frame ≤ Part281.world12125.frame := by
  exact frame.2.trans (by norm_num [Part281.world12125])

theorem moment_payment : internalParameters.moment ≤ Part281.world12125.moment := by
  exact moment.2.trans (by norm_num [Part281.world12125])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (599575429/500000000000) ∧
    internalParameters.frame ≤ (158490273913/250000000000) ∧
    internalParameters.moment ≤ (2658949037/250000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12125) (Part281.world12125) where
  hidden := internalWorld.hidden
  hidden_measurable := internalWorld.hidden_measurable
  scale := internalWorld.scale
  scale_measurable := internalWorld.scale_measurable
  scale_eq := internalWorld.scale_eq
  calibration := internalWorld.calibration
  calibration_measurable := internalWorld.calibration_measurable
  hidden_charge := internalWorld.hidden_charge.trans hidden_payment
  product_window := by
    intro θ hθ
    obtain ⟨hl, hu⟩ := internalWorld.product_window θ hθ
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part281.world12125]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part281.world12125])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part281.world12125]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part281.world12125]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12125).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12125).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part281.WorldRow12125
namespace BstLean.Part281.WorldRow12126
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
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
    exp (-((mW 12126 : ℝ)*24252)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12126 : ℝ)*24252)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12126 : ℝ)*24252)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12126 : ℝ)*24252)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24252 (mW 12126) i /
      (rowEps i * e1MeanBounds 24252 (mW 12126) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24252 (mW 12126) (1/10^6) (1/10^7) rowEps ≤ (213419/100000000000) := by
  have hr : 0 ≤ firstRatio 24252 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24252 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24252) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12126 (1/10^6) (1/10^7) ((213419/100000000000))
      (712/10000) rowEps ≤ (22457239/200000000000) := by
  have hs : statisticsPayment ≤ (4226422872921/1000000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (107959771007547/1000000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12126 (1/10^6) (1/10^7) ((213419/100000000000))
      (712/10000) rowEps =
      exp (-((mW 12126 : ℝ)*24252)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12126 : ℝ)*24252)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12126) (mW 12126)).real
      (goodDist 12126 (712/10000))ᶜ ≤ (22457239/200000000000) := by
  apply le_trans (concrete_distance_charge (n := 12126) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (213419/100000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12126 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (149779939151/200000000000000000)
  k0 := (4091198870761999/1000000000000000000)
  k6 := (388590228626847/31250000000000000)
  ε₁ := 161/10000
  ε₂ := 1118/100000
  s := 46727425/10^8
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  ε₁_pos := by norm_num
  ε₂_pos := by norm_num
  s_pos := by norm_num
  norm_lower := (window_guards (n := 12126) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12126) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((22457239/200000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12126 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12126) internalParameters :=
  BstLean.Part227.worldPackage (n := 12126) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (22457239/200000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12126) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part281.world12126.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part281.world12126, width]

theorem frame_payment : internalParameters.frame ≤ Part281.world12126.frame := by
  exact frame.2.trans (by norm_num [Part281.world12126])

theorem moment_payment : internalParameters.moment ≤ Part281.world12126.moment := by
  exact moment.2.trans (by norm_num [Part281.world12126])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1199099901/1000000000000) ∧
    internalParameters.frame ≤ (316972927313/500000000000) ∧
    internalParameters.moment ≤ (5316749659/500000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12126) (Part281.world12126) where
  hidden := internalWorld.hidden
  hidden_measurable := internalWorld.hidden_measurable
  scale := internalWorld.scale
  scale_measurable := internalWorld.scale_measurable
  scale_eq := internalWorld.scale_eq
  calibration := internalWorld.calibration
  calibration_measurable := internalWorld.calibration_measurable
  hidden_charge := internalWorld.hidden_charge.trans hidden_payment
  product_window := by
    intro θ hθ
    obtain ⟨hl, hu⟩ := internalWorld.product_window θ hθ
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part281.world12126]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part281.world12126])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part281.world12126]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part281.world12126]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12126).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12126).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part281.WorldRow12126
namespace BstLean.Part281.WorldRow12127
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
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
    exp (-((mW 12127 : ℝ)*24254)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12127 : ℝ)*24254)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12127 : ℝ)*24254)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12127 : ℝ)*24254)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24254 (mW 12127) i /
      (rowEps i * e1MeanBounds 24254 (mW 12127) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24254 (mW 12127) (1/10^6) (1/10^7) rowEps ≤ (533503/250000000000) := by
  have hr : 0 ≤ firstRatio 24254 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24254 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24254) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12127 (1/10^6) (1/10^7) ((533503/250000000000))
      (712/10000) rowEps ≤ (28066761/250000000000) := by
  have hs : statisticsPayment ≤ (2112852056007/500000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (5397066937559/50000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12127 (1/10^6) (1/10^7) ((533503/250000000000))
      (712/10000) rowEps =
      exp (-((mW 12127 : ℝ)*24254)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12127 : ℝ)*24254)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12127) (mW 12127)).real
      (goodDist 12127 (712/10000))ᶜ ≤ (28066761/250000000000) := by
  apply le_trans (concrete_distance_charge (n := 12127) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (533503/250000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12127 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (748807065559/1000000000000000000)
  k0 := (4090945846041433/1000000000000000000)
  k6 := (3108593652799783/250000000000000000)
  ε₁ := 161/10000
  ε₂ := 1118/100000
  s := 46727425/10^8
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  ε₁_pos := by norm_num
  ε₂_pos := by norm_num
  s_pos := by norm_num
  norm_lower := (window_guards (n := 12127) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12127) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((28066761/250000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12127 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12127) internalParameters :=
  BstLean.Part227.worldPackage (n := 12127) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (28066761/250000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12127) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part281.world12127.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part281.world12127, width]

theorem frame_payment : internalParameters.frame ≤ Part281.world12127.frame := by
  exact frame.2.trans (by norm_num [Part281.world12127])

theorem moment_payment : internalParameters.moment ≤ Part281.world12127.moment := by
  exact moment.2.trans (by norm_num [Part281.world12127])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1199048957/1000000000000) ∧
    internalParameters.frame ≤ (633930616187/1000000000000) ∧
    internalParameters.moment ≤ (5315601591/500000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12127) (Part281.world12127) where
  hidden := internalWorld.hidden
  hidden_measurable := internalWorld.hidden_measurable
  scale := internalWorld.scale
  scale_measurable := internalWorld.scale_measurable
  scale_eq := internalWorld.scale_eq
  calibration := internalWorld.calibration
  calibration_measurable := internalWorld.calibration_measurable
  hidden_charge := internalWorld.hidden_charge.trans hidden_payment
  product_window := by
    intro θ hθ
    obtain ⟨hl, hu⟩ := internalWorld.product_window θ hθ
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part281.world12127]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part281.world12127])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part281.world12127]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part281.world12127]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12127).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12127).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part281.WorldRow12127
namespace BstLean.Part281.WorldRow12128
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
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
    exp (-((mW 12128 : ℝ)*24256)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12128 : ℝ)*24256)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12128 : ℝ)*24256)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12128 : ℝ)*24256)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24256 (mW 12128) i /
      (rowEps i * e1MeanBounds 24256 (mW 12128) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24256 (mW 12128) (1/10^6) (1/10^7) rowEps ≤ (1066917/500000000000) := by
  have hr : 0 ≤ firstRatio 24256 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24256 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24256) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12128 (1/10^6) (1/10^7) ((1066917/500000000000))
      (712/10000) rowEps ≤ (11224789/100000000000) := by
  have hs : statisticsPayment ≤ (4224985576361/1000000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (107922902468037/1000000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12128 (1/10^6) (1/10^7) ((1066917/500000000000))
      (712/10000) rowEps =
      exp (-((mW 12128 : ℝ)*24256)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12128 : ℝ)*24256)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12128) (mW 12128)).real
      (goodDist 12128 (712/10000))ᶜ ≤ (11224789/100000000000) := by
  apply le_trans (concrete_distance_charge (n := 12128) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (1066917/500000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12128 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (748714454457/1000000000000000000)
  k0 := (2045346428915769/500000000000000000)
  k6 := (6216930984876091/500000000000000000)
  ε₁ := 161/10000
  ε₂ := 1118/100000
  s := 46727425/10^8
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  ε₁_pos := by norm_num
  ε₂_pos := by norm_num
  s_pos := by norm_num
  norm_lower := (window_guards (n := 12128) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12128) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((11224789/100000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12128 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12128) internalParameters :=
  BstLean.Part227.worldPackage (n := 12128) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (11224789/100000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12128) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part281.world12128.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part281.world12128, width]

theorem frame_payment : internalParameters.frame ≤ Part281.world12128.frame := by
  exact frame.2.trans (by norm_num [Part281.world12128])

theorem moment_payment : internalParameters.moment ≤ Part281.world12128.moment := by
  exact moment.2.trans (by norm_num [Part281.world12128])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (299749507/250000000000) ∧
    internalParameters.frame ≤ (633915380333/1000000000000) ∧
    internalParameters.moment ≤ (5314453869/500000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12128) (Part281.world12128) where
  hidden := internalWorld.hidden
  hidden_measurable := internalWorld.hidden_measurable
  scale := internalWorld.scale
  scale_measurable := internalWorld.scale_measurable
  scale_eq := internalWorld.scale_eq
  calibration := internalWorld.calibration
  calibration_measurable := internalWorld.calibration_measurable
  hidden_charge := internalWorld.hidden_charge.trans hidden_payment
  product_window := by
    intro θ hθ
    obtain ⟨hl, hu⟩ := internalWorld.product_window θ hθ
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part281.world12128]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part281.world12128])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part281.world12128]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part281.world12128]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12128).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12128).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part281.WorldRow12128
namespace BstLean.Part281.WorldRow12129
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
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
    exp (-((mW 12129 : ℝ)*24258)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12129 : ℝ)*24258)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12129 : ℝ)*24258)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12129 : ℝ)*24258)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24258 (mW 12129) i /
      (rowEps i * e1MeanBounds 24258 (mW 12129) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24258 (mW 12129) (1/10^6) (1/10^7) rowEps ≤ (266707/125000000000) := by
  have hr : 0 ≤ firstRatio 24258 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24258 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24258) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12129 (1/10^6) (1/10^7) ((266707/125000000000))
      (712/10000) rowEps ≤ (112228731/1000000000000) := by
  have hs : statisticsPayment ≤ (2112133632933/500000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (107904462161073/1000000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12129 (1/10^6) (1/10^7) ((266707/125000000000))
      (712/10000) rowEps =
      exp (-((mW 12129 : ℝ)*24258)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12129 : ℝ)*24258)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12129) (mW 12129)).real
      (goodDist 12129 (712/10000))ᶜ ≤ (112228731/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 12129) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (266707/125000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12129 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (187155465611/250000000000000000)
  k0 := (1022609976531357/250000000000000000)
  k6 := (2486669878341037/200000000000000000)
  ε₁ := 161/10000
  ε₂ := 1118/100000
  s := 46727425/10^8
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  ε₁_pos := by norm_num
  ε₂_pos := by norm_num
  s_pos := by norm_num
  norm_lower := (window_guards (n := 12129) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12129) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((112228731/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12129 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12129) internalParameters :=
  BstLean.Part227.worldPackage (n := 12129) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (112228731/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12129) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part281.world12129.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part281.world12129, width]

theorem frame_payment : internalParameters.frame ≤ Part281.world12129.frame := by
  exact frame.2.trans (by norm_num [Part281.world12129])

theorem moment_payment : internalParameters.moment ≤ Part281.world12129.moment := by
  exact moment.2.trans (by norm_num [Part281.world12129])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1198947113/1000000000000) ∧
    internalParameters.frame ≤ (126780029413/200000000000) ∧
    internalParameters.moment ≤ (5313306493/500000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12129) (Part281.world12129) where
  hidden := internalWorld.hidden
  hidden_measurable := internalWorld.hidden_measurable
  scale := internalWorld.scale
  scale_measurable := internalWorld.scale_measurable
  scale_eq := internalWorld.scale_eq
  calibration := internalWorld.calibration
  calibration_measurable := internalWorld.calibration_measurable
  hidden_charge := internalWorld.hidden_charge.trans hidden_payment
  product_window := by
    intro θ hθ
    obtain ⟨hl, hu⟩ := internalWorld.product_window θ hθ
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part281.world12129]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part281.world12129])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part281.world12129]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part281.world12129]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12129).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12129).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part281.WorldRow12129
namespace BstLean.Part281.WorldRow12130
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
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
    exp (-((mW 12130 : ℝ)*24260)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12130 : ℝ)*24260)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12130 : ℝ)*24260)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12130 : ℝ)*24260)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24260 (mW 12130) i /
      (rowEps i * e1MeanBounds 24260 (mW 12130) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24260 (mW 12130) (1/10^6) (1/10^7) rowEps ≤ (1066739/500000000000) := by
  have hr : 0 ≤ firstRatio 24260 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24260 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24260) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12130 (1/10^6) (1/10^7) ((1066739/500000000000))
      (712/10000) rowEps ≤ (112209569/1000000000000) := by
  have hs : statisticsPayment ≤ (844709836087/200000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (53943008916621/500000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12130 (1/10^6) (1/10^7) ((1066739/500000000000))
      (712/10000) rowEps =
      exp (-((mW 12130 : ℝ)*24260)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12130 : ℝ)*24260)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12130) (mW 12130)).real
      (goodDist 12130 (712/10000))ᶜ ≤ (112209569/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 12130) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (1066739/500000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12130 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (748529289513/1000000000000000000)
  k0 := (127818343465961/31250000000000000)
  k6 := (12432836877045073/1000000000000000000)
  ε₁ := 161/10000
  ε₂ := 1118/100000
  s := 46727425/10^8
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  ε₁_pos := by norm_num
  ε₂_pos := by norm_num
  s_pos := by norm_num
  norm_lower := (window_guards (n := 12130) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12130) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((112209569/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12130 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12130) internalParameters :=
  BstLean.Part227.worldPackage (n := 12130) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (112209569/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12130) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part281.world12130.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part281.world12130, width]

theorem frame_payment : internalParameters.frame ≤ Part281.world12130.frame := by
  exact frame.2.trans (by norm_num [Part281.world12130])

theorem moment_payment : internalParameters.moment ≤ Part281.world12130.moment := by
  exact moment.2.trans (by norm_num [Part281.world12130])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (299724053/250000000000) ∧
    internalParameters.frame ≤ (316942458191/500000000000) ∧
    internalParameters.moment ≤ (10624318927/1000000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12130) (Part281.world12130) where
  hidden := internalWorld.hidden
  hidden_measurable := internalWorld.hidden_measurable
  scale := internalWorld.scale
  scale_measurable := internalWorld.scale_measurable
  scale_eq := internalWorld.scale_eq
  calibration := internalWorld.calibration
  calibration_measurable := internalWorld.calibration_measurable
  hidden_charge := internalWorld.hidden_charge.trans hidden_payment
  product_window := by
    intro θ hθ
    obtain ⟨hl, hu⟩ := internalWorld.product_window θ hθ
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part281.world12130]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part281.world12130])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part281.world12130]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part281.world12130]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12130).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12130).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part281.WorldRow12130
namespace BstLean.Part281.WorldRow12131
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
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
    exp (-((mW 12131 : ℝ)*24262)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12131 : ℝ)*24262)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12131 : ℝ)*24262)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12131 : ℝ)*24262)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24262 (mW 12131) i /
      (rowEps i * e1MeanBounds 24262 (mW 12131) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24262 (mW 12131) (1/10^6) (1/10^7) rowEps ≤ (21333/10000000000) := by
  have hr : 0 ≤ firstRatio 24262 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24262 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24262) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12131 (1/10^6) (1/10^7) ((21333/10000000000))
      (712/10000) rowEps ≤ (56095201/500000000000) := by
  have hs : statisticsPayment ≤ (1055707829993/250000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (8629405559/80000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12131 (1/10^6) (1/10^7) ((21333/10000000000))
      (712/10000) rowEps =
      exp (-((mW 12131 : ℝ)*24262)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12131 : ℝ)*24262)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12131) (mW 12131)).real
      (goodDist 12131 (712/10000))ᶜ ≤ (56095201/500000000000) := by
  apply le_trans (concrete_distance_charge (n := 12131) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (21333/10000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12131 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (37421836783/50000000000000000)
  k0 := (81798682243667/20000000000000000)
  k6 := (12432324425758783/1000000000000000000)
  ε₁ := 161/10000
  ε₂ := 1118/100000
  s := 46727425/10^8
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  ε₁_pos := by norm_num
  ε₂_pos := by norm_num
  s_pos := by norm_num
  norm_lower := (window_guards (n := 12131) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12131) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((56095201/500000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12131 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12131) internalParameters :=
  BstLean.Part227.worldPackage (n := 12131) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (56095201/500000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12131) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part281.world12131.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part281.world12131, width]

theorem frame_payment : internalParameters.frame ≤ Part281.world12131.frame := by
  exact frame.2.trans (by norm_num [Part281.world12131])

theorem moment_payment : internalParameters.moment ≤ Part281.world12131.moment := by
  exact moment.2.trans (by norm_num [Part281.world12131])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (47953813/40000000000) ∧
    internalParameters.frame ≤ (633869688283/1000000000000) ∧
    internalParameters.moment ≤ (265550639/25000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12131) (Part281.world12131) where
  hidden := internalWorld.hidden
  hidden_measurable := internalWorld.hidden_measurable
  scale := internalWorld.scale
  scale_measurable := internalWorld.scale_measurable
  scale_eq := internalWorld.scale_eq
  calibration := internalWorld.calibration
  calibration_measurable := internalWorld.calibration_measurable
  hidden_charge := internalWorld.hidden_charge.trans hidden_payment
  product_window := by
    intro θ hθ
    obtain ⟨hl, hu⟩ := internalWorld.product_window θ hθ
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part281.world12131]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part281.world12131])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part281.world12131]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part281.world12131]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12131).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12131).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part281.WorldRow12131
namespace BstLean.Part281.WorldRow12132
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
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
    exp (-((mW 12132 : ℝ)*24264)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12132 : ℝ)*24264)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12132 : ℝ)*24264)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12132 : ℝ)*24264)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24264 (mW 12132) i /
      (rowEps i * e1MeanBounds 24264 (mW 12132) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24264 (mW 12132) (1/10^6) (1/10^7) rowEps ≤ (1066561/500000000000) := by
  have hr : 0 ≤ firstRatio 24264 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24264 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24264) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12132 (1/10^6) (1/10^7) ((1066561/500000000000))
      (712/10000) rowEps ≤ (3505351/31250000000) := by
  have hs : statisticsPayment ≤ (4222113684381/1000000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (107849117126807/1000000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12132 (1/10^6) (1/10^7) ((1066561/500000000000))
      (712/10000) rowEps =
      exp (-((mW 12132 : ℝ)*24264)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12132 : ℝ)*24264)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12132) (mW 12132)).real
      (goodDist 12132 (712/10000))ᶜ ≤ (3505351/31250000000) := by
  apply le_trans (concrete_distance_charge (n := 12132) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (1066561/500000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12132 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (374172100439/500000000000000000)
  k0 := (2044840634965431/500000000000000000)
  k6 := (2486362407566651/200000000000000000)
  ε₁ := 161/10000
  ε₂ := 1118/100000
  s := 46727425/10^8
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  ε₁_pos := by norm_num
  ε₂_pos := by norm_num
  s_pos := by norm_num
  norm_lower := (window_guards (n := 12132) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12132) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((3505351/31250000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12132 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12132) internalParameters :=
  BstLean.Part227.worldPackage (n := 12132) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (3505351/31250000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12132) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part281.world12132.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part281.world12132, width]

theorem frame_payment : internalParameters.frame ≤ Part281.world12132.frame := by
  exact frame.2.trans (by norm_num [Part281.world12132])

theorem moment_payment : internalParameters.moment ≤ Part281.world12132.moment := by
  exact moment.2.trans (by norm_num [Part281.world12132])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (299698613/250000000000) ∧
    internalParameters.frame ≤ (316927231383/500000000000) ∧
    internalParameters.moment ≤ (2654933221/250000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12132) (Part281.world12132) where
  hidden := internalWorld.hidden
  hidden_measurable := internalWorld.hidden_measurable
  scale := internalWorld.scale
  scale_measurable := internalWorld.scale_measurable
  scale_eq := internalWorld.scale_eq
  calibration := internalWorld.calibration
  calibration_measurable := internalWorld.calibration_measurable
  hidden_charge := internalWorld.hidden_charge.trans hidden_payment
  product_window := by
    intro θ hθ
    obtain ⟨hl, hu⟩ := internalWorld.product_window θ hθ
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part281.world12132]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part281.world12132])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part281.world12132]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part281.world12132]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12132).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12132).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part281.WorldRow12132
namespace BstLean.Part281.WorldRow12133
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
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
    exp (-((mW 12133 : ℝ)*24266)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12133 : ℝ)*24266)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12133 : ℝ)*24266)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12133 : ℝ)*24266)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24266 (mW 12133) i /
      (rowEps i * e1MeanBounds 24266 (mW 12133) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24266 (mW 12133) (1/10^6) (1/10^7) rowEps ≤ (133309/62500000000) := by
  have hr : 0 ≤ firstRatio 24266 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24266 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24266) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12133 (1/10^6) (1/10^7) ((133309/62500000000))
      (712/10000) rowEps ≤ (112152059/1000000000000) := by
  have hs : statisticsPayment ≤ (131918633549/31250000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (2695766518853/25000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12133 (1/10^6) (1/10^7) ((133309/62500000000))
      (712/10000) rowEps =
      exp (-((mW 12133 : ℝ)*24266)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12133 : ℝ)*24266)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12133) (mW 12133)).real
      (goodDist 12133 (712/10000))ᶜ ≤ (112152059/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 12133) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (133309/62500000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12133 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (748251685163/1000000000000000000)
  k0 := (4089428464149123/1000000000000000000)
  k6 := (2486259942651087/200000000000000000)
  ε₁ := 161/10000
  ε₂ := 1118/100000
  s := 46727425/10^8
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  ε₁_pos := by norm_num
  ε₂_pos := by norm_num
  s_pos := by norm_num
  norm_lower := (window_guards (n := 12133) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12133) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((112152059/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12133 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12133) internalParameters :=
  BstLean.Part227.worldPackage (n := 12133) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (112152059/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12133) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part281.world12133.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part281.world12133, width]

theorem frame_payment : internalParameters.frame ≤ Part281.world12133.frame := by
  exact frame.2.trans (by norm_num [Part281.world12133])

theorem moment_payment : internalParameters.moment ≤ Part281.world12133.moment := by
  exact moment.2.trans (by norm_num [Part281.world12133])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1198743593/1000000000000) ∧
    internalParameters.frame ≤ (633839239833/1000000000000) ∧
    internalParameters.moment ≤ (10617440899/1000000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12133) (Part281.world12133) where
  hidden := internalWorld.hidden
  hidden_measurable := internalWorld.hidden_measurable
  scale := internalWorld.scale
  scale_measurable := internalWorld.scale_measurable
  scale_eq := internalWorld.scale_eq
  calibration := internalWorld.calibration
  calibration_measurable := internalWorld.calibration_measurable
  hidden_charge := internalWorld.hidden_charge.trans hidden_payment
  product_window := by
    intro θ hθ
    obtain ⟨hl, hu⟩ := internalWorld.product_window θ hθ
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part281.world12133]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part281.world12133])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part281.world12133]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part281.world12133]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12133).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12133).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part281.WorldRow12133
