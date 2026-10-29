import BstLean.Part268World33Step5
namespace BstLean.Part268.WorldRow13175
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
    exp (-((mW 13175 : ℝ)*26350)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 13175 : ℝ)*26350)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 13175 : ℝ)*26350)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 13175 : ℝ)*26350)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 26350 (mW 13175) i /
      (rowEps i * e1MeanBounds 26350 (mW 13175) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 26350 (mW 13175) (1/10^6) (1/10^7) rowEps ≤ (1962549/1000000000000) := by
  have hr : 0 ≤ firstRatio 26350 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 26350 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 26350) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 13175 (1/10^6) (1/10^7) ((1962549/1000000000000))
      (712/10000) rowEps ≤ (23660013/250000000000) := by
  have hs : statisticsPayment ≤ (1790080739841/500000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (45479944672369/500000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 13175 (1/10^6) (1/10^7) ((1962549/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 13175 : ℝ)*26350)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 13175 : ℝ)*26350)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*13175) (mW 13175)).real
      (goodDist 13175 (712/10000))ᶜ ≤ (23660013/250000000000) := by
  apply le_trans (concrete_distance_charge (n := 13175) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (1962549/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 13175 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (82657844757/125000000000000000)
  k0 := (1922187727730541/500000000000000000)
  k6 := (5964792337381369/500000000000000000)
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
  norm_lower := (window_guards (n := 13175) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 13175) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((23660013/250000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 13175 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 13175) internalParameters :=
  BstLean.Part227.worldPackage (n := 13175) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (23660013/250000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 13175) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world13175.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world13175, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world13175.frame := by
  exact frame.2.trans (by norm_num [Part268.world13175])

theorem moment_payment : internalParameters.moment ≤ Part268.world13175.moment := by
  exact moment.2.trans (by norm_num [Part268.world13175])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (576277271/500000000000) ∧
    internalParameters.frame ≤ (24770392963/40000000000) ∧
    internalParameters.moment ≤ (8559831407/1000000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 13175) (Part268.world13175) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world13175]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world13175])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world13175]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world13175]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 13175).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 13175).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow13175
namespace BstLean.Part268.WorldRow13176
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
    exp (-((mW 13176 : ℝ)*26352)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 13176 : ℝ)*26352)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 13176 : ℝ)*26352)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 13176 : ℝ)*26352)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 26352 (mW 13176) i /
      (rowEps i * e1MeanBounds 26352 (mW 13176) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 26352 (mW 13176) (1/10^6) (1/10^7) rowEps ≤ (981199/500000000000) := by
  have hr : 0 ≤ firstRatio 26352 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 26352 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 26352) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 13176 (1/10^6) (1/10^7) ((981199/500000000000))
      (712/10000) rowEps ≤ (94625141/1000000000000) := by
  have hs : statisticsPayment ≤ (3579634754343/1000000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (1818910097419/20000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 13176 (1/10^6) (1/10^7) ((981199/500000000000))
      (712/10000) rowEps =
      exp (-((mW 13176 : ℝ)*26352)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 13176 : ℝ)*26352)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*13176) (mW 13176)).real
      (goodDist 13176 (712/10000))ᶜ ≤ (94625141/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 13176) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (981199/500000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 13176 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (165296869779/250000000000000000)
  k0 := (1922078312546253/500000000000000000)
  k6 := (2385826392974451/200000000000000000)
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
  norm_lower := (window_guards (n := 13176) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 13176) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((94625141/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 13176 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 13176) internalParameters :=
  BstLean.Part227.worldPackage (n := 13176) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (94625141/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 13176) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world13176.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world13176, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world13176.frame := by
  exact frame.2.trans (by norm_num [Part268.world13176])

theorem moment_payment : internalParameters.moment ≤ Part268.world13176.moment := by
  exact moment.2.trans (by norm_num [Part268.world13176])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (576258001/500000000000) ∧
    internalParameters.frame ≤ (619246958033/1000000000000) ∧
    internalParameters.moment ≤ (8558135647/1000000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 13176) (Part268.world13176) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world13176]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world13176])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world13176]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world13176]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 13176).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 13176).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow13176
namespace BstLean.Part268.WorldRow13177
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
    exp (-((mW 13177 : ℝ)*26354)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 13177 : ℝ)*26354)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 13177 : ℝ)*26354)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 13177 : ℝ)*26354)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 26354 (mW 13177) i /
      (rowEps i * e1MeanBounds 26354 (mW 13177) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 26354 (mW 13177) (1/10^6) (1/10^7) rowEps ≤ (245281/125000000000) := by
  have hr : 0 ≤ firstRatio 26354 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 26354 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 26354) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 13177 (1/10^6) (1/10^7) ((245281/125000000000))
      (712/10000) rowEps ≤ (1478289/15625000000) := by
  have hs : statisticsPayment ≤ (1789554088263/500000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (22732846669171/250000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 13177 (1/10^6) (1/10^7) ((245281/125000000000))
      (712/10000) rowEps =
      exp (-((mW 13177 : ℝ)*26354)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 13177 : ℝ)*26354)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*13177) (mW 13177)).real
      (goodDist 13177 (712/10000))ᶜ ≤ (1478289/15625000000) := by
  apply le_trans (concrete_distance_charge (n := 13177) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (245281/125000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 13177 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (661112214457/1000000000000000000)
  k0 := (240246113986473/62500000000000000)
  k6 := (238573586130337/20000000000000000)
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
  norm_lower := (window_guards (n := 13177) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 13177) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((1478289/15625000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 13177 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 13177) internalParameters :=
  BstLean.Part227.worldPackage (n := 13177) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (1478289/15625000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 13177) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world13177.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world13177, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world13177.frame := by
  exact frame.2.trans (by norm_num [Part268.world13177])

theorem moment_payment : internalParameters.moment ≤ Part268.world13177.moment := by
  exact moment.2.trans (by norm_num [Part268.world13177])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1152477471/1000000000000) ∧
    internalParameters.frame ≤ (123846818793/200000000000) ∧
    internalParameters.moment ≤ (1711288071/200000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 13177) (Part268.world13177) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world13177]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world13177])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world13177]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world13177]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 13177).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 13177).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow13177
namespace BstLean.Part268.WorldRow13178
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
    exp (-((mW 13178 : ℝ)*26356)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 13178 : ℝ)*26356)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 13178 : ℝ)*26356)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 13178 : ℝ)*26356)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 26356 (mW 13178) i /
      (rowEps i * e1MeanBounds 26356 (mW 13178) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 26356 (mW 13178) (1/10^6) (1/10^7) rowEps ≤ (981049/500000000000) := by
  have hr : 0 ≤ firstRatio 26356 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 26356 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 26356) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 13178 (1/10^6) (1/10^7) ((981049/500000000000))
      (712/10000) rowEps ≤ (94595849/1000000000000) := by
  have hs : statisticsPayment ≤ (143143269847/40000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (90917265598549/1000000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 13178 (1/10^6) (1/10^7) ((981049/500000000000))
      (712/10000) rowEps =
      exp (-((mW 13178 : ℝ)*26356)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 13178 : ℝ)*26356)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*13178) (mW 13178)).real
      (goodDist 13178 (712/10000))ᶜ ≤ (94595849/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 13178) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (981049/500000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 13178 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (661036964077/1000000000000000000)
  k0 := (3843719051533417/1000000000000000000)
  k6 := (5964113349843373/500000000000000000)
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
  norm_lower := (window_guards (n := 13178) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 13178) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((94595849/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 13178 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 13178) internalParameters :=
  BstLean.Part227.worldPackage (n := 13178) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (94595849/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 13178) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world13178.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world13178, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world13178.frame := by
  exact frame.2.trans (by norm_num [Part268.world13178])

theorem moment_payment : internalParameters.moment ≤ Part268.world13178.moment := by
  exact moment.2.trans (by norm_num [Part268.world13178])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (23048779/20000000000) ∧
    internalParameters.frame ≤ (619221231871/1000000000000) ∧
    internalParameters.moment ≤ (8554745533/1000000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 13178) (Part268.world13178) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world13178]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world13178])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world13178]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world13178]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 13178).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 13178).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow13178
namespace BstLean.Part268.WorldRow13179
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
    exp (-((mW 13179 : ℝ)*26358)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 13179 : ℝ)*26358)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 13179 : ℝ)*26358)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 13179 : ℝ)*26358)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 26358 (mW 13179) i /
      (rowEps i * e1MeanBounds 26358 (mW 13179) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 26358 (mW 13179) (1/10^6) (1/10^7) rowEps ≤ (1961947/1000000000000) := by
  have hr : 0 ≤ firstRatio 26358 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 26358 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 26358) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 13179 (1/10^6) (1/10^7) ((1961947/1000000000000))
      (712/10000) rowEps ≤ (9458093/100000000000) := by
  have hs : statisticsPayment ≤ (3578055463233/1000000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (90902872561127/1000000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 13179 (1/10^6) (1/10^7) ((1961947/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 13179 : ℝ)*26358)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 13179 : ℝ)*26358)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*13179) (mW 13179)).real
      (goodDist 13179 (712/10000))ᶜ ≤ (9458093/100000000000) := by
  apply le_trans (concrete_distance_charge (n := 13179) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (1961947/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 13179 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (165240431993/250000000000000000)
  k0 := (1921750154167693/500000000000000000)
  k6 := (1490971768046521/125000000000000000)
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
  norm_lower := (window_guards (n := 13179) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 13179) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((9458093/100000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 13179 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 13179) internalParameters :=
  BstLean.Part227.worldPackage (n := 13179) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (9458093/100000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 13179) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world13179.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world13179, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world13179.frame := by
  exact frame.2.trans (by norm_num [Part268.world13179])

theorem moment_payment : internalParameters.moment ≤ Part268.world13179.moment := by
  exact moment.2.trans (by norm_num [Part268.world13179])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (576200219/500000000000) ∧
    internalParameters.frame ≤ (2476833487/4000000000) ∧
    internalParameters.moment ≤ (427652559/50000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 13179) (Part268.world13179) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world13179]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world13179])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world13179]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world13179]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 13179).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 13179).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow13179
namespace BstLean.Part268.WorldRow13180
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
    exp (-((mW 13180 : ℝ)*26360)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 13180 : ℝ)*26360)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 13180 : ℝ)*26360)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 13180 : ℝ)*26360)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 26360 (mW 13180) i /
      (rowEps i * e1MeanBounds 26360 (mW 13180) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 26360 (mW 13180) (1/10^6) (1/10^7) rowEps ≤ (1961797/1000000000000) := by
  have hr : 0 ≤ firstRatio 26360 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 26360 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 26360) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 13180 (1/10^6) (1/10^7) ((1961797/1000000000000))
      (712/10000) rowEps ≤ (94566277/1000000000000) := by
  have hs : statisticsPayment ≤ (894382331911/250000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (90888745742691/1000000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 13180 (1/10^6) (1/10^7) ((1961797/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 13180 : ℝ)*26360)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 13180 : ℝ)*26360)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*13180) (mW 13180)).real
      (goodDist 13180 (712/10000))ᶜ ≤ (94566277/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 13180) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (1961797/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 13180 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (660886506137/1000000000000000000)
  k0 := (768656318835979/200000000000000000)
  k6 := (2385464328112669/200000000000000000)
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
  norm_lower := (window_guards (n := 13180) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 13180) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((94566277/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 13180 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 13180) internalParameters :=
  BstLean.Part227.worldPackage (n := 13180) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (94566277/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 13180) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world13180.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world13180, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world13180.frame := by
  exact frame.2.trans (by norm_num [Part268.world13180])

theorem moment_payment : internalParameters.moment ≤ Part268.world13180.moment := by
  exact moment.2.trans (by norm_num [Part268.world13180])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1152361937/1000000000000) ∧
    internalParameters.frame ≤ (309597756801/500000000000) ∧
    internalParameters.moment ≤ (534459831/62500000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 13180) (Part268.world13180) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world13180]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world13180])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world13180]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world13180]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 13180).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 13180).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow13180
namespace BstLean.Part268.WorldRow13181
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
    exp (-((mW 13181 : ℝ)*26362)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 13181 : ℝ)*26362)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 13181 : ℝ)*26362)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 13181 : ℝ)*26362)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 26362 (mW 13181) i /
      (rowEps i * e1MeanBounds 26362 (mW 13181) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 26362 (mW 13181) (1/10^6) (1/10^7) rowEps ≤ (1961647/1000000000000) := by
  have hr : 0 ≤ firstRatio 26362 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 26362 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 26362) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 13181 (1/10^6) (1/10^7) ((1961647/1000000000000))
      (712/10000) rowEps ≤ (94551621/1000000000000) := by
  have hs : statisticsPayment ≤ (71540066787/20000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (90874616046079/1000000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 13181 (1/10^6) (1/10^7) ((1961647/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 13181 : ℝ)*26362)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 13181 : ℝ)*26362)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*13181) (mW 13181)).real
      (goodDist 13181 (712/10000))ᶜ ≤ (94551621/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 13181) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (1961647/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 13181 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (82601412321/125000000000000000)
  k0 := (240191431816267/62500000000000000)
  k6 := (2981717297062627/250000000000000000)
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
  norm_lower := (window_guards (n := 13181) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 13181) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((94551621/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 13181 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 13181) internalParameters :=
  BstLean.Part227.worldPackage (n := 13181) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (94551621/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 13181) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world13181.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world13181, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world13181.frame := by
  exact frame.2.trans (by norm_num [Part268.world13181])

theorem moment_payment : internalParameters.moment ≤ Part268.world13181.moment := by
  exact moment.2.trans (by norm_num [Part268.world13181])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (230464689/200000000000) ∧
    internalParameters.frame ≤ (309591328713/500000000000) ∧
    internalParameters.moment ≤ (8549663881/1000000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 13181) (Part268.world13181) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world13181]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world13181])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world13181]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world13181]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 13181).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 13181).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow13181
namespace BstLean.Part268.WorldRow13182
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
    exp (-((mW 13182 : ℝ)*26364)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 13182 : ℝ)*26364)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 13182 : ℝ)*26364)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 13182 : ℝ)*26364)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 26364 (mW 13182) i /
      (rowEps i * e1MeanBounds 26364 (mW 13182) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 26364 (mW 13182) (1/10^6) (1/10^7) rowEps ≤ (245187/125000000000) := by
  have hr : 0 ≤ firstRatio 26364 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 26364 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 26364) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 13182 (1/10^6) (1/10^7) ((245187/125000000000))
      (712/10000) rowEps ≤ (94536693/1000000000000) := by
  have hs : statisticsPayment ≤ (447059687287/125000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (90860214462363/1000000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 13182 (1/10^6) (1/10^7) ((245187/125000000000))
      (712/10000) rowEps =
      exp (-((mW 13182 : ℝ)*26364)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 13182 : ℝ)*26364)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*13182) (mW 13182)).real
      (goodDist 13182 (712/10000))ᶜ ≤ (94536693/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 13182) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (245187/125000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 13182 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (660736105263/1000000000000000000)
  k0 := (3842844252975659/1000000000000000000)
  k6 := (11926416787423891/1000000000000000000)
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
  norm_lower := (window_guards (n := 13182) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 13182) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((94536693/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 13182 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 13182) internalParameters :=
  BstLean.Part227.worldPackage (n := 13182) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (94536693/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 13182) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world13182.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world13182, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world13182.frame := by
  exact frame.2.trans (by norm_num [Part268.world13182])

theorem moment_payment : internalParameters.moment ≤ Part268.world13182.moment := by
  exact moment.2.trans (by norm_num [Part268.world13182])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1152284963/1000000000000) ∧
    internalParameters.frame ≤ (309584901611/500000000000) ∧
    internalParameters.moment ≤ (1709594187/200000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 13182) (Part268.world13182) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world13182]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world13182])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world13182]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world13182]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 13182).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 13182).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow13182
namespace BstLean.Part268.WorldRow13183
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
    exp (-((mW 13183 : ℝ)*26366)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 13183 : ℝ)*26366)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 13183 : ℝ)*26366)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 13183 : ℝ)*26366)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 26366 (mW 13183) i /
      (rowEps i * e1MeanBounds 26366 (mW 13183) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 26366 (mW 13183) (1/10^6) (1/10^7) rowEps ≤ (980673/500000000000) := by
  have hr : 0 ≤ firstRatio 26366 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 26366 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 26366) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 13183 (1/10^6) (1/10^7) ((980673/500000000000))
      (712/10000) rowEps ≤ (5907627/62500000000) := by
  have hs : statisticsPayment ≤ (143038072177/40000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (45423039518453/500000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 13183 (1/10^6) (1/10^7) ((980673/500000000000))
      (712/10000) rowEps =
      exp (-((mW 13183 : ℝ)*26366)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 13183 : ℝ)*26366)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*13183) (mW 13183)).real
      (goodDist 13183 (712/10000))ᶜ ≤ (5907627/62500000000) := by
  apply le_trans (concrete_distance_charge (n := 13183) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (980673/500000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 13183 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (660660926217/1000000000000000000)
  k0 := (3842625625916471/1000000000000000000)
  k6 := (93171597172451/7812500000000000)
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
  norm_lower := (window_guards (n := 13183) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 13183) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((5907627/62500000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 13183 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 13183) internalParameters :=
  BstLean.Part227.worldPackage (n := 13183) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (5907627/62500000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 13183) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world13183.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world13183, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world13183.frame := by
  exact frame.2.trans (by norm_num [Part268.world13183])

theorem moment_payment : internalParameters.moment ≤ Part268.world13183.moment := by
  exact moment.2.trans (by norm_num [Part268.world13183])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1152246491/1000000000000) ∧
    internalParameters.frame ≤ (619156950989/1000000000000) ∧
    internalParameters.moment ≤ (1068284807/125000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 13183) (Part268.world13183) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world13183]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world13183])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world13183]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world13183]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 13183).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 13183).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow13183
namespace BstLean.Part268.WorldRow13184
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
    exp (-((mW 13184 : ℝ)*26368)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 13184 : ℝ)*26368)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 13184 : ℝ)*26368)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 13184 : ℝ)*26368)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 26368 (mW 13184) i /
      (rowEps i * e1MeanBounds 26368 (mW 13184) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 26368 (mW 13184) (1/10^6) (1/10^7) rowEps ≤ (490299/250000000000) := by
  have hr : 0 ≤ firstRatio 26368 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 26368 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 26368) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 13184 (1/10^6) (1/10^7) ((490299/250000000000))
      (712/10000) rowEps ≤ (11813421/125000000000) := by
  have hs : statisticsPayment ≤ (44692828221/12500000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (90831940738971/1000000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 13184 (1/10^6) (1/10^7) ((490299/250000000000))
      (712/10000) rowEps =
      exp (-((mW 13184 : ℝ)*26368)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 13184 : ℝ)*26368)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*13184) (mW 13184)).real
      (goodDist 13184 (712/10000))ᶜ ≤ (11813421/125000000000) := by
  apply le_trans (concrete_distance_charge (n := 13184) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (490299/250000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 13184 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (660585761427/1000000000000000000)
  k0 := (1921203513939469/500000000000000000)
  k6 := (11925512140190259/1000000000000000000)
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
  norm_lower := (window_guards (n := 13184) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 13184) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((11813421/125000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 13184 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 13184) internalParameters :=
  BstLean.Part227.worldPackage (n := 13184) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (11813421/125000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 13184) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world13184.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world13184, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world13184.frame := by
  exact frame.2.trans (by norm_num [Part268.world13184])

theorem moment_payment : internalParameters.moment ≤ Part268.world13184.moment := by
  exact moment.2.trans (by norm_num [Part268.world13184])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1152208029/1000000000000) ∧
    internalParameters.frame ≤ (309572050363/500000000000) ∧
    internalParameters.moment ≤ (4272293223/500000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 13184) (Part268.world13184) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world13184]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world13184])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world13184]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world13184]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 13184).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 13184).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow13184
namespace BstLean.Part268.WorldRow13185
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
    exp (-((mW 13185 : ℝ)*26370)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 13185 : ℝ)*26370)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 13185 : ℝ)*26370)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 13185 : ℝ)*26370)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 26370 (mW 13185) i /
      (rowEps i * e1MeanBounds 26370 (mW 13185) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 26370 (mW 13185) (1/10^6) (1/10^7) rowEps ≤ (980523/500000000000) := by
  have hr : 0 ≤ firstRatio 26370 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 26370 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 26370) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 13185 (1/10^6) (1/10^7) ((980523/500000000000))
      (712/10000) rowEps ≤ (47246351/500000000000) := by
  have hs : statisticsPayment ≤ (893725214501/250000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (1816355991409/20000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 13185 (1/10^6) (1/10^7) ((980523/500000000000))
      (712/10000) rowEps =
      exp (-((mW 13185 : ℝ)*26370)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 13185 : ℝ)*26370)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*13185) (mW 13185)).real
      (goodDist 13185 (712/10000))ᶜ ≤ (47246351/500000000000) := by
  apply le_trans (concrete_distance_charge (n := 13185) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (980523/500000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 13185 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (82563826361/125000000000000000)
  k0 := (384218845885347/100000000000000000)
  k6 := (5962529946881863/500000000000000000)
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
  norm_lower := (window_guards (n := 13185) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 13185) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((47246351/500000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 13185 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 13185) internalParameters :=
  BstLean.Part227.worldPackage (n := 13185) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (47246351/500000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 13185) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world13185.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world13185, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world13185.frame := by
  exact frame.2.trans (by norm_num [Part268.world13185])

theorem moment_payment : internalParameters.moment ≤ Part268.world13185.moment := by
  exact moment.2.trans (by norm_num [Part268.world13185])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1152169577/1000000000000) ∧
    internalParameters.frame ≤ (309565626217/500000000000) ∧
    internalParameters.moment ≤ (1708578981/200000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 13185) (Part268.world13185) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world13185]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world13185])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world13185]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world13185]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 13185).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 13185).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow13185
namespace BstLean.Part268.WorldRow13186
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
    exp (-((mW 13186 : ℝ)*26372)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 13186 : ℝ)*26372)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 13186 : ℝ)*26372)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 13186 : ℝ)*26372)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 26372 (mW 13186) i /
      (rowEps i * e1MeanBounds 26372 (mW 13186) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 26372 (mW 13186) (1/10^6) (1/10^7) rowEps ≤ (392179/200000000000) := by
  have hr : 0 ≤ firstRatio 26372 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 26372 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 26372) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 13186 (1/10^6) (1/10^7) ((392179/200000000000))
      (712/10000) rowEps ≤ (23619441/250000000000) := by
  have hs : statisticsPayment ≤ (1787187802671/500000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (9080338661101/100000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 13186 (1/10^6) (1/10^7) ((392179/200000000000))
      (712/10000) rowEps =
      exp (-((mW 13186 : ℝ)*26372)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 13186 : ℝ)*26372)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*13186) (mW 13186)).real
      (goodDist 13186 (712/10000))ᶜ ≤ (23619441/250000000000) := by
  apply le_trans (concrete_distance_charge (n := 13186) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (392179/200000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 13186 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (660435474597/1000000000000000000)
  k0 := (3841969918836293/1000000000000000000)
  k6 := (11924607698784371/1000000000000000000)
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
  norm_lower := (window_guards (n := 13186) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 13186) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((23619441/250000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 13186 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 13186) internalParameters :=
  BstLean.Part227.worldPackage (n := 13186) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (23619441/250000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 13186) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world13186.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world13186, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world13186.frame := by
  exact frame.2.trans (by norm_num [Part268.world13186])

theorem moment_payment : internalParameters.moment ≤ Part268.world13186.moment := by
  exact moment.2.trans (by norm_num [Part268.world13186])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (576065567/500000000000) ∧
    internalParameters.frame ≤ (19347450191/31250000000) ∧
    internalParameters.moment ≤ (8541203831/1000000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 13186) (Part268.world13186) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world13186]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world13186])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world13186]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world13186]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 13186).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 13186).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow13186
namespace BstLean.Part268.WorldRow13187
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
    exp (-((mW 13187 : ℝ)*26374)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 13187 : ℝ)*26374)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 13187 : ℝ)*26374)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 13187 : ℝ)*26374)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 26374 (mW 13187) i /
      (rowEps i * e1MeanBounds 26374 (mW 13187) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 26374 (mW 13187) (1/10^6) (1/10^7) rowEps ≤ (392149/200000000000) := by
  have hr : 0 ≤ firstRatio 26374 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 26374 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 26374) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 13187 (1/10^6) (1/10^7) ((392149/200000000000))
      (712/10000) rowEps ≤ (23615773/250000000000) := by
  have hs : statisticsPayment ≤ (3573850499637/1000000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (45394619864463/500000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 13187 (1/10^6) (1/10^7) ((392149/200000000000))
      (712/10000) rowEps =
      exp (-((mW 13187 : ℝ)*26374)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 13187 : ℝ)*26374)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*13187) (mW 13187)).real
      (goodDist 13187 (712/10000))ᶜ ≤ (23615773/250000000000) := by
  apply le_trans (concrete_distance_charge (n := 13187) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (392149/200000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 13187 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (13207207051/20000000000000000)
  k0 := (3841751407820723/1000000000000000000)
  k6 := (5962077777621221/500000000000000000)
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
  norm_lower := (window_guards (n := 13187) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 13187) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((23615773/250000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 13187 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 13187) internalParameters :=
  BstLean.Part227.worldPackage (n := 13187) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (23615773/250000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 13187) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world13187.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world13187, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world13187.frame := by
  exact frame.2.trans (by norm_num [Part268.world13187])

theorem moment_payment : internalParameters.moment ≤ Part268.world13187.moment := by
  exact moment.2.trans (by norm_num [Part268.world13187])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1152092701/1000000000000) ∧
    internalParameters.frame ≤ (619105561759/1000000000000) ∧
    internalParameters.moment ≤ (341580529/40000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 13187) (Part268.world13187) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world13187]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world13187])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world13187]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world13187]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 13187).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 13187).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow13187
namespace BstLean.Part268.WorldRow13188
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
    exp (-((mW 13188 : ℝ)*26376)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 13188 : ℝ)*26376)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 13188 : ℝ)*26376)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 13188 : ℝ)*26376)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 26376 (mW 13188) i /
      (rowEps i * e1MeanBounds 26376 (mW 13188) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 26376 (mW 13188) (1/10^6) (1/10^7) rowEps ≤ (392119/200000000000) := by
  have hr : 0 ≤ firstRatio 26376 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 26376 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 26376) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 13188 (1/10^6) (1/10^7) ((392119/200000000000))
      (712/10000) rowEps ≤ (94448417/1000000000000) := by
  have hs : statisticsPayment ≤ (111666423151/31250000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (18155017996393/200000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 13188 (1/10^6) (1/10^7) ((392119/200000000000))
      (712/10000) rowEps =
      exp (-((mW 13188 : ℝ)*26376)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 13188 : ℝ)*26376)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*13188) (mW 13188)).real
      (goodDist 13188 (712/10000))ᶜ ≤ (94448417/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 13188) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (392119/200000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 13188 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (82535655593/125000000000000000)
  k0 := (192076646290149/50000000000000000)
  k6 := (11923703463128187/1000000000000000000)
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
  norm_lower := (window_guards (n := 13188) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 13188) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((94448417/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 13188 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 13188) internalParameters :=
  BstLean.Part227.worldPackage (n := 13188) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (94448417/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 13188) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world13188.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world13188, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world13188.frame := by
  exact frame.2.trans (by norm_num [Part268.world13188])

theorem moment_payment : internalParameters.moment ≤ Part268.world13188.moment := by
  exact moment.2.trans (by norm_num [Part268.world13188])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (576027139/500000000000) ∧
    internalParameters.frame ≤ (990548351/1600000000) ∧
    internalParameters.moment ≤ (4268911543/500000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 13188) (Part268.world13188) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world13188]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world13188])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world13188]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world13188]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 13188).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 13188).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow13188
namespace BstLean.Part268.WorldRow13189
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
    exp (-((mW 13189 : ℝ)*26378)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 13189 : ℝ)*26378)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 13189 : ℝ)*26378)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 13189 : ℝ)*26378)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 26378 (mW 13189) i /
      (rowEps i * e1MeanBounds 26378 (mW 13189) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 26378 (mW 13189) (1/10^6) (1/10^7) rowEps ≤ (392089/200000000000) := by
  have hr : 0 ≤ firstRatio 26378 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 26378 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 26378) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 13189 (1/10^6) (1/10^7) ((392089/200000000000))
      (712/10000) rowEps ≤ (4721687/50000000000) := by
  have hs : statisticsPayment ≤ (3572800728871/1000000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (90760937372023/1000000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 13189 (1/10^6) (1/10^7) ((392089/200000000000))
      (712/10000) rowEps =
      exp (-((mW 13189 : ℝ)*26378)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 13189 : ℝ)*26378)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*13189) (mW 13189)).real
      (goodDist 13189 (712/10000))ᶜ ≤ (4721687/50000000000) := by
  apply le_trans (concrete_distance_charge (n := 13189) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (392089/200000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 13189 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (330105075587/500000000000000000)
  k0 := (960328618193367/250000000000000000)
  k6 := (5961625711215929/500000000000000000)
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
  norm_lower := (window_guards (n := 13189) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 13189) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((4721687/50000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 13189 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 13189) internalParameters :=
  BstLean.Part227.worldPackage (n := 13189) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (4721687/50000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 13189) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world13189.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world13189, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world13189.frame := by
  exact frame.2.trans (by norm_num [Part268.world13189])

theorem moment_payment : internalParameters.moment ≤ Part268.world13189.moment := by
  exact moment.2.trans (by norm_num [Part268.world13189])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (144001983/125000000000) ∧
    internalParameters.frame ≤ (7738498487/12500000000) ∧
    internalParameters.moment ≤ (1707226683/200000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 13189) (Part268.world13189) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world13189]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world13189])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world13189]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world13189]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 13189).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 13189).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow13189
namespace BstLean.Part268.WorldRow13190
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
    exp (-((mW 13190 : ℝ)*26380)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 13190 : ℝ)*26380)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 13190 : ℝ)*26380)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 13190 : ℝ)*26380)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 26380 (mW 13190) i /
      (rowEps i * e1MeanBounds 26380 (mW 13190) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 26380 (mW 13190) (1/10^6) (1/10^7) rowEps ≤ (392059/200000000000) := by
  have hr : 0 ≤ firstRatio 26380 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 26380 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 26380) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 13190 (1/10^6) (1/10^7) ((392059/200000000000))
      (712/10000) rowEps ≤ (94419059/1000000000000) := by
  have hs : statisticsPayment ≤ (1786138031849/500000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (45373390950499/500000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 13190 (1/10^6) (1/10^7) ((392059/200000000000))
      (712/10000) rowEps =
      exp (-((mW 13190 : ℝ)*26380)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 13190 : ℝ)*26380)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*13190) (mW 13190)).real
      (goodDist 13190 (712/10000))ᶜ ≤ (94419059/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 13190) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (392059/200000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 13190 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (660135071837/1000000000000000000)
  k0 := (3841096048728403/1000000000000000000)
  k6 := (11922799433143709/1000000000000000000)
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
  norm_lower := (window_guards (n := 13190) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 13190) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((94419059/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 13190 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 13190) internalParameters :=
  BstLean.Part227.worldPackage (n := 13190) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (94419059/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 13190) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world13190.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world13190, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world13190.frame := by
  exact frame.2.trans (by norm_num [Part268.world13190])

theorem moment_payment : internalParameters.moment ≤ Part268.world13190.moment := by
  exact moment.2.trans (by norm_num [Part268.world13190])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1151977461/1000000000000) ∧
    internalParameters.frame ≤ (2418230627/3906250000) ∧
    internalParameters.moment ≤ (8534444211/1000000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 13190) (Part268.world13190) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world13190]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world13190])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world13190]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world13190]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 13190).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 13190).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow13190
namespace BstLean.Part268.WorldRow13191
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
    exp (-((mW 13191 : ℝ)*26382)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 13191 : ℝ)*26382)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 13191 : ℝ)*26382)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 13191 : ℝ)*26382)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 26382 (mW 13191) i /
      (rowEps i * e1MeanBounds 26382 (mW 13191) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 26382 (mW 13191) (1/10^6) (1/10^7) rowEps ≤ (392029/200000000000) := by
  have hr : 0 ≤ firstRatio 26382 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 26382 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 26382) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 13191 (1/10^6) (1/10^7) ((392029/200000000000))
      (712/10000) rowEps ≤ (94404377/1000000000000) := by
  have hs : statisticsPayment ≤ (714350309051/200000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (22683155892697/250000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 13191 (1/10^6) (1/10^7) ((392029/200000000000))
      (712/10000) rowEps =
      exp (-((mW 13191 : ℝ)*26382)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 13191 : ℝ)*26382)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*13191) (mW 13191)).real
      (goodDist 13191 (712/10000))ᶜ ≤ (94404377/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 13191) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (392029/200000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 13191 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (660060006729/1000000000000000000)
  k0 := (1920438826830547/500000000000000000)
  k6 := (5961173747626999/500000000000000000)
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
  norm_lower := (window_guards (n := 13191) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 13191) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((94404377/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 13191 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 13191) internalParameters :=
  BstLean.Part227.worldPackage (n := 13191) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (94404377/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 13191) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world13191.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world13191, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world13191.frame := by
  exact frame.2.trans (by norm_num [Part268.world13191])

theorem moment_payment : internalParameters.moment ≤ Part268.world13191.moment := by
  exact moment.2.trans (by norm_num [Part268.world13191])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1151939067/1000000000000) ∧
    internalParameters.frame ≤ (4836360969/7812500000) ∧
    internalParameters.moment ≤ (4266377737/500000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 13191) (Part268.world13191) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world13191]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world13191])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world13191]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world13191]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 13191).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 13191).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow13191
namespace BstLean.Part268.WorldRow13192
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
    exp (-((mW 13192 : ℝ)*26384)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 13192 : ℝ)*26384)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 13192 : ℝ)*26384)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 13192 : ℝ)*26384)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 26384 (mW 13192) i /
      (rowEps i * e1MeanBounds 26384 (mW 13192) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 26384 (mW 13192) (1/10^6) (1/10^7) rowEps ≤ (391999/200000000000) := by
  have hr : 0 ≤ firstRatio 26384 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 26384 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 26384) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 13192 (1/10^6) (1/10^7) ((391999/200000000000))
      (712/10000) rowEps ≤ (94389691/1000000000000) := by
  have hs : statisticsPayment ≤ (223201698343/62500000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (90718462383293/1000000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 13192 (1/10^6) (1/10^7) ((391999/200000000000))
      (712/10000) rowEps =
      exp (-((mW 13192 : ℝ)*26384)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 13192 : ℝ)*26384)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*13192) (mW 13192)).real
      (goodDist 13192 (712/10000))ᶜ ≤ (94389691/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 13192) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (391999/200000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 13192 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (329992477923/500000000000000000)
  k0 := (768131857512969/200000000000000000)
  k6 := (11921895608752983/1000000000000000000)
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
  norm_lower := (window_guards (n := 13192) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 13192) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((94389691/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 13192 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 13192) internalParameters :=
  BstLean.Part227.worldPackage (n := 13192) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (94389691/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 13192) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world13192.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world13192, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world13192.frame := by
  exact frame.2.trans (by norm_num [Part268.world13192])

theorem moment_payment : internalParameters.moment ≤ Part268.world13192.moment := by
  exact moment.2.trans (by norm_num [Part268.world13192])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1151900683/1000000000000) ∧
    internalParameters.frame ≤ (309520684759/500000000000) ∧
    internalParameters.moment ≤ (2132766801/250000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 13192) (Part268.world13192) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world13192]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world13192])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world13192]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world13192]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 13192).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 13192).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow13192
namespace BstLean.Part268.WorldRow13193
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
    exp (-((mW 13193 : ℝ)*26386)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 13193 : ℝ)*26386)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 13193 : ℝ)*26386)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 13193 : ℝ)*26386)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 26386 (mW 13193) i /
      (rowEps i * e1MeanBounds 26386 (mW 13193) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 26386 (mW 13193) (1/10^6) (1/10^7) rowEps ≤ (391969/200000000000) := by
  have hr : 0 ≤ firstRatio 26386 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 26386 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 26386) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 13193 (1/10^6) (1/10^7) ((391969/200000000000))
      (712/10000) rowEps ≤ (94375003/1000000000000) := by
  have hs : statisticsPayment ≤ (178535147417/50000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (90704298340411/1000000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 13193 (1/10^6) (1/10^7) ((391969/200000000000))
      (712/10000) rowEps =
      exp (-((mW 13193 : ℝ)*26386)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 13193 : ℝ)*26386)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*13193) (mW 13193)).real
      (goodDist 13193 (712/10000))ᶜ ≤ (94375003/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 13193) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (391969/200000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 13193 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (131981983837/200000000000000000)
  k0 := (960110237608967/250000000000000000)
  k6 := (5960721886815463/500000000000000000)
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
  norm_lower := (window_guards (n := 13193) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 13193) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((94375003/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 13193 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 13193) internalParameters :=
  BstLean.Part227.worldPackage (n := 13193) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (94375003/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 13193) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world13193.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world13193, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world13193.frame := by
  exact frame.2.trans (by norm_num [Part268.world13193])

theorem moment_payment : internalParameters.moment ≤ Part268.world13193.moment := by
  exact moment.2.trans (by norm_num [Part268.world13193])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1151862309/1000000000000) ∧
    internalParameters.frame ≤ (619028536971/1000000000000) ∧
    internalParameters.moment ≤ (8529379401/1000000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 13193) (Part268.world13193) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world13193]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world13193])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world13193]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world13193]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 13193).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 13193).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow13193
namespace BstLean.Part268.WorldRow13194
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
    exp (-((mW 13194 : ℝ)*26388)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 13194 : ℝ)*26388)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 13194 : ℝ)*26388)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 13194 : ℝ)*26388)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 26388 (mW 13194) i /
      (rowEps i * e1MeanBounds 26388 (mW 13194) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 26388 (mW 13194) (1/10^6) (1/10^7) rowEps ≤ (391939/200000000000) := by
  have hr : 0 ≤ firstRatio 26388 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 26388 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 26388) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 13194 (1/10^6) (1/10^7) ((391939/200000000000))
      (712/10000) rowEps ≤ (11795039/125000000000) := by
  have hs : statisticsPayment ≤ (1785089434877/500000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (22672532861011/250000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 13194 (1/10^6) (1/10^7) ((391939/200000000000))
      (712/10000) rowEps =
      exp (-((mW 13194 : ℝ)*26388)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 13194 : ℝ)*26388)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*13194) (mW 13194)).real
      (goodDist 13194 (712/10000))ᶜ ≤ (11795039/125000000000) := by
  apply le_trans (concrete_distance_charge (n := 13194) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (391939/200000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 13194 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (659834896741/1000000000000000000)
  k0 := (1920111321132277/500000000000000000)
  k6 := (2980247997469523/250000000000000000)
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
  norm_lower := (window_guards (n := 13194) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 13194) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((11795039/125000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 13194 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 13194) internalParameters :=
  BstLean.Part227.worldPackage (n := 13194) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (11795039/125000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 13194) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world13194.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world13194, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world13194.frame := by
  exact frame.2.trans (by norm_num [Part268.world13194])

theorem moment_payment : internalParameters.moment ≤ Part268.world13194.moment := by
  exact moment.2.trans (by norm_num [Part268.world13194])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (143977993/125000000000) ∧
    internalParameters.frame ≤ (61901570639/100000000000) ∧
    internalParameters.moment ≤ (1705538413/200000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 13194) (Part268.world13194) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world13194]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world13194])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world13194]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world13194]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 13194).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 13194).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow13194
namespace BstLean.Part268.WorldRow13195
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
    exp (-((mW 13195 : ℝ)*26390)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 13195 : ℝ)*26390)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 13195 : ℝ)*26390)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 13195 : ℝ)*26390)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 26390 (mW 13195) i /
      (rowEps i * e1MeanBounds 26390 (mW 13195) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 26390 (mW 13195) (1/10^6) (1/10^7) rowEps ≤ (391909/200000000000) := by
  have hr : 0 ≤ firstRatio 26390 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 26390 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 26390) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 13195 (1/10^6) (1/10^7) ((391909/200000000000))
      (712/10000) rowEps ≤ (47172809/500000000000) := by
  have hs : statisticsPayment ≤ (1784827468837/500000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (90675961696093/1000000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 13195 (1/10^6) (1/10^7) ((391909/200000000000))
      (712/10000) rowEps =
      exp (-((mW 13195 : ℝ)*26390)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 13195 : ℝ)*26390)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*13195) (mW 13195)).real
      (goodDist 13195 (712/10000))ᶜ ≤ (47172809/500000000000) := by
  apply le_trans (concrete_distance_charge (n := 13195) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (391909/200000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 13195 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (659759888511/1000000000000000000)
  k0 := (480000545380889/125000000000000000)
  k6 := (11920540257484747/1000000000000000000)
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
  norm_lower := (window_guards (n := 13195) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 13195) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((47172809/500000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 13195 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 13195) internalParameters :=
  BstLean.Part227.worldPackage (n := 13195) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (47172809/500000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 13195) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world13195.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world13195, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world13195.frame := by
  exact frame.2.trans (by norm_num [Part268.world13195])

theorem moment_payment : internalParameters.moment ≤ Part268.world13195.moment := by
  exact moment.2.trans (by norm_num [Part268.world13195])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (115178559/100000000000) ∧
    internalParameters.frame ≤ (24760115111/40000000000) ∧
    internalParameters.moment ≤ (1705201039/200000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 13195) (Part268.world13195) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world13195]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world13195])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world13195]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world13195]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 13195).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 13195).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow13195
namespace BstLean.Part268.WorldRow13196
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
    exp (-((mW 13196 : ℝ)*26392)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 13196 : ℝ)*26392)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 13196 : ℝ)*26392)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 13196 : ℝ)*26392)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 26392 (mW 13196) i /
      (rowEps i * e1MeanBounds 26392 (mW 13196) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 26392 (mW 13196) (1/10^6) (1/10^7) rowEps ≤ (391879/200000000000) := by
  have hr : 0 ≤ firstRatio 26392 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 26392 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 26392) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 13196 (1/10^6) (1/10^7) ((391879/200000000000))
      (712/10000) rowEps ≤ (47165461/500000000000) := by
  have hs : statisticsPayment ≤ (3569131152043/1000000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (90661789098461/1000000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 13196 (1/10^6) (1/10^7) ((391879/200000000000))
      (712/10000) rowEps =
      exp (-((mW 13196 : ℝ)*26392)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 13196 : ℝ)*26392)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*13196) (mW 13196)).real
      (goodDist 13196 (712/10000))ᶜ ≤ (47165461/500000000000) := by
  apply le_trans (concrete_distance_charge (n := 13196) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (391879/200000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 13196 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (659684894491/1000000000000000000)
  k0 := (3839786112776837/1000000000000000000)
  k6 := (11920088576441163/1000000000000000000)
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
  norm_lower := (window_guards (n := 13196) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 13196) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((47165461/500000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 13196 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 13196) internalParameters :=
  BstLean.Part227.worldPackage (n := 13196) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (47165461/500000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 13196) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world13196.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world13196, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world13196.frame := by
  exact frame.2.trans (by norm_num [Part268.world13196])

theorem moment_payment : internalParameters.moment ≤ Part268.world13196.moment := by
  exact moment.2.trans (by norm_num [Part268.world13196])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (230349449/200000000000) ∧
    internalParameters.frame ≤ (154747512781/250000000000) ∧
    internalParameters.moment ≤ (8524318791/1000000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 13196) (Part268.world13196) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world13196]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world13196])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world13196]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world13196]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 13196).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 13196).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow13196
namespace BstLean.Part268.WorldRow13197
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
    exp (-((mW 13197 : ℝ)*26394)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 13197 : ℝ)*26394)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 13197 : ℝ)*26394)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 13197 : ℝ)*26394)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 26394 (mW 13197) i /
      (rowEps i * e1MeanBounds 26394 (mW 13197) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 26394 (mW 13197) (1/10^6) (1/10^7) rowEps ≤ (391849/200000000000) := by
  have hr : 0 ≤ firstRatio 26394 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 26394 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 26394) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 13197 (1/10^6) (1/10^7) ((391849/200000000000))
      (712/10000) rowEps ≤ (94316223/1000000000000) := by
  have hs : statisticsPayment ≤ (3568607512807/1000000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (1812952273061/20000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 13197 (1/10^6) (1/10^7) ((391849/200000000000))
      (712/10000) rowEps =
      exp (-((mW 13197 : ℝ)*26394)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 13197 : ℝ)*26394)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*13197) (mW 13197)).real
      (goodDist 13197 (712/10000))ᶜ ≤ (94316223/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 13197) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (391849/200000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 13197 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (329804957339/500000000000000000)
  k0 := (239972993215621/62500000000000000)
  k6 := (1191963694673761/100000000000000000)
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
  norm_lower := (window_guards (n := 13197) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 13197) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((94316223/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 13197 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 13197) internalParameters :=
  BstLean.Part227.worldPackage (n := 13197) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (94316223/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 13197) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world13197.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world13197, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world13197.frame := by
  exact frame.2.trans (by norm_num [Part268.world13197])

theorem moment_payment : internalParameters.moment ≤ Part268.world13197.moment := by
  exact moment.2.trans (by norm_num [Part268.world13197])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1151708909/1000000000000) ∧
    internalParameters.frame ≤ (309488613219/500000000000) ∧
    internalParameters.moment ≤ (4261316427/500000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 13197) (Part268.world13197) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world13197]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world13197])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world13197]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world13197]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 13197).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 13197).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow13197
namespace BstLean.Part268.WorldRow13198
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
    exp (-((mW 13198 : ℝ)*26396)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 13198 : ℝ)*26396)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 13198 : ℝ)*26396)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 13198 : ℝ)*26396)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 26396 (mW 13198) i /
      (rowEps i * e1MeanBounds 26396 (mW 13198) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 26396 (mW 13198) (1/10^6) (1/10^7) rowEps ≤ (391819/200000000000) := by
  have hr : 0 ≤ firstRatio 26396 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 26396 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 26396) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 13198 (1/10^6) (1/10^7) ((391819/200000000000))
      (712/10000) rowEps ≤ (94301521/1000000000000) := by
  have hs : statisticsPayment ≤ (892021004977/250000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (90633435361763/1000000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 13198 (1/10^6) (1/10^7) ((391819/200000000000))
      (712/10000) rowEps =
      exp (-((mW 13198 : ℝ)*26396)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 13198 : ℝ)*26396)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*13198) (mW 13198)).real
      (goodDist 13198 (712/10000))ᶜ ≤ (94301521/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 13198) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (391819/200000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 13198 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (659534949067/1000000000000000000)
  k0 := (3839349699056789/1000000000000000000)
  k6 := (2979796342091091/250000000000000000)
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
  norm_lower := (window_guards (n := 13198) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 13198) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((94301521/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 13198 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 13198) internalParameters :=
  BstLean.Part227.worldPackage (n := 13198) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (94301521/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 13198) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world13198.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world13198, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world13198.frame := by
  exact frame.2.trans (by norm_num [Part268.world13198])

theorem moment_payment : internalParameters.moment ≤ Part268.world13198.moment := by
  exact moment.2.trans (by norm_num [Part268.world13198])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (143958823/125000000000) ∧
    internalParameters.frame ≤ (154741100929/250000000000) ∧
    internalParameters.moment ≤ (4260473691/500000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 13198) (Part268.world13198) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world13198]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world13198])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world13198]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world13198]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 13198).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 13198).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow13198
namespace BstLean.Part268.WorldRow13199
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
    exp (-((mW 13199 : ℝ)*26398)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 13199 : ℝ)*26398)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 13199 : ℝ)*26398)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 13199 : ℝ)*26398)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 26398 (mW 13199) i /
      (rowEps i * e1MeanBounds 26398 (mW 13199) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 26398 (mW 13199) (1/10^6) (1/10^7) rowEps ≤ (391789/200000000000) := by
  have hr : 0 ≤ firstRatio 26398 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 26398 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 26398) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 13199 (1/10^6) (1/10^7) ((391789/200000000000))
      (712/10000) rowEps ≤ (2946463/31250000000) := by
  have hs : statisticsPayment ≤ (3567560673291/1000000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (45309627113253/500000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 13199 (1/10^6) (1/10^7) ((391789/200000000000))
      (712/10000) rowEps =
      exp (-((mW 13199 : ℝ)*26398)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 13199 : ℝ)*26398)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*13199) (mW 13199)).real
      (goodDist 13199 (712/10000))ᶜ ≤ (2946463/31250000000) := by
  apply le_trans (concrete_distance_charge (n := 13199) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (391789/200000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 13199 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (82432499707/125000000000000000)
  k0 := (959782883899127/250000000000000000)
  k6 := (5959366920655851/500000000000000000)
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
  norm_lower := (window_guards (n := 13199) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 13199) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((2946463/31250000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 13199 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 13199) internalParameters :=
  BstLean.Part227.worldPackage (n := 13199) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (2946463/31250000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 13199) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world13199.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world13199, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world13199.frame := by
  exact frame.2.trans (by norm_num [Part268.world13199])

theorem moment_payment : internalParameters.moment ≤ Part268.world13199.moment := by
  exact moment.2.trans (by norm_num [Part268.world13199])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (287908067/250000000000) ∧
    internalParameters.frame ≤ (309475791479/500000000000) ∧
    internalParameters.moment ≤ (1064907797/125000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 13199) (Part268.world13199) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world13199]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world13199])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world13199]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world13199]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 13199).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 13199).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow13199
