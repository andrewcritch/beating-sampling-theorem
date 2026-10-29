import BstLean.Part268World16Step5
namespace BstLean.Part268.WorldRow12750
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
    exp (-((mW 12750 : ℝ)*25500)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12750 : ℝ)*25500)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12750 : ℝ)*25500)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12750 : ℝ)*25500)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 25500 (mW 12750) i /
      (rowEps i * e1MeanBounds 25500 (mW 12750) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 25500 (mW 12750) (1/10^6) (1/10^7) rowEps ≤ (12679/6250000000) := by
  have hr : 0 ≤ firstRatio 25500 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 25500 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 25500) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12750 (1/10^6) (1/10^7) ((12679/6250000000))
      (712/10000) rowEps ≤ (101242577/1000000000000) := by
  have hs : statisticsPayment ≤ (1909071807291/500000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (4866221579721/50000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12750 (1/10^6) (1/10^7) ((12679/6250000000))
      (712/10000) rowEps =
      exp (-((mW 12750 : ℝ)*25500)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12750 : ℝ)*25500)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12750) (mW 12750)).real
      (goodDist 12750 (712/10000))ᶜ ≤ (101242577/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 12750) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (12679/6250000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12750 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (173649977557/250000000000000000)
  k0 := (197004492293931/50000000000000000)
  k6 := (12126781251816649/1000000000000000000)
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
  norm_lower := (window_guards (n := 12750) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12750) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((101242577/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12750 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12750) internalParameters :=
  BstLean.Part227.worldPackage (n := 12750) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (101242577/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12750) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world12750.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world12750, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world12750.frame := by
  exact frame.2.trans (by norm_num [Part268.world12750])

theorem moment_payment : internalParameters.moment ≤ Part268.world12750.moment := by
  exact moment.2.trans (by norm_num [Part268.world12750])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1169867439/1000000000000) ∧
    internalParameters.frame ≤ (78114133187/125000000000) ∧
    internalParameters.moment ≤ (9325277879/1000000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12750) (Part268.world12750) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world12750]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world12750])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world12750]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world12750]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12750).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12750).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow12750
namespace BstLean.Part268.WorldRow12751
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
    exp (-((mW 12751 : ℝ)*25502)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12751 : ℝ)*25502)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12751 : ℝ)*25502)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12751 : ℝ)*25502)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 25502 (mW 12751) i /
      (rowEps i * e1MeanBounds 25502 (mW 12751) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 25502 (mW 12751) (1/10^6) (1/10^7) rowEps ≤ (2028479/1000000000000) := by
  have hr : 0 ≤ firstRatio 25502 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 25502 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 25502) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12751 (1/10^6) (1/10^7) ((2028479/1000000000000))
      (712/10000) rowEps ≤ (101226157/1000000000000) := by
  have hs : statisticsPayment ≤ (763509738373/200000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (4865430334659/50000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12751 (1/10^6) (1/10^7) ((2028479/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 12751 : ℝ)*25502)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12751 : ℝ)*25502)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12751) (mW 12751)).real
      (goodDist 12751 (712/10000))ᶜ ≤ (101226157/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 12751) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (2028479/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12751 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (347259100301/500000000000000000)
  k0 := (984964522947867/250000000000000000)
  k6 := (12126305719739851/1000000000000000000)
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
  norm_lower := (window_guards (n := 12751) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12751) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((101226157/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12751 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12751) internalParameters :=
  BstLean.Part227.worldPackage (n := 12751) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (101226157/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12751) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world12751.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world12751, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world12751.frame := by
  exact frame.2.trans (by norm_num [Part268.world12751])

theorem moment_payment : internalParameters.moment ≤ Part268.world12751.moment := by
  exact moment.2.trans (by norm_num [Part268.world12751])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (116982441/100000000000) ∧
    internalParameters.frame ≤ (624899314473/1000000000000) ∧
    internalParameters.moment ≤ (72838801/7812500000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12751) (Part268.world12751) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world12751]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world12751])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world12751]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world12751]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12751).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12751).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow12751
namespace BstLean.Part268.WorldRow12752
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
    exp (-((mW 12752 : ℝ)*25504)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12752 : ℝ)*25504)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12752 : ℝ)*25504)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12752 : ℝ)*25504)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 25504 (mW 12752) i /
      (rowEps i * e1MeanBounds 25504 (mW 12752) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 25504 (mW 12752) (1/10^6) (1/10^7) rowEps ≤ (2028319/1000000000000) := by
  have hr : 0 ≤ firstRatio 25504 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 25504 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 25504) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12752 (1/10^6) (1/10^7) ((2028319/1000000000000))
      (712/10000) rowEps ≤ (101210013/1000000000000) := by
  have hs : statisticsPayment ≤ (1908476971703/500000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (1945861148053/20000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12752 (1/10^6) (1/10^7) ((2028319/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 12752 : ℝ)*25504)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12752 : ℝ)*25504)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12752) (mW 12752)).real
      (goodDist 12752 (712/10000))ᶜ ≤ (101210013/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 12752) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (2028319/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12752 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (138887301399/200000000000000000)
  k0 := (3939626369509963/1000000000000000000)
  k6 := (485033209744013/40000000000000000)
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
  norm_lower := (window_guards (n := 12752) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12752) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((101210013/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12752 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12752) internalParameters :=
  BstLean.Part227.worldPackage (n := 12752) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (101210013/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12752) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world12752.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world12752, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world12752.frame := by
  exact frame.2.trans (by norm_num [Part268.world12752])

theorem moment_payment : internalParameters.moment ≤ Part268.world12752.moment := by
  exact moment.2.trans (by norm_num [Part268.world12752])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (73111337/62500000000) ∧
    internalParameters.frame ≤ (156221391411/250000000000) ∧
    internalParameters.moment ≤ (2330363931/250000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12752) (Part268.world12752) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world12752]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world12752])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world12752]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world12752]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12752).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12752).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow12752
namespace BstLean.Part268.WorldRow12753
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
    exp (-((mW 12753 : ℝ)*25506)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12753 : ℝ)*25506)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12753 : ℝ)*25506)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12753 : ℝ)*25506)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 25506 (mW 12753) i /
      (rowEps i * e1MeanBounds 25506 (mW 12753) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 25506 (mW 12753) (1/10^6) (1/10^7) rowEps ≤ (1014079/500000000000) := by
  have hr : 0 ≤ firstRatio 25506 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 25506 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 25506) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12753 (1/10^6) (1/10^7) ((1014079/500000000000))
      (712/10000) rowEps ≤ (101193587/1000000000000) := by
  have hs : statisticsPayment ≤ (1908179684567/500000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (24319306486193/250000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12753 (1/10^6) (1/10^7) ((1014079/500000000000))
      (712/10000) rowEps =
      exp (-((mW 12753 : ℝ)*25506)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12753 : ℝ)*25506)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12753) (mW 12753)).real
      (goodDist 12753 (712/10000))ᶜ ≤ (101193587/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 12753) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (1014079/500000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12753 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (694354829403/1000000000000000000)
  k0 := (984848669757093/250000000000000000)
  k6 := (6062677411693553/500000000000000000)
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
  norm_lower := (window_guards (n := 12753) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12753) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((101193587/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12753 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12753) internalParameters :=
  BstLean.Part227.worldPackage (n := 12753) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (101193587/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12753) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world12753.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world12753, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world12753.frame := by
  exact frame.2.trans (by norm_num [Part268.world12753])

theorem moment_payment : internalParameters.moment ≤ Part268.world12753.moment := by
  exact moment.2.trans (by norm_num [Part268.world12753])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (584869193/500000000000) ∧
    internalParameters.frame ≤ (624871819011/1000000000000) ∧
    internalParameters.moment ≤ (9319545467/1000000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12753) (Part268.world12753) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world12753]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world12753])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world12753]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world12753]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12753).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12753).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow12753
namespace BstLean.Part268.WorldRow12754
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
    exp (-((mW 12754 : ℝ)*25508)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12754 : ℝ)*25508)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12754 : ℝ)*25508)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12754 : ℝ)*25508)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 25508 (mW 12754) i /
      (rowEps i * e1MeanBounds 25508 (mW 12754) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 25508 (mW 12754) (1/10^6) (1/10^7) rowEps ≤ (2027997/1000000000000) := by
  have hr : 0 ≤ firstRatio 25508 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 25508 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 25508) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12754 (1/10^6) (1/10^7) ((2027997/1000000000000))
      (712/10000) rowEps ≤ (50588579/500000000000) := by
  have hs : statisticsPayment ≤ (190788248449/50000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (48630695612029/500000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12754 (1/10^6) (1/10^7) ((2027997/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 12754 : ℝ)*25508)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12754 : ℝ)*25508)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12754) (mW 12754)).real
      (goodDist 12754 (712/10000))ᶜ ≤ (50588579/500000000000) := by
  apply le_trans (concrete_distance_charge (n := 12754) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (2027997/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12754 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (34713658391/50000000000000000)
  k0 := (787832604067057/200000000000000000)
  k6 := (12124879459089231/1000000000000000000)
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
  norm_lower := (window_guards (n := 12754) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12754) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((50588579/500000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12754 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12754) internalParameters :=
  BstLean.Part227.worldPackage (n := 12754) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (50588579/500000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12754) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world12754.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world12754, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world12754.frame := by
  exact frame.2.trans (by norm_num [Part268.world12754])

theorem moment_payment : internalParameters.moment ≤ Part268.world12754.moment := by
  exact moment.2.trans (by norm_num [Part268.world12754])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1169695391/1000000000000) ∧
    internalParameters.frame ≤ (624858074571/1000000000000) ∧
    internalParameters.moment ≤ (4658817879/500000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12754) (Part268.world12754) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world12754]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world12754])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world12754]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world12754]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12754).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12754).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow12754
namespace BstLean.Part268.WorldRow12755
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
    exp (-((mW 12755 : ℝ)*25510)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12755 : ℝ)*25510)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12755 : ℝ)*25510)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12755 : ℝ)*25510)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 25510 (mW 12755) i /
      (rowEps i * e1MeanBounds 25510 (mW 12755) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 25510 (mW 12755) (1/10^6) (1/10^7) rowEps ≤ (2027837/1000000000000) := by
  have hr : 0 ≤ firstRatio 25510 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 25510 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 25510) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12755 (1/10^6) (1/10^7) ((2027837/1000000000000))
      (712/10000) rowEps ≤ (25290251/250000000000) := by
  have hs : statisticsPayment ≤ (30521365943/8000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (3889833281981/40000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12755 (1/10^6) (1/10^7) ((2027837/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 12755 : ℝ)*25510)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12755 : ℝ)*25510)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12755) (mW 12755)).real
      (goodDist 12755 (712/10000))ᶜ ≤ (25290251/250000000000) := by
  apply le_trans (concrete_distance_charge (n := 12755) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (2027837/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12755 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (347095761121/500000000000000000)
  k0 := (3938931393424961/1000000000000000000)
  k6 := (606220207534787/50000000000000000)
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
  norm_lower := (window_guards (n := 12755) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12755) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((25290251/250000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12755 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12755) internalParameters :=
  BstLean.Part227.worldPackage (n := 12755) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (25290251/250000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12755) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world12755.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world12755, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world12755.frame := by
  exact frame.2.trans (by norm_num [Part268.world12755])

theorem moment_payment : internalParameters.moment ≤ Part268.world12755.moment := by
  exact moment.2.trans (by norm_num [Part268.world12755])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1169652407/1000000000000) ∧
    internalParameters.frame ≤ (24993773293/40000000000) ∧
    internalParameters.moment ≤ (1863145319/200000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12755) (Part268.world12755) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world12755]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world12755])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world12755]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world12755]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12755).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12755).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow12755
namespace BstLean.Part268.WorldRow12756
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
    exp (-((mW 12756 : ℝ)*25512)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12756 : ℝ)*25512)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12756 : ℝ)*25512)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12756 : ℝ)*25512)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 25512 (mW 12756) i /
      (rowEps i * e1MeanBounds 25512 (mW 12756) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 25512 (mW 12756) (1/10^6) (1/10^7) rowEps ≤ (506919/250000000000) := by
  have hr : 0 ≤ firstRatio 25512 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 25512 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 25512) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12756 (1/10^6) (1/10^7) ((506919/250000000000))
      (712/10000) rowEps ≤ (101144569/1000000000000) := by
  have hs : statisticsPayment ≤ (3814576690749/1000000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (486149953929/5000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12756 (1/10^6) (1/10^7) ((506919/250000000000))
      (712/10000) rowEps =
      exp (-((mW 12756 : ℝ)*25512)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12756 : ℝ)*25512)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12756) (mW 12756)).real
      (goodDist 12756 (712/10000))ᶜ ≤ (101144569/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 12756) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (506919/250000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12756 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (347054946333/500000000000000000)
  k0 := (123084368696703/31250000000000000)
  k6 := (12123928898195677/1000000000000000000)
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
  norm_lower := (window_guards (n := 12756) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12756) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((101144569/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12756 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12756) internalParameters :=
  BstLean.Part227.worldPackage (n := 12756) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (101144569/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12756) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world12756.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world12756, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world12756.frame := by
  exact frame.2.trans (by norm_num [Part268.world12756])

theorem moment_payment : internalParameters.moment ≤ Part268.world12756.moment := by
  exact moment.2.trans (by norm_num [Part268.world12756])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (233921887/200000000000) ∧
    internalParameters.frame ≤ (39051912017/62500000000) ∧
    internalParameters.moment ≤ (9313817979/1000000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12756) (Part268.world12756) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world12756]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world12756])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world12756]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world12756]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12756).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12756).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow12756
namespace BstLean.Part268.WorldRow12757
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
    exp (-((mW 12757 : ℝ)*25514)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12757 : ℝ)*25514)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12757 : ℝ)*25514)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12757 : ℝ)*25514)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 25514 (mW 12757) i /
      (rowEps i * e1MeanBounds 25514 (mW 12757) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 25514 (mW 12757) (1/10^6) (1/10^7) rowEps ≤ (405503/200000000000) := by
  have hr : 0 ≤ firstRatio 25514 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 25514 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 25514) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12757 (1/10^6) (1/10^7) ((405503/200000000000))
      (712/10000) rowEps ≤ (101128131/1000000000000) := by
  have hs : statisticsPayment ≤ (953495703133/250000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (6075884141631/62500000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12757 (1/10^6) (1/10^7) ((405503/200000000000))
      (712/10000) rowEps =
      exp (-((mW 12757 : ℝ)*25514)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12757 : ℝ)*25514)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12757) (mW 12757)).real
      (goodDist 12757 (712/10000))ᶜ ≤ (101128131/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 12757) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (405503/200000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12757 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (347014139543/500000000000000000)
  k0 := (492308529366559/125000000000000000)
  k6 := (1515431712697261/125000000000000000)
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
  norm_lower := (window_guards (n := 12757) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12757) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((101128131/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12757 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12757) internalParameters :=
  BstLean.Part227.worldPackage (n := 12757) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (101128131/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12757) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world12757.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world12757, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world12757.frame := by
  exact frame.2.trans (by norm_num [Part268.world12757])

theorem moment_payment : internalParameters.moment ≤ Part268.world12757.moment := by
  exact moment.2.trans (by norm_num [Part268.world12757])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (584783237/500000000000) ∧
    internalParameters.frame ≤ (156204213603/250000000000) ∧
    internalParameters.moment ≤ (9311909909/1000000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12757) (Part268.world12757) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world12757]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world12757])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world12757]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world12757]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12757).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12757).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow12757
namespace BstLean.Part268.WorldRow12758
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
    exp (-((mW 12758 : ℝ)*25516)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12758 : ℝ)*25516)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12758 : ℝ)*25516)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12758 : ℝ)*25516)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 25516 (mW 12758) i /
      (rowEps i * e1MeanBounds 25516 (mW 12758) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 25516 (mW 12758) (1/10^6) (1/10^7) rowEps ≤ (405471/200000000000) := by
  have hr : 0 ≤ firstRatio 25516 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 25516 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 25516) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12758 (1/10^6) (1/10^7) ((405471/200000000000))
      (712/10000) rowEps ≤ (3159749/31250000000) := by
  have hs : statisticsPayment ≤ (762677821631/200000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (9719857722783/100000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12758 (1/10^6) (1/10^7) ((405471/200000000000))
      (712/10000) rowEps =
      exp (-((mW 12758 : ℝ)*25516)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12758 : ℝ)*25516)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12758) (mW 12758)).real
      (goodDist 12758 (712/10000))ᶜ ≤ (3159749/31250000000) := by
  apply le_trans (concrete_distance_charge (n := 12758) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (405471/200000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12758 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (693946681499/1000000000000000000)
  k0 := (3938236703335981/1000000000000000000)
  k6 := (12122978560832023/1000000000000000000)
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
  norm_lower := (window_guards (n := 12758) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12758) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((3159749/31250000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12758 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12758) internalParameters :=
  BstLean.Part227.worldPackage (n := 12758) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (3159749/31250000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12758) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world12758.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world12758, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world12758.frame := by
  exact frame.2.trans (by norm_num [Part268.world12758])

theorem moment_payment : internalParameters.moment ≤ Part268.world12758.moment := by
  exact moment.2.trans (by norm_num [Part268.world12758])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (292380881/250000000000) ∧
    internalParameters.frame ≤ (78100389843/125000000000) ∧
    internalParameters.moment ≤ (1862000477/200000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12758) (Part268.world12758) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world12758]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world12758])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world12758]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world12758]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12758).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12758).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow12758
namespace BstLean.Part268.WorldRow12759
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
    exp (-((mW 12759 : ℝ)*25518)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12759 : ℝ)*25518)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12759 : ℝ)*25518)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12759 : ℝ)*25518)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 25518 (mW 12759) i /
      (rowEps i * e1MeanBounds 25518 (mW 12759) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 25518 (mW 12759) (1/10^6) (1/10^7) rowEps ≤ (1013597/500000000000) := by
  have hr : 0 ≤ firstRatio 25518 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 25518 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 25518) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12759 (1/10^6) (1/10^7) ((1013597/500000000000))
      (712/10000) rowEps ≤ (101095523/1000000000000) := by
  have hs : statisticsPayment ≤ (3812795577549/1000000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (2429568154469/25000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12759 (1/10^6) (1/10^7) ((1013597/500000000000))
      (712/10000) rowEps =
      exp (-((mW 12759 : ℝ)*25518)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12759 : ℝ)*25518)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12759) (mW 12759)).real
      (goodDist 12759 (712/10000))ᶜ ≤ (101095523/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 12759) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (1013597/500000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12759 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (6938650999/10000000000000000)
  k0 := (984501300874109/250000000000000000)
  k6 := (12122503475946533/1000000000000000000)
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
  norm_lower := (window_guards (n := 12759) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12759) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((101095523/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12759 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12759) internalParameters :=
  BstLean.Part227.worldPackage (n := 12759) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (101095523/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12759) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world12759.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world12759, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world12759.frame := by
  exact frame.2.trans (by norm_num [Part268.world12759])

theorem moment_payment : internalParameters.moment ≤ Part268.world12759.moment := by
  exact moment.2.trans (by norm_num [Part268.world12759])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (584740293/500000000000) ∧
    internalParameters.frame ≤ (624789385267/1000000000000) ∧
    internalParameters.moment ≤ (9308095407/1000000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12759) (Part268.world12759) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world12759]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world12759])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world12759]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world12759]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12759).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12759).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow12759
namespace BstLean.Part268.WorldRow12760
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
    exp (-((mW 12760 : ℝ)*25520)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12760 : ℝ)*25520)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12760 : ℝ)*25520)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12760 : ℝ)*25520)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 25520 (mW 12760) i /
      (rowEps i * e1MeanBounds 25520 (mW 12760) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 25520 (mW 12760) (1/10^6) (1/10^7) rowEps ≤ (1013517/500000000000) := by
  have hr : 0 ≤ firstRatio 25520 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 25520 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 25520) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12760 (1/10^6) (1/10^7) ((1013517/500000000000))
      (712/10000) rowEps ≤ (50539677/500000000000) := by
  have hs : statisticsPayment ≤ (953050555161/250000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (97167150568217/1000000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12760 (1/10^6) (1/10^7) ((1013517/500000000000))
      (712/10000) rowEps =
      exp (-((mW 12760 : ℝ)*25520)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12760 : ℝ)*25520)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12760) (mW 12760)).real
      (goodDist 12760 (712/10000))ᶜ ≤ (50539677/500000000000) := by
  apply le_trans (concrete_distance_charge (n := 12760) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (1013517/500000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12760 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (173445883571/250000000000000000)
  k0 := (61527714615707/15625000000000000)
  k6 := (6061014223455337/500000000000000000)
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
  norm_lower := (window_guards (n := 12760) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12760) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((50539677/500000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12760 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12760) internalParameters :=
  BstLean.Part227.worldPackage (n := 12760) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (50539677/500000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12760) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world12760.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world12760, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world12760.frame := by
  exact frame.2.trans (by norm_num [Part268.world12760])

theorem moment_payment : internalParameters.moment ≤ Part268.world12760.moment := by
  exact moment.2.trans (by norm_num [Part268.world12760])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1169437659/1000000000000) ∧
    internalParameters.frame ≤ (624775653981/1000000000000) ∧
    internalParameters.moment ≤ (372247559/40000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12760) (Part268.world12760) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world12760]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world12760])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world12760]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world12760]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12760).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12760).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow12760
namespace BstLean.Part268.WorldRow12761
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
    exp (-((mW 12761 : ℝ)*25522)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12761 : ℝ)*25522)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12761 : ℝ)*25522)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12761 : ℝ)*25522)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 25522 (mW 12761) i /
      (rowEps i * e1MeanBounds 25522 (mW 12761) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 25522 (mW 12761) (1/10^6) (1/10^7) rowEps ≤ (2026873/1000000000000) := by
  have hr : 0 ≤ firstRatio 25522 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 25522 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 25522) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12761 (1/10^6) (1/10^7) ((2026873/1000000000000))
      (712/10000) rowEps ≤ (12632863/125000000000) := by
  have hs : statisticsPayment ≤ (3811609037371/1000000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (97151292998873/1000000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12761 (1/10^6) (1/10^7) ((2026873/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 12761 : ℝ)*25522)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12761 : ℝ)*25522)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12761) (mW 12761)).real
      (goodDist 12761 (712/10000))ᶜ ≤ (12632863/125000000000) := by
  apply le_trans (concrete_distance_charge (n := 12761) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (2026873/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12761 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (693701984647/1000000000000000000)
  k0 := (1968771149528333/500000000000000000)
  k6 := (2424310694742701/200000000000000000)
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
  norm_lower := (window_guards (n := 12761) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12761) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((12632863/125000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12761 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12761) internalParameters :=
  BstLean.Part227.worldPackage (n := 12761) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (12632863/125000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12761) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world12761.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world12761, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world12761.frame := by
  exact frame.2.trans (by norm_num [Part268.world12761])

theorem moment_payment : internalParameters.moment ≤ Part268.world12761.moment := by
  exact moment.2.trans (by norm_num [Part268.world12761])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1169394743/1000000000000) ∧
    internalParameters.frame ≤ (124952384977/200000000000) ∧
    internalParameters.moment ≤ (581517693/62500000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12761) (Part268.world12761) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world12761]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world12761])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world12761]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world12761]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12761).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12761).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow12761
namespace BstLean.Part268.WorldRow12762
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
    exp (-((mW 12762 : ℝ)*25524)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12762 : ℝ)*25524)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12762 : ℝ)*25524)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12762 : ℝ)*25524)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 25524 (mW 12762) i /
      (rowEps i * e1MeanBounds 25524 (mW 12762) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 25524 (mW 12762) (1/10^6) (1/10^7) rowEps ≤ (2026713/1000000000000) := by
  have hr : 0 ≤ firstRatio 25524 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 25524 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 25524) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12762 (1/10^6) (1/10^7) ((2026713/1000000000000))
      (712/10000) rowEps ≤ (12630841/125000000000) := by
  have hs : statisticsPayment ≤ (3811016027661/1000000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (12141963853131/125000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12762 (1/10^6) (1/10^7) ((2026713/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 12762 : ℝ)*25524)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12762 : ℝ)*25524)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12762) (mW 12762)).real
      (goodDist 12762 (712/10000))ᶜ ≤ (12630841/125000000000) := by
  apply le_trans (concrete_distance_charge (n := 12762) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (2026713/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12762 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (138724090197/200000000000000000)
  k0 := (984327723611233/250000000000000000)
  k6 := (6060539278172043/500000000000000000)
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
  norm_lower := (window_guards (n := 12762) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12762) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((12630841/125000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12762 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12762) internalParameters :=
  BstLean.Part227.worldPackage (n := 12762) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (12630841/125000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12762) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world12762.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world12762, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world12762.frame := by
  exact frame.2.trans (by norm_num [Part268.world12762])

theorem moment_payment : internalParameters.moment ≤ Part268.world12762.moment := by
  exact moment.2.trans (by norm_num [Part268.world12762])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1169351839/1000000000000) ∧
    internalParameters.frame ≤ (312374098989/500000000000) ∧
    internalParameters.moment ≤ (9302377747/1000000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12762) (Part268.world12762) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world12762]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world12762])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world12762]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world12762]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12762).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12762).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow12762
namespace BstLean.Part268.WorldRow12763
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
    exp (-((mW 12763 : ℝ)*25526)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12763 : ℝ)*25526)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12763 : ℝ)*25526)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12763 : ℝ)*25526)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 25526 (mW 12763) i /
      (rowEps i * e1MeanBounds 25526 (mW 12763) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 25526 (mW 12763) (1/10^6) (1/10^7) rowEps ≤ (253319/125000000000) := by
  have hr : 0 ≤ firstRatio 25526 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 25526 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 25526) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12763 (1/10^6) (1/10^7) ((253319/125000000000))
      (712/10000) rowEps ≤ (101030271/1000000000000) := by
  have hs : statisticsPayment ≤ (762084638289/200000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (48559923372263/500000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12763 (1/10^6) (1/10^7) ((253319/125000000000))
      (712/10000) rowEps =
      exp (-((mW 12763 : ℝ)*25526)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12763 : ℝ)*25526)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12763) (mW 12763)).real
      (goodDist 12763 (712/10000))ᶜ ≤ (101030271/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 12763) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (253319/125000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12763 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (346769466647/500000000000000000)
  k0 := (3937079521564291/1000000000000000000)
  k6 := (6060301847395741/500000000000000000)
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
  norm_lower := (window_guards (n := 12763) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12763) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((101030271/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12763 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12763) internalParameters :=
  BstLean.Part227.worldPackage (n := 12763) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (101030271/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12763) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world12763.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world12763, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world12763.frame := by
  exact frame.2.trans (by norm_num [Part268.world12763])

theorem moment_payment : internalParameters.moment ≤ Part268.world12763.moment := by
  exact moment.2.trans (by norm_num [Part268.world12763])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (584654473/500000000000) ∧
    internalParameters.frame ≤ (624734473261/1000000000000) ∧
    internalParameters.moment ≤ (9300472951/1000000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12763) (Part268.world12763) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world12763]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world12763])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world12763]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world12763]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12763).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12763).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow12763
namespace BstLean.Part268.WorldRow12764
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
    exp (-((mW 12764 : ℝ)*25528)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12764 : ℝ)*25528)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12764 : ℝ)*25528)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12764 : ℝ)*25528)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 25528 (mW 12764) i /
      (rowEps i * e1MeanBounds 25528 (mW 12764) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 25528 (mW 12764) (1/10^6) (1/10^7) rowEps ≤ (253299/125000000000) := by
  have hr : 0 ≤ firstRatio 25528 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 25528 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 25528) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12764 (1/10^6) (1/10^7) ((253299/125000000000))
      (712/10000) rowEps ≤ (10101409/100000000000) := by
  have hs : statisticsPayment ≤ (952457632163/250000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (12138032252053/125000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12764 (1/10^6) (1/10^7) ((253299/125000000000))
      (712/10000) rowEps =
      exp (-((mW 12764 : ℝ)*25528)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12764 : ℝ)*25528)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12764) (mW 12764)).real
      (goodDist 12764 (712/10000))ᶜ ≤ (10101409/100000000000) := by
  apply le_trans (concrete_distance_charge (n := 12764) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (253299/125000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12764 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (43341089473/62500000000000000)
  k0 := (492106022550413/125000000000000000)
  k6 := (303003222226119/25000000000000000)
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
  norm_lower := (window_guards (n := 12764) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12764) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((10101409/100000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12764 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12764) internalParameters :=
  BstLean.Part227.worldPackage (n := 12764) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (10101409/100000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12764) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world12764.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world12764, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world12764.frame := by
  exact frame.2.trans (by norm_num [Part268.world12764])

theorem moment_payment : internalParameters.moment ≤ Part268.world12764.moment := by
  exact moment.2.trans (by norm_num [Part268.world12764])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (73079129/62500000000) ∧
    internalParameters.frame ≤ (624720750733/1000000000000) ∧
    internalParameters.moment ≤ (92985687/10000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12764) (Part268.world12764) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world12764]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world12764])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world12764]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world12764]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12764).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12764).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow12764
namespace BstLean.Part268.WorldRow12765
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
    exp (-((mW 12765 : ℝ)*25530)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12765 : ℝ)*25530)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12765 : ℝ)*25530)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12765 : ℝ)*25530)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 25530 (mW 12765) i /
      (rowEps i * e1MeanBounds 25530 (mW 12765) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 25530 (mW 12765) (1/10^6) (1/10^7) rowEps ≤ (253279/125000000000) := by
  have hr : 0 ≤ firstRatio 25530 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 25530 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 25530) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12765 (1/10^6) (1/10^7) ((253279/125000000000))
      (712/10000) rowEps ≤ (50498953/500000000000) := by
  have hs : statisticsPayment ≤ (1904619019607/500000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (97088666002903/1000000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12765 (1/10^6) (1/10^7) ((253279/125000000000))
      (712/10000) rowEps =
      exp (-((mW 12765 : ℝ)*25530)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12765 : ℝ)*25530)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12765) (mW 12765)).real
      (goodDist 12765 (712/10000))ᶜ ≤ (50498953/500000000000) := by
  apply le_trans (concrete_distance_charge (n := 12765) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (253279/125000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12765 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (138675189161/200000000000000000)
  k0 := (1968308435480943/500000000000000000)
  k6 := (1211965413909299/100000000000000000)
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
  norm_lower := (window_guards (n := 12765) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12765) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((50498953/500000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12765 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12765) internalParameters :=
  BstLean.Part227.worldPackage (n := 12765) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (50498953/500000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12765) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world12765.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world12765, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world12765.frame := by
  exact frame.2.trans (by norm_num [Part268.world12765])

theorem moment_payment : internalParameters.moment ≤ Part268.world12765.moment := by
  exact moment.2.trans (by norm_num [Part268.world12765])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (584611597/500000000000) ∧
    internalParameters.frame ≤ (624707030393/1000000000000) ∧
    internalParameters.moment ≤ (4648332497/500000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12765) (Part268.world12765) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world12765]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world12765])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world12765]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world12765]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12765).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12765).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow12765
namespace BstLean.Part268.WorldRow12766
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
    exp (-((mW 12766 : ℝ)*25532)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12766 : ℝ)*25532)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12766 : ℝ)*25532)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12766 : ℝ)*25532)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 25532 (mW 12766) i /
      (rowEps i * e1MeanBounds 25532 (mW 12766) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 25532 (mW 12766) (1/10^6) (1/10^7) rowEps ≤ (2026071/1000000000000) := by
  have hr : 0 ≤ firstRatio 25532 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 25532 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 25532) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12766 (1/10^6) (1/10^7) ((2026071/1000000000000))
      (712/10000) rowEps ≤ (100981439/1000000000000) := by
  have hs : statisticsPayment ≤ (3808645723063/1000000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (4853639608023/50000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12766 (1/10^6) (1/10^7) ((2026071/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 12766 : ℝ)*25532)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12766 : ℝ)*25532)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12766) (mW 12766)).real
      (goodDist 12766 (712/10000))ᶜ ≤ (100981439/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 12766) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (2026071/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12766 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (346647237999/500000000000000000)
  k0 := (1968192796612879/500000000000000000)
  k6 := (12119179444925247/1000000000000000000)
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
  norm_lower := (window_guards (n := 12766) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12766) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((100981439/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12766 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12766) internalParameters :=
  BstLean.Part227.worldPackage (n := 12766) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (100981439/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12766) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world12766.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world12766, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world12766.frame := by
  exact frame.2.trans (by norm_num [Part268.world12766])

theorem moment_payment : internalParameters.moment ≤ Part268.world12766.moment := by
  exact moment.2.trans (by norm_num [Part268.world12766])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (584590167/500000000000) ∧
    internalParameters.frame ≤ (624693312239/1000000000000) ∧
    internalParameters.moment ≤ (1161845229/125000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12766) (Part268.world12766) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world12766]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world12766])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world12766]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world12766]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12766).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12766).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow12766
namespace BstLean.Part268.WorldRow12767
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
    exp (-((mW 12767 : ℝ)*25534)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12767 : ℝ)*25534)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12767 : ℝ)*25534)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12767 : ℝ)*25534)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 25534 (mW 12767) i /
      (rowEps i * e1MeanBounds 25534 (mW 12767) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 25534 (mW 12767) (1/10^6) (1/10^7) rowEps ≤ (2025911/1000000000000) := by
  have hr : 0 ≤ firstRatio 25534 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 25534 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 25534) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12767 (1/10^6) (1/10^7) ((2025911/1000000000000))
      (712/10000) rowEps ≤ (100965249/1000000000000) := by
  have hs : statisticsPayment ≤ (119001674379/31250000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (24264298401539/250000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12767 (1/10^6) (1/10^7) ((2025911/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 12767 : ℝ)*25534)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12767 : ℝ)*25534)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12767) (mW 12767)).real
      (goodDist 12767 (712/10000))ᶜ ≤ (100965249/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 12767) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (2025911/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12767 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (10831453471/15625000000000000)
  k0 := (393615434719199/100000000000000000)
  k6 := (6059352403265303/500000000000000000)
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
  norm_lower := (window_guards (n := 12767) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12767) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((100965249/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12767 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12767) internalParameters :=
  BstLean.Part227.worldPackage (n := 12767) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (100965249/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12767) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world12767.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world12767, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world12767.frame := by
  exact frame.2.trans (by norm_num [Part268.world12767])

theorem moment_payment : internalParameters.moment ≤ Part268.world12767.moment := by
  exact moment.2.trans (by norm_num [Part268.world12767])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (584568743/500000000000) ∧
    internalParameters.frame ≤ (624679596273/1000000000000) ∧
    internalParameters.moment ≤ (1858571843/200000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12767) (Part268.world12767) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world12767]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world12767])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world12767]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world12767]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12767).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12767).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow12767
namespace BstLean.Part268.WorldRow12768
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
    exp (-((mW 12768 : ℝ)*25536)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12768 : ℝ)*25536)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12768 : ℝ)*25536)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12768 : ℝ)*25536)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 25536 (mW 12768) i /
      (rowEps i * e1MeanBounds 25536 (mW 12768) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 25536 (mW 12768) (1/10^6) (1/10^7) rowEps ≤ (2025751/1000000000000) := by
  have hr : 0 ≤ firstRatio 25536 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 25536 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 25536) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12768 (1/10^6) (1/10^7) ((2025751/1000000000000))
      (712/10000) rowEps ≤ (20189811/200000000000) := by
  have hs : statisticsPayment ≤ (190373080517/50000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (1940831835463/20000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12768 (1/10^6) (1/10^7) ((2025751/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 12768 : ℝ)*25536)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12768 : ℝ)*25536)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12768) (mW 12768)).real
      (goodDist 12768 (712/10000))ᶜ ≤ (20189811/200000000000) := by
  apply le_trans (concrete_distance_charge (n := 12768) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (2025751/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12768 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (693131584239/1000000000000000000)
  k0 := (1967961566427407/500000000000000000)
  k6 := (6059115111949073/500000000000000000)
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
  norm_lower := (window_guards (n := 12768) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12768) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((20189811/200000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12768 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12768) internalParameters :=
  BstLean.Part227.worldPackage (n := 12768) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (20189811/200000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12768) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world12768.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world12768, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world12768.frame := by
  exact frame.2.trans (by norm_num [Part268.world12768])

theorem moment_payment : internalParameters.moment ≤ Part268.world12768.moment := by
  exact moment.2.trans (by norm_num [Part268.world12768])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (23381893/20000000000) ∧
    internalParameters.frame ≤ (312332941247/500000000000) ∧
    internalParameters.moment ≤ (4645478571/500000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12768) (Part268.world12768) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world12768]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world12768])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world12768]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world12768]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12768).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12768).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow12768
namespace BstLean.Part268.WorldRow12769
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
    exp (-((mW 12769 : ℝ)*25538)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12769 : ℝ)*25538)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12769 : ℝ)*25538)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12769 : ℝ)*25538)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 25538 (mW 12769) i /
      (rowEps i * e1MeanBounds 25538 (mW 12769) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 25538 (mW 12769) (1/10^6) (1/10^7) rowEps ≤ (202559/100000000000) := by
  have hr : 0 ≤ firstRatio 25538 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 25538 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 25538) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12769 (1/10^6) (1/10^7) ((202559/100000000000))
      (712/10000) rowEps ≤ (5046629/50000000000) := by
  have hs : statisticsPayment ≤ (3806869813631/1000000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (3881028327569/40000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12769 (1/10^6) (1/10^7) ((202559/100000000000))
      (712/10000) rowEps =
      exp (-((mW 12769 : ℝ)*25538)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12769 : ℝ)*25538)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12769) (mW 12769)).real
      (goodDist 12769 (712/10000))ᶜ ≤ (5046629/50000000000) := by
  apply le_trans (concrete_distance_charge (n := 12769) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (202559/100000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12769 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (346525081139/500000000000000000)
  k0 := (1967845975102809/500000000000000000)
  k6 := (242355113940339/20000000000000000)
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
  norm_lower := (window_guards (n := 12769) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12769) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((5046629/50000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12769 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12769) internalParameters :=
  BstLean.Part227.worldPackage (n := 12769) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (5046629/50000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12769) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world12769.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world12769, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world12769.frame := by
  exact frame.2.trans (by norm_num [Part268.world12769])

theorem moment_payment : internalParameters.moment ≤ Part268.world12769.moment := by
  exact moment.2.trans (by norm_num [Part268.world12769])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (73065739/62500000000) ∧
    internalParameters.frame ≤ (6246521709/10000000000) ∧
    internalParameters.moment ≤ (2322263903/250000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12769) (Part268.world12769) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world12769]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world12769])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world12769]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world12769]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12769).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12769).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow12769
namespace BstLean.Part268.WorldRow12770
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
    exp (-((mW 12770 : ℝ)*25540)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12770 : ℝ)*25540)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12770 : ℝ)*25540)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12770 : ℝ)*25540)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 25540 (mW 12770) i /
      (rowEps i * e1MeanBounds 25540 (mW 12770) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 25540 (mW 12770) (1/10^6) (1/10^7) rowEps ≤ (202543/100000000000) := by
  have hr : 0 ≤ firstRatio 25540 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 25540 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 25540) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12770 (1/10^6) (1/10^7) ((202543/100000000000))
      (712/10000) rowEps ≤ (5045819/50000000000) := by
  have hs : statisticsPayment ≤ (951569547483/250000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (24252524957237/250000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12770 (1/10^6) (1/10^7) ((202543/100000000000))
      (712/10000) rowEps =
      exp (-((mW 12770 : ℝ)*25540)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12770 : ℝ)*25540)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12770) (mW 12770)).real
      (goodDist 12770 (712/10000))ᶜ ≤ (5045819/50000000000) := by
  apply le_trans (concrete_distance_charge (n := 12770) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (202543/100000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12770 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (692968756257/1000000000000000000)
  k0 := (393546079923863/100000000000000000)
  k6 := (12117281225876103/1000000000000000000)
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
  norm_lower := (window_guards (n := 12770) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12770) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((5045819/50000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12770 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12770) internalParameters :=
  BstLean.Part227.worldPackage (n := 12770) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (5045819/50000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12770) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world12770.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world12770, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world12770.frame := by
  exact frame.2.trans (by norm_num [Part268.world12770])

theorem moment_payment : internalParameters.moment ≤ Part268.world12770.moment := by
  exact moment.2.trans (by norm_num [Part268.world12770])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (116900901/100000000000) ∧
    internalParameters.frame ≤ (624638461491/1000000000000) ∧
    internalParameters.moment ≤ (9287154627/1000000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12770) (Part268.world12770) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world12770]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world12770])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world12770]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world12770]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12770).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12770).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow12770
namespace BstLean.Part268.WorldRow12771
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
    exp (-((mW 12771 : ℝ)*25542)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12771 : ℝ)*25542)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12771 : ℝ)*25542)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12771 : ℝ)*25542)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 25542 (mW 12771) i /
      (rowEps i * e1MeanBounds 25542 (mW 12771) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 25542 (mW 12771) (1/10^6) (1/10^7) rowEps ≤ (202527/100000000000) := by
  have hr : 0 ≤ firstRatio 25542 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 25542 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 25542) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12771 (1/10^6) (1/10^7) ((202527/100000000000))
      (712/10000) rowEps ≤ (6306261/62500000000) := by
  have hs : statisticsPayment ≤ (3805686739173/1000000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (24248622049173/250000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12771 (1/10^6) (1/10^7) ((202527/100000000000))
      (712/10000) rowEps =
      exp (-((mW 12771 : ℝ)*25542)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12771 : ℝ)*25542)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12771) (mW 12771)).real
      (goodDist 12771 (712/10000))ᶜ ≤ (6306261/62500000000) := by
  apply le_trans (concrete_distance_charge (n := 12771) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (202527/100000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12771 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (692887366171/1000000000000000000)
  k0 := (245951854996577/62500000000000000)
  k6 := (12116806810464693/1000000000000000000)
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
  norm_lower := (window_guards (n := 12771) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12771) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((6306261/62500000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12771 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12771) internalParameters :=
  BstLean.Part227.worldPackage (n := 12771) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (6306261/62500000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12771) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world12771.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world12771, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world12771.frame := by
  exact frame.2.trans (by norm_num [Part268.world12771])

theorem moment_payment : internalParameters.moment ≤ Part268.world12771.moment := by
  exact moment.2.trans (by norm_num [Part268.world12771])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1168966207/1000000000000) ∧
    internalParameters.frame ≤ (156156188567/250000000000) ∧
    internalParameters.moment ≤ (1857050837/200000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12771) (Part268.world12771) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world12771]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world12771])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world12771]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world12771]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12771).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12771).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow12771
namespace BstLean.Part268.WorldRow12772
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
    exp (-((mW 12772 : ℝ)*25544)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12772 : ℝ)*25544)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12772 : ℝ)*25544)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12772 : ℝ)*25544)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 25544 (mW 12772) i /
      (rowEps i * e1MeanBounds 25544 (mW 12772) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 25544 (mW 12772) (1/10^6) (1/10^7) rowEps ≤ (202511/100000000000) := by
  have hr : 0 ≤ firstRatio 25544 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 25544 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 25544) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12772 (1/10^6) (1/10^7) ((202511/100000000000))
      (712/10000) rowEps ≤ (10088397/100000000000) := by
  have hs : statisticsPayment ≤ (1902547730643/500000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (96978873294693/1000000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12772 (1/10^6) (1/10^7) ((202511/100000000000))
      (712/10000) rowEps =
      exp (-((mW 12772 : ℝ)*25544)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12772 : ℝ)*25544)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12772) (mW 12772)).real
      (goodDist 12772 (712/10000))ᶜ ≤ (10088397/100000000000) := by
  apply le_trans (concrete_distance_charge (n := 12772) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (202511/100000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12772 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (43300374501/62500000000000000)
  k0 := (3934998592319647/1000000000000000000)
  k6 := (3029083112692953/250000000000000000)
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
  norm_lower := (window_guards (n := 12772) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12772) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((10088397/100000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12772 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12772) internalParameters :=
  BstLean.Part227.worldPackage (n := 12772) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (10088397/100000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12772) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world12772.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world12772, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world12772.frame := by
  exact frame.2.trans (by norm_num [Part268.world12772])

theorem moment_payment : internalParameters.moment ≤ Part268.world12772.moment := by
  exact moment.2.trans (by norm_num [Part268.world12772])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (146115427/125000000000) ∧
    internalParameters.frame ≤ (156152762307/250000000000) ∧
    internalParameters.moment ≤ (4641677143/500000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12772) (Part268.world12772) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world12772]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world12772])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world12772]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world12772]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12772).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12772).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow12772
namespace BstLean.Part268.WorldRow12773
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
    exp (-((mW 12773 : ℝ)*25546)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12773 : ℝ)*25546)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12773 : ℝ)*25546)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12773 : ℝ)*25546)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 25546 (mW 12773) i /
      (rowEps i * e1MeanBounds 25546 (mW 12773) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 25546 (mW 12773) (1/10^6) (1/10^7) rowEps ≤ (2024949/1000000000000) := by
  have hr : 0 ≤ firstRatio 25546 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 25546 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 25546) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12773 (1/10^6) (1/10^7) ((2024949/1000000000000))
      (712/10000) rowEps ≤ (100867483/1000000000000) := by
  have hs : statisticsPayment ≤ (3804504356201/1000000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (96962976745751/1000000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12773 (1/10^6) (1/10^7) ((2024949/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 12773 : ℝ)*25546)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12773 : ℝ)*25546)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12773) (mW 12773)).real
      (goodDist 12773 (712/10000))ᶜ ≤ (100867483/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 12773) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (2024949/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12773 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (173181158447/250000000000000000)
  k0 := (1967383768178047/500000000000000000)
  k6 := (6057929073393277/500000000000000000)
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
  norm_lower := (window_guards (n := 12773) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12773) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((100867483/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12773 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12773) internalParameters :=
  BstLean.Part227.worldPackage (n := 12773) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (100867483/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12773) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world12773.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world12773, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world12773.frame := by
  exact frame.2.trans (by norm_num [Part268.world12773])

theorem moment_payment : internalParameters.moment ≤ Part268.world12773.moment := by
  exact moment.2.trans (by norm_num [Part268.world12773])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (233776127/200000000000) ∧
    internalParameters.frame ≤ (156149336593/250000000000) ∧
    internalParameters.moment ≤ (9281454931/1000000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12773) (Part268.world12773) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world12773]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world12773])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world12773]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world12773]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12773).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12773).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow12773
namespace BstLean.Part268.WorldRow12774
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
    exp (-((mW 12774 : ℝ)*25548)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12774 : ℝ)*25548)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12774 : ℝ)*25548)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12774 : ℝ)*25548)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 25548 (mW 12774) i /
      (rowEps i * e1MeanBounds 25548 (mW 12774) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 25548 (mW 12774) (1/10^6) (1/10^7) rowEps ≤ (2024789/1000000000000) := by
  have hr : 0 ≤ firstRatio 25548 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 25548 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 25548) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12774 (1/10^6) (1/10^7) ((2024789/1000000000000))
      (712/10000) rowEps ≤ (10085127/100000000000) := by
  have hs : statisticsPayment ≤ (76078268477/20000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (96947355334507/1000000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12774 (1/10^6) (1/10^7) ((2024789/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 12774 : ℝ)*25548)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12774 : ℝ)*25548)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12774) (mW 12774)).real
      (goodDist 12774 (712/10000))ᶜ ≤ (10085127/100000000000) := by
  apply le_trans (concrete_distance_charge (n := 12774) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (2024789/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12774 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (346321645741/500000000000000000)
  k0 := (3934536512045949/1000000000000000000)
  k6 := (378605746828063/31250000000000000)
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
  norm_lower := (window_guards (n := 12774) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12774) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((10085127/100000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12774 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12774) internalParameters :=
  BstLean.Part227.worldPackage (n := 12774) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (10085127/100000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12774) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world12774.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world12774, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world12774.frame := by
  exact frame.2.trans (by norm_num [Part268.world12774])

theorem moment_payment : internalParameters.moment ≤ Part268.world12774.moment := by
  exact moment.2.trans (by norm_num [Part268.world12774])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (584418933/500000000000) ∧
    internalParameters.frame ≤ (312291822849/500000000000) ∧
    internalParameters.moment ≤ (9279556119/1000000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12774) (Part268.world12774) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world12774]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world12774])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world12774]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world12774]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12774).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12774).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow12774
