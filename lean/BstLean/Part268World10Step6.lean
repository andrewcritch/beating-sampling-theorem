import BstLean.Part268World10Step5
namespace BstLean.Part268.WorldRow12600
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
    exp (-((mW 12600 : ℝ)*25200)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12600 : ℝ)*25200)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12600 : ℝ)*25200)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12600 : ℝ)*25200)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 25200 (mW 12600) i /
      (rowEps i * e1MeanBounds 25200 (mW 12600) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 25200 (mW 12600) (1/10^6) (1/10^7) rowEps ≤ (410609/200000000000) := by
  have hr : 0 ≤ firstRatio 25200 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 25200 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 25200) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12600 (1/10^6) (1/10^7) ((410609/200000000000))
      (712/10000) rowEps ≤ (103741281/1000000000000) := by
  have hs : statisticsPayment ≤ (1954698094017/500000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (6233242702919/62500000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12600 (1/10^6) (1/10^7) ((410609/200000000000))
      (712/10000) rowEps =
      exp (-((mW 12600 : ℝ)*25200)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12600 : ℝ)*25200)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12600) (mW 12600)).real
      (goodDist 12600 (712/10000))ᶜ ≤ (103741281/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 12600) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (410609/200000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12600 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (17676008063/25000000000000000)
  k0 := (1987608563596087/500000000000000000)
  k6 := (2439750182371333/200000000000000000)
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
  norm_lower := (window_guards (n := 12600) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12600) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((103741281/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12600 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12600) internalParameters :=
  BstLean.Part227.worldPackage (n := 12600) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (103741281/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12600) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world12600.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world12600, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world12600.frame := by
  exact frame.2.trans (by norm_num [Part268.world12600])

theorem moment_payment : internalParameters.moment ≤ Part268.world12600.moment := by
  exact moment.2.trans (by norm_num [Part268.world12600])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (588226261/500000000000) ∧
    internalParameters.frame ≤ (627000905921/1000000000000) ∧
    internalParameters.moment ≤ (4809148459/500000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12600) (Part268.world12600) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world12600]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world12600])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world12600]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world12600]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12600).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12600).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow12600
namespace BstLean.Part268.WorldRow12601
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
    exp (-((mW 12601 : ℝ)*25202)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12601 : ℝ)*25202)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12601 : ℝ)*25202)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12601 : ℝ)*25202)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 25202 (mW 12601) i /
      (rowEps i * e1MeanBounds 25202 (mW 12601) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 25202 (mW 12601) (1/10^6) (1/10^7) rowEps ≤ (2052881/1000000000000) := by
  have hr : 0 ≤ firstRatio 25202 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 25202 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 25202) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12601 (1/10^6) (1/10^7) ((2052881/1000000000000))
      (712/10000) rowEps ≤ (103724497/1000000000000) := by
  have hs : statisticsPayment ≤ (2442983949/625000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (1558058141719/15625000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12601 (1/10^6) (1/10^7) ((2052881/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 12601 : ℝ)*25202)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12601 : ℝ)*25202)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12601) (mW 12601)).real
      (goodDist 12601 (712/10000))ᶜ ≤ (103724497/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 12601) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (2052881/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12601 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (706956159403/1000000000000000000)
  k0 := (1987490261778473/500000000000000000)
  k6 := (6099133431625877/500000000000000000)
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
  norm_lower := (window_guards (n := 12601) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12601) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((103724497/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12601 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12601) internalParameters :=
  BstLean.Part227.worldPackage (n := 12601) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (103724497/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12601) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world12601.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world12601, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world12601.frame := by
  exact frame.2.trans (by norm_num [Part268.world12601])

theorem moment_payment : internalParameters.moment ≤ Part268.world12601.moment := by
  exact moment.2.trans (by norm_num [Part268.world12601])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (588203873/500000000000) ∧
    internalParameters.frame ≤ (313493409579/500000000000) ∧
    internalParameters.moment ≤ (9616301131/1000000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12601) (Part268.world12601) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world12601]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world12601])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world12601]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world12601]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12601).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12601).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow12601
namespace BstLean.Part268.WorldRow12602
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
    exp (-((mW 12602 : ℝ)*25204)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12602 : ℝ)*25204)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12602 : ℝ)*25204)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12602 : ℝ)*25204)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 25204 (mW 12602) i /
      (rowEps i * e1MeanBounds 25204 (mW 12602) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 25204 (mW 12602) (1/10^6) (1/10^7) rowEps ≤ (513179/250000000000) := by
  have hr : 0 ≤ firstRatio 25204 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 25204 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 25204) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12602 (1/10^6) (1/10^7) ((513179/250000000000))
      (712/10000) rowEps ≤ (103707427/1000000000000) := by
  have hs : statisticsPayment ≤ (3908152633863/1000000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (19939854584559/200000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12602 (1/10^6) (1/10^7) ((513179/250000000000))
      (712/10000) rowEps =
      exp (-((mW 12602 : ℝ)*25204)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12602 : ℝ)*25204)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12602) (mW 12602)).real
      (goodDist 12602 (712/10000))ᶜ ≤ (103707427/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 12602) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (513179/250000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12602 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (706872012981/1000000000000000000)
  k0 := (3974743952775493/1000000000000000000)
  k6 := (487911314890547/40000000000000000)
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
  norm_lower := (window_guards (n := 12602) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12602) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((103707427/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12602 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12602) internalParameters :=
  BstLean.Part227.worldPackage (n := 12602) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (103707427/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12602) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world12602.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world12602, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world12602.frame := by
  exact frame.2.trans (by norm_num [Part268.world12602])

theorem moment_payment : internalParameters.moment ≤ Part268.world12602.moment := by
  exact moment.2.trans (by norm_num [Part268.world12602])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1176362983/1000000000000) ∧
    internalParameters.frame ≤ (25078909387/40000000000) ∧
    internalParameters.moment ≤ (9614305923/1000000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12602) (Part268.world12602) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world12602]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world12602])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world12602]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world12602]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12602).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12602).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow12602
namespace BstLean.Part268.WorldRow12603
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
    exp (-((mW 12603 : ℝ)*25206)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12603 : ℝ)*25206)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12603 : ℝ)*25206)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12603 : ℝ)*25206)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 25206 (mW 12603) i /
      (rowEps i * e1MeanBounds 25206 (mW 12603) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 25206 (mW 12603) (1/10^6) (1/10^7) rowEps ≤ (2052551/1000000000000) := by
  have hr : 0 ≤ firstRatio 25206 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 25206 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 25206) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12603 (1/10^6) (1/10^7) ((2052551/1000000000000))
      (712/10000) rowEps ≤ (51845177/500000000000) := by
  have hs : statisticsPayment ≤ (3907531134349/1000000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (12460352669103/125000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12603 (1/10^6) (1/10^7) ((2052551/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 12603 : ℝ)*25206)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12603 : ℝ)*25206)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12603) (mW 12603)).real
      (goodDist 12603 (712/10000))ᶜ ≤ (51845177/500000000000) := by
  apply le_trans (concrete_distance_charge (n := 12603) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (2052551/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12603 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (706787883251/1000000000000000000)
  k0 := (62101678356957/15625000000000000)
  k6 := (6098649469440499/500000000000000000)
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
  norm_lower := (window_guards (n := 12603) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12603) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((51845177/500000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12603 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12603) internalParameters :=
  BstLean.Part227.worldPackage (n := 12603) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (51845177/500000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12603) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world12603.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world12603, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world12603.frame := by
  exact frame.2.trans (by norm_num [Part268.world12603])

theorem moment_payment : internalParameters.moment ≤ Part268.world12603.moment := by
  exact moment.2.trans (by norm_num [Part268.world12603])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1176318231/1000000000000) ∧
    internalParameters.frame ≤ (626958652473/1000000000000) ∧
    internalParameters.moment ≤ (2403077823/250000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12603) (Part268.world12603) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world12603]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world12603])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world12603]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world12603]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12603).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12603).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow12603
namespace BstLean.Part268.WorldRow12604
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
    exp (-((mW 12604 : ℝ)*25208)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12604 : ℝ)*25208)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12604 : ℝ)*25208)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12604 : ℝ)*25208)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 25208 (mW 12604) i /
      (rowEps i * e1MeanBounds 25208 (mW 12604) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 25208 (mW 12604) (1/10^6) (1/10^7) rowEps ≤ (2052387/1000000000000) := by
  have hr : 0 ≤ firstRatio 25208 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 25208 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 25208) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12604 (1/10^6) (1/10^7) ((2052387/1000000000000))
      (712/10000) rowEps ≤ (2591839/25000000000) := by
  have hs : statisticsPayment ≤ (3906909819781/1000000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (49833324404753/500000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12604 (1/10^6) (1/10^7) ((2052387/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 12604 : ℝ)*25208)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12604 : ℝ)*25208)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12604) (mW 12604)).real
      (goodDist 12604 (712/10000))ᶜ ≤ (2591839/25000000000) := by
  apply le_trans (concrete_distance_charge (n := 12604) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (2052387/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12604 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (22084492819/31250000000000000)
  k0 := (794854181951603/200000000000000000)
  k6 := (12196815063092297/1000000000000000000)
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
  norm_lower := (window_guards (n := 12604) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12604) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((2591839/25000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12604 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12604) internalParameters :=
  BstLean.Part227.worldPackage (n := 12604) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (2591839/25000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12604) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world12604.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world12604, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world12604.frame := by
  exact frame.2.trans (by norm_num [Part268.world12604])

theorem moment_payment : internalParameters.moment ≤ Part268.world12604.moment := by
  exact moment.2.trans (by norm_num [Part268.world12604])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1176273491/1000000000000) ∧
    internalParameters.frame ≤ (78368071569/125000000000) ∧
    internalParameters.moment ≤ (240257931/25000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12604) (Part268.world12604) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world12604]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world12604])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world12604]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world12604]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12604).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12604).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow12604
namespace BstLean.Part268.WorldRow12605
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
    exp (-((mW 12605 : ℝ)*25210)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12605 : ℝ)*25210)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12605 : ℝ)*25210)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12605 : ℝ)*25210)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 25210 (mW 12605) i /
      (rowEps i * e1MeanBounds 25210 (mW 12605) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 25210 (mW 12605) (1/10^6) (1/10^7) rowEps ≤ (1026111/500000000000) := by
  have hr : 0 ≤ firstRatio 25210 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 25210 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 25210) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12605 (1/10^6) (1/10^7) ((1026111/500000000000))
      (712/10000) rowEps ≤ (103656481/1000000000000) := by
  have hs : statisticsPayment ≤ (781257738017/200000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (49825095188213/500000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12605 (1/10^6) (1/10^7) ((1026111/500000000000))
      (712/10000) rowEps =
      exp (-((mW 12605 : ℝ)*25210)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12605 : ℝ)*25210)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12605) (mW 12605)).real
      (goodDist 12605 (712/10000))ᶜ ≤ (103656481/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 12605) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (1026111/500000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12605 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (706619673847/1000000000000000000)
  k0 := (2483771523441/625000000000000)
  k6 := (12196331244886149/1000000000000000000)
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
  norm_lower := (window_guards (n := 12605) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12605) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((103656481/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12605 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12605) internalParameters :=
  BstLean.Part227.worldPackage (n := 12605) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (103656481/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12605) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world12605.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world12605, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world12605.frame := by
  exact frame.2.trans (by norm_num [Part268.world12605])

theorem moment_payment : internalParameters.moment ≤ Part268.world12605.moment := by
  exact moment.2.trans (by norm_num [Part268.world12605])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1176228763/1000000000000) ∧
    internalParameters.frame ≤ (62693049491/100000000000) ∧
    internalParameters.moment ≤ (4804161883/500000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12605) (Part268.world12605) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world12605]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world12605])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world12605]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world12605]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12605).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12605).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow12605
namespace BstLean.Part268.WorldRow12606
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
    exp (-((mW 12606 : ℝ)*25212)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12606 : ℝ)*25212)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12606 : ℝ)*25212)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12606 : ℝ)*25212)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 25212 (mW 12606) i /
      (rowEps i * e1MeanBounds 25212 (mW 12606) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 25212 (mW 12606) (1/10^6) (1/10^7) rowEps ≤ (1026029/500000000000) := by
  have hr : 0 ≤ firstRatio 25212 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 25212 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 25212) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12606 (1/10^6) (1/10^7) ((1026029/500000000000))
      (712/10000) rowEps ≤ (161937/1562500000) := by
  have hs : statisticsPayment ≤ (1952833872593/500000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (49817005463043/500000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12606 (1/10^6) (1/10^7) ((1026029/500000000000))
      (712/10000) rowEps =
      exp (-((mW 12606 : ℝ)*25212)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12606 : ℝ)*25212)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12606) (mW 12606)).real
      (goodDist 12606 (712/10000))ᶜ ≤ (161937/1562500000) := by
  apply le_trans (concrete_distance_charge (n := 12606) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (1026029/500000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12606 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (176633898541/250000000000000000)
  k0 := (496724749760327/125000000000000000)
  k6 := (6097923742125567/500000000000000000)
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
  norm_lower := (window_guards (n := 12606) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12606) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((161937/1562500000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12606 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12606) internalParameters :=
  BstLean.Part227.worldPackage (n := 12606) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (161937/1562500000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12606) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world12606.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world12606, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world12606.frame := by
  exact frame.2.trans (by norm_num [Part268.world12606])

theorem moment_payment : internalParameters.moment ≤ Part268.world12606.moment := by
  exact moment.2.trans (by norm_num [Part268.world12606])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1176184047/1000000000000) ∧
    internalParameters.frame ≤ (156729104887/250000000000) ∧
    internalParameters.moment ≤ (960633087/100000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12606) (Part268.world12606) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world12606]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world12606])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world12606]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world12606]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12606).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12606).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow12606
namespace BstLean.Part268.WorldRow12607
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
    exp (-((mW 12607 : ℝ)*25214)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12607 : ℝ)*25214)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12607 : ℝ)*25214)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12607 : ℝ)*25214)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 25214 (mW 12607) i /
      (rowEps i * e1MeanBounds 25214 (mW 12607) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 25214 (mW 12607) (1/10^6) (1/10^7) rowEps ≤ (2051893/1000000000000) := by
  have hr : 0 ≤ firstRatio 25214 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 25214 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 25214) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12607 (1/10^6) (1/10^7) ((2051893/1000000000000))
      (712/10000) rowEps ≤ (51811297/500000000000) := by
  have hs : statisticsPayment ≤ (390504698501/100000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (99617545639579/1000000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12607 (1/10^6) (1/10^7) ((2051893/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 12607 : ℝ)*25214)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12607 : ℝ)*25214)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12607) (mW 12607)).real
      (goodDist 12607 (712/10000))ᶜ ≤ (51811297/500000000000) := by
  apply le_trans (concrete_distance_charge (n := 12607) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (2051893/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12607 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (706451531153/1000000000000000000)
  k0 := (124173799733689/31250000000000000)
  k6 := (2439072756235167/200000000000000000)
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
  norm_lower := (window_guards (n := 12607) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12607) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((51811297/500000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12607 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12607) internalParameters :=
  BstLean.Part227.worldPackage (n := 12607) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (51811297/500000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12607) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world12607.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world12607, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world12607.frame := by
  exact frame.2.trans (by norm_num [Part268.world12607])

theorem moment_payment : internalParameters.moment ≤ Part268.world12607.moment := by
  exact moment.2.trans (by norm_num [Part268.world12607])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1176139343/1000000000000) ∧
    internalParameters.frame ≤ (19590698327/31250000000) ∧
    internalParameters.moment ≤ (9604338551/1000000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12607) (Part268.world12607) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world12607]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world12607])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world12607]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world12607]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12607).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12607).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow12607
namespace BstLean.Part268.WorldRow12608
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
    exp (-((mW 12608 : ℝ)*25216)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12608 : ℝ)*25216)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12608 : ℝ)*25216)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12608 : ℝ)*25216)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 25216 (mW 12608) i /
      (rowEps i * e1MeanBounds 25216 (mW 12608) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 25216 (mW 12608) (1/10^6) (1/10^7) rowEps ≤ (2051729/1000000000000) := by
  have hr : 0 ≤ firstRatio 25216 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 25216 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 25216) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12608 (1/10^6) (1/10^7) ((2051729/1000000000000))
      (712/10000) rowEps ≤ (103605787/1000000000000) := by
  have hs : statisticsPayment ≤ (3904426409481/1000000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (99601359291801/1000000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12608 (1/10^6) (1/10^7) ((2051729/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 12608 : ℝ)*25216)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12608 : ℝ)*25216)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12608) (mW 12608)).real
      (goodDist 12608 (712/10000))ᶜ ≤ (103605787/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 12608) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (2051729/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12608 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (706367484811/1000000000000000000)
  k0 := (993331304422329/250000000000000000)
  k6 := (12194880135648839/1000000000000000000)
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
  norm_lower := (window_guards (n := 12608) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12608) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((103605787/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12608 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12608) internalParameters :=
  BstLean.Part227.worldPackage (n := 12608) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (103605787/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12608) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world12608.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world12608, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world12608.frame := by
  exact frame.2.trans (by norm_num [Part268.world12608])

theorem moment_payment : internalParameters.moment ≤ Part268.world12608.moment := by
  exact moment.2.trans (by norm_num [Part268.world12608])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1176094651/1000000000000) ∧
    internalParameters.frame ≤ (626888275657/1000000000000) ∧
    internalParameters.moment ≤ (9602346809/1000000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12608) (Part268.world12608) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world12608]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world12608])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world12608]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world12608]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12608).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12608).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow12608
namespace BstLean.Part268.WorldRow12609
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
    exp (-((mW 12609 : ℝ)*25218)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12609 : ℝ)*25218)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12609 : ℝ)*25218)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12609 : ℝ)*25218)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 25218 (mW 12609) i /
      (rowEps i * e1MeanBounds 25218 (mW 12609) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 25218 (mW 12609) (1/10^6) (1/10^7) rowEps ≤ (512891/250000000000) := by
  have hr : 0 ≤ firstRatio 25218 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 25218 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 25218) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12609 (1/10^6) (1/10^7) ((512891/250000000000))
      (712/10000) rowEps ≤ (20717739/200000000000) := by
  have hs : statisticsPayment ≤ (156152240741/40000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (49792443580779/500000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12609 (1/10^6) (1/10^7) ((512891/250000000000))
      (712/10000) rowEps =
      exp (-((mW 12609 : ℝ)*25218)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12609 : ℝ)*25218)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12609) (mW 12609)).real
      (goodDist 12609 (712/10000))ᶜ ≤ (20717739/200000000000) := by
  apply le_trans (concrete_distance_charge (n := 12609) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (512891/250000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12609 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (176570863783/250000000000000000)
  k0 := (3973088876705403/1000000000000000000)
  k6 := (2438879309531747/200000000000000000)
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
  norm_lower := (window_guards (n := 12609) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12609) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((20717739/200000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12609 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12609) internalParameters :=
  BstLean.Part227.worldPackage (n := 12609) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (20717739/200000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12609) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world12609.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world12609, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world12609.frame := by
  exact frame.2.trans (by norm_num [Part268.world12609])

theorem moment_payment : internalParameters.moment ≤ Part268.world12609.moment := by
  exact moment.2.trans (by norm_num [Part268.world12609])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1176049971/1000000000000) ∧
    internalParameters.frame ≤ (78359275891/125000000000) ∧
    internalParameters.moment ≤ (1920071129/200000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12609) (Part268.world12609) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world12609]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world12609])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world12609]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world12609]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12609).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12609).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow12609
namespace BstLean.Part268.WorldRow12610
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
    exp (-((mW 12610 : ℝ)*25220)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12610 : ℝ)*25220)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12610 : ℝ)*25220)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12610 : ℝ)*25220)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 25220 (mW 12610) i /
      (rowEps i * e1MeanBounds 25220 (mW 12610) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 25220 (mW 12610) (1/10^6) (1/10^7) rowEps ≤ (10257/5000000000) := by
  have hr : 0 ≤ firstRatio 25220 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 25220 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 25220) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12610 (1/10^6) (1/10^7) ((10257/5000000000))
      (712/10000) rowEps ≤ (103571881/1000000000000) := by
  have hs : statisticsPayment ≤ (975796453017/250000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (19913738785187/200000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12610 (1/10^6) (1/10^7) ((10257/5000000000))
      (712/10000) rowEps =
      exp (-((mW 12610 : ℝ)*25220)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12610 : ℝ)*25220)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12610) (mW 12610)).real
      (goodDist 12610 (712/10000))ᶜ ≤ (103571881/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 12610) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (10257/5000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12610 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (11034366283/15625000000000000)
  k0 := (248303285532557/62500000000000000)
  k6 := (12193913017194117/1000000000000000000)
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
  norm_lower := (window_guards (n := 12610) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12610) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((103571881/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12610 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12610) internalParameters :=
  BstLean.Part227.worldPackage (n := 12610) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (103571881/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12610) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world12610.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world12610, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world12610.frame := by
  exact frame.2.trans (by norm_num [Part268.world12610])

theorem moment_payment : internalParameters.moment ≤ Part268.world12610.moment := by
  exact moment.2.trans (by norm_num [Part268.world12610])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1176005303/1000000000000) ∧
    internalParameters.frame ≤ (156715035219/250000000000) ∧
    internalParameters.moment ≤ (9598365057/1000000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12610) (Part268.world12610) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world12610]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world12610])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world12610]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world12610]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12610).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12610).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow12610
namespace BstLean.Part268.WorldRow12611
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
    exp (-((mW 12611 : ℝ)*25222)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12611 : ℝ)*25222)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12611 : ℝ)*25222)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12611 : ℝ)*25222)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 25222 (mW 12611) i /
      (rowEps i * e1MeanBounds 25222 (mW 12611) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 25222 (mW 12611) (1/10^6) (1/10^7) rowEps ≤ (410247/200000000000) := by
  have hr : 0 ≤ firstRatio 25222 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 25222 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 25222) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12611 (1/10^6) (1/10^7) ((410247/200000000000))
      (712/10000) rowEps ≤ (51777391/500000000000) := by
  have hs : statisticsPayment ≤ (3902565790033/1000000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (49776107480827/500000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12611 (1/10^6) (1/10^7) ((410247/200000000000))
      (712/10000) rowEps =
      exp (-((mW 12611 : ℝ)*25222)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12611 : ℝ)*25222)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12611) (mW 12611)).real
      (goodDist 12611 (712/10000))ᶜ ≤ (51777391/500000000000) := by
  apply le_trans (concrete_distance_charge (n := 12611) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (410247/200000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12611 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (706115445747/1000000000000000000)
  k0 := (1986308146565221/500000000000000000)
  k6 := (12193429544243579/1000000000000000000)
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
  norm_lower := (window_guards (n := 12611) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12611) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((51777391/500000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12611 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12611) internalParameters :=
  BstLean.Part227.worldPackage (n := 12611) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (51777391/500000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12611) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world12611.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world12611, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world12611.frame := by
  exact frame.2.trans (by norm_num [Part268.world12611])

theorem moment_payment : internalParameters.moment ≤ Part268.world12611.moment := by
  exact moment.2.trans (by norm_num [Part268.world12611])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (587980323/500000000000) ∧
    internalParameters.frame ≤ (6268460769/10000000000) ∧
    internalParameters.moment ≤ (4798187523/500000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12611) (Part268.world12611) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world12611]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world12611])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world12611]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world12611]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12611).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12611).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow12611
namespace BstLean.Part268.WorldRow12612
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
    exp (-((mW 12612 : ℝ)*25224)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12612 : ℝ)*25224)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12612 : ℝ)*25224)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12612 : ℝ)*25224)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 25224 (mW 12612) i /
      (rowEps i * e1MeanBounds 25224 (mW 12612) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 25224 (mW 12612) (1/10^6) (1/10^7) rowEps ≤ (2051071/1000000000000) := by
  have hr : 0 ≤ firstRatio 25224 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 25224 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 25224) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12612 (1/10^6) (1/10^7) ((2051071/1000000000000))
      (712/10000) rowEps ≤ (51768981/500000000000) := by
  have hs : statisticsPayment ≤ (975486488087/250000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (49768007423893/500000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12612 (1/10^6) (1/10^7) ((2051071/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 12612 : ℝ)*25224)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12612 : ℝ)*25224)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12612) (mW 12612)).real
      (goodDist 12612 (712/10000))ᶜ ≤ (51768981/500000000000) := by
  apply le_trans (concrete_distance_charge (n := 12612) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (2051071/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12612 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (706031466031/1000000000000000000)
  k0 := (496547506315371/125000000000000000)
  k6 := (12192946128795721/1000000000000000000)
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
  norm_lower := (window_guards (n := 12612) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12612) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((51768981/500000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12612 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12612) internalParameters :=
  BstLean.Part227.worldPackage (n := 12612) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (51768981/500000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12612) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world12612.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world12612, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world12612.frame := by
  exact frame.2.trans (by norm_num [Part268.world12612])

theorem moment_payment : internalParameters.moment ≤ Part268.world12612.moment := by
  exact moment.2.trans (by norm_num [Part268.world12612])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (587958001/500000000000) ∧
    internalParameters.frame ≤ (626832015199/1000000000000) ∧
    internalParameters.moment ≤ (2398596403/250000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12612) (Part268.world12612) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world12612]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world12612])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world12612]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world12612]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12612).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12612).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow12612
namespace BstLean.Part268.WorldRow12613
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
    exp (-((mW 12613 : ℝ)*25226)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12613 : ℝ)*25226)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12613 : ℝ)*25226)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12613 : ℝ)*25226)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 25226 (mW 12613) i /
      (rowEps i * e1MeanBounds 25226 (mW 12613) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 25226 (mW 12613) (1/10^6) (1/10^7) rowEps ≤ (2050907/1000000000000) := by
  have hr : 0 ≤ firstRatio 25226 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 25226 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 25226) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12613 (1/10^6) (1/10^7) ((2050907/1000000000000))
      (712/10000) rowEps ≤ (103521139/1000000000000) := by
  have hs : statisticsPayment ≤ (3901326298937/1000000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (99519811286389/1000000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12613 (1/10^6) (1/10^7) ((2050907/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 12613 : ℝ)*25226)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12613 : ℝ)*25226)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12613) (mW 12613)).real
      (goodDist 12613 (712/10000))ᶜ ≤ (103521139/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 12613) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (2050907/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12613 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (705947502961/1000000000000000000)
  k0 := (3972143840695897/1000000000000000000)
  k6 := (6096231385419573/500000000000000000)
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
  norm_lower := (window_guards (n := 12613) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12613) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((103521139/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12613 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12613) internalParameters :=
  BstLean.Part227.worldPackage (n := 12613) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (103521139/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12613) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world12613.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world12613, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world12613.frame := by
  exact frame.2.trans (by norm_num [Part268.world12613])

theorem moment_payment : internalParameters.moment ≤ Part268.world12613.moment := by
  exact moment.2.trans (by norm_num [Part268.world12613])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1175871369/1000000000000) ∧
    internalParameters.frame ≤ (313408977887/500000000000) ∧
    internalParameters.moment ≤ (4796198377/500000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12613) (Part268.world12613) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world12613]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world12613])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world12613]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world12613]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12613).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12613).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow12613
namespace BstLean.Part268.WorldRow12614
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
    exp (-((mW 12614 : ℝ)*25228)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12614 : ℝ)*25228)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12614 : ℝ)*25228)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12614 : ℝ)*25228)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 25228 (mW 12614) i /
      (rowEps i * e1MeanBounds 25228 (mW 12614) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 25228 (mW 12614) (1/10^6) (1/10^7) rowEps ≤ (1025371/500000000000) := by
  have hr : 0 ≤ firstRatio 25228 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 25228 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 25228) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12614 (1/10^6) (1/10^7) ((1025371/500000000000))
      (712/10000) rowEps ≤ (10350403/100000000000) := by
  have hs : statisticsPayment ≤ (156028273189/40000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (99503322076669/1000000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12614 (1/10^6) (1/10^7) ((1025371/500000000000))
      (712/10000) rowEps =
      exp (-((mW 12614 : ℝ)*25228)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12614 : ℝ)*25228)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12614) (mW 12614)).real
      (goodDist 12614 (712/10000))ᶜ ≤ (10350403/100000000000) := by
  apply le_trans (concrete_distance_charge (n := 12614) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (1025371/500000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12614 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (705863556531/1000000000000000000)
  k0 := (3971907663638199/1000000000000000000)
  k6 := (12191979470362459/1000000000000000000)
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
  norm_lower := (window_guards (n := 12614) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12614) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((10350403/100000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12614 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12614) internalParameters :=
  BstLean.Part227.worldPackage (n := 12614) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (10350403/100000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12614) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world12614.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world12614, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world12614.frame := by
  exact frame.2.trans (by norm_num [Part268.world12614])

theorem moment_payment : internalParameters.moment ≤ Part268.world12614.moment := by
  exact moment.2.trans (by norm_num [Part268.world12614])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1175826749/1000000000000) ∧
    internalParameters.frame ≤ (313401949311/500000000000) ∧
    internalParameters.moment ≤ (9590408471/1000000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12614) (Part268.world12614) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world12614]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world12614])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world12614]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world12614]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12614).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12614).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow12614
namespace BstLean.Part268.WorldRow12615
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
    exp (-((mW 12615 : ℝ)*25230)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12615 : ℝ)*25230)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12615 : ℝ)*25230)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12615 : ℝ)*25230)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 25230 (mW 12615) i /
      (rowEps i * e1MeanBounds 25230 (mW 12615) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 25230 (mW 12615) (1/10^6) (1/10^7) rowEps ≤ (1025289/500000000000) := by
  have hr : 0 ≤ firstRatio 25230 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 25230 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 25230) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12615 (1/10^6) (1/10^7) ((1025289/500000000000))
      (712/10000) rowEps ≤ (103487201/1000000000000) := by
  have hs : statisticsPayment ≤ (3900087544639/1000000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (99487111651419/1000000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12615 (1/10^6) (1/10^7) ((1025289/500000000000))
      (712/10000) rowEps =
      exp (-((mW 12615 : ℝ)*25230)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12615 : ℝ)*25230)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12615) (mW 12615)).real
      (goodDist 12615 (712/10000))ᶜ ≤ (103487201/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 12615) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (1025289/500000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12615 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (705779626737/1000000000000000000)
  k0 := (3971671519344463/1000000000000000000)
  k6 := (3047874056838567/250000000000000000)
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
  norm_lower := (window_guards (n := 12615) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12615) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((103487201/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12615 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12615) internalParameters :=
  BstLean.Part227.worldPackage (n := 12615) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (103487201/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12615) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world12615.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world12615, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world12615.frame := by
  exact frame.2.trans (by norm_num [Part268.world12615])

theorem moment_payment : internalParameters.moment ≤ Part268.world12615.moment := by
  exact moment.2.trans (by norm_num [Part268.world12615])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (58789107/50000000000) ∧
    internalParameters.frame ≤ (125357968749/200000000000) ∧
    internalParameters.moment ≤ (1917684153/200000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12615) (Part268.world12615) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world12615]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world12615])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world12615]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world12615]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12615).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12615).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow12615
namespace BstLean.Part268.WorldRow12616
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
    exp (-((mW 12616 : ℝ)*25232)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12616 : ℝ)*25232)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12616 : ℝ)*25232)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12616 : ℝ)*25232)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 25232 (mW 12616) i /
      (rowEps i * e1MeanBounds 25232 (mW 12616) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 25232 (mW 12616) (1/10^6) (1/10^7) rowEps ≤ (1025207/500000000000) := by
  have hr : 0 ≤ firstRatio 25232 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 25232 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 25232) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12616 (1/10^6) (1/10^7) ((1025207/500000000000))
      (712/10000) rowEps ≤ (3233449/31250000000) := by
  have hs : statisticsPayment ≤ (3899468443603/1000000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (99470897785803/1000000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12616 (1/10^6) (1/10^7) ((1025207/500000000000))
      (712/10000) rowEps =
      exp (-((mW 12616 : ℝ)*25232)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12616 : ℝ)*25232)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12616) (mW 12616)).real
      (goodDist 12616 (712/10000))ᶜ ≤ (3233449/31250000000) := by
  apply le_trans (concrete_distance_charge (n := 12616) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (1025207/500000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12616 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (352847856787/500000000000000000)
  k0 := (794287081561293/200000000000000000)
  k6 := (6095506520901593/500000000000000000)
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
  norm_lower := (window_guards (n := 12616) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12616) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((3233449/31250000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12616 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12616) internalParameters :=
  BstLean.Part227.worldPackage (n := 12616) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (3233449/31250000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12616) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world12616.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world12616, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world12616.frame := by
  exact frame.2.trans (by norm_num [Part268.world12616])

theorem moment_payment : internalParameters.moment ≤ Part268.world12616.moment := by
  exact moment.2.trans (by norm_num [Part268.world12616])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1175737543/1000000000000) ∧
    internalParameters.frame ≤ (626775791141/1000000000000) ∧
    internalParameters.moment ≤ (4793216817/500000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12616) (Part268.world12616) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world12616]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world12616])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world12616]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world12616]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12616).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12616).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow12616
namespace BstLean.Part268.WorldRow12617
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
    exp (-((mW 12617 : ℝ)*25234)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12617 : ℝ)*25234)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12617 : ℝ)*25234)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12617 : ℝ)*25234)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 25234 (mW 12617) i /
      (rowEps i * e1MeanBounds 25234 (mW 12617) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 25234 (mW 12617) (1/10^6) (1/10^7) rowEps ≤ (8201/4000000000) := by
  have hr : 0 ≤ firstRatio 25234 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 25234 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 25234) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12617 (1/10^6) (1/10^7) ((8201/4000000000))
      (712/10000) rowEps ≤ (25863383/250000000000) := by
  have hs : statisticsPayment ≤ (243678095409/62500000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (497273402411/5000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12617 (1/10^6) (1/10^7) ((8201/4000000000))
      (712/10000) rowEps =
      exp (-((mW 12617 : ℝ)*25234)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12617 : ℝ)*25234)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12617) (mW 12617)).real
      (goodDist 12617 (712/10000))ᶜ ≤ (25863383/250000000000) := by
  apply le_trans (concrete_distance_charge (n := 12617) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (8201/4000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12617 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (352805908519/500000000000000000)
  k0 := (496399916127349/125000000000000000)
  k6 := (6095264956848913/500000000000000000)
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
  norm_lower := (window_guards (n := 12617) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12617) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((25863383/250000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12617 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12617) internalParameters :=
  BstLean.Part227.worldPackage (n := 12617) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (25863383/250000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12617) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world12617.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world12617, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world12617.frame := by
  exact frame.2.trans (by norm_num [Part268.world12617])

theorem moment_payment : internalParameters.moment ≤ Part268.world12617.moment := by
  exact moment.2.trans (by norm_num [Part268.world12617])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (587846479/500000000000) ∧
    internalParameters.frame ≤ (626761740809/1000000000000) ∧
    internalParameters.moment ≤ (9584447079/1000000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12617) (Part268.world12617) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world12617]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world12617])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world12617]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world12617]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12617).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12617).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow12617
namespace BstLean.Part268.WorldRow12618
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
    exp (-((mW 12618 : ℝ)*25236)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12618 : ℝ)*25236)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12618 : ℝ)*25236)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12618 : ℝ)*25236)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 25236 (mW 12618) i /
      (rowEps i * e1MeanBounds 25236 (mW 12618) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 25236 (mW 12618) (1/10^6) (1/10^7) rowEps ≤ (1025043/500000000000) := by
  have hr : 0 ≤ firstRatio 25236 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 25236 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 25236) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12618 (1/10^6) (1/10^7) ((1025043/500000000000))
      (712/10000) rowEps ≤ (25859173/250000000000) := by
  have hs : statisticsPayment ≤ (3898230793387/1000000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (49719229871497/500000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12618 (1/10^6) (1/10^7) ((1025043/500000000000))
      (712/10000) rowEps =
      exp (-((mW 12618 : ℝ)*25236)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12618 : ℝ)*25236)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12618) (mW 12618)).real
      (goodDist 12618 (712/10000))ᶜ ≤ (25859173/250000000000) := by
  apply le_trans (concrete_distance_charge (n := 12618) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (1025043/500000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12618 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (176381984281/250000000000000000)
  k0 := (1985481641486607/500000000000000000)
  k6 := (1523755855378351/125000000000000000)
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
  norm_lower := (window_guards (n := 12618) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12618) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((25859173/250000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12618 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12618) internalParameters :=
  BstLean.Part227.worldPackage (n := 12618) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (25859173/250000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12618) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world12618.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world12618, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world12618.frame := by
  exact frame.2.trans (by norm_num [Part268.world12618])

theorem moment_payment : internalParameters.moment ≤ Part268.world12618.moment := by
  exact moment.2.trans (by norm_num [Part268.world12618])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (235129677/200000000000) ∧
    internalParameters.frame ≤ (626747692749/1000000000000) ∧
    internalParameters.moment ≤ (4791230549/500000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12618) (Part268.world12618) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world12618]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world12618])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world12618]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world12618]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12618).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12618).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow12618
namespace BstLean.Part268.WorldRow12619
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
    exp (-((mW 12619 : ℝ)*25238)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12619 : ℝ)*25238)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12619 : ℝ)*25238)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12619 : ℝ)*25238)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 25238 (mW 12619) i /
      (rowEps i * e1MeanBounds 25238 (mW 12619) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 25238 (mW 12619) (1/10^6) (1/10^7) rowEps ≤ (2049921/1000000000000) := by
  have hr : 0 ≤ firstRatio 25238 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 25238 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 25238) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12619 (1/10^6) (1/10^7) ((2049921/1000000000000))
      (712/10000) rowEps ≤ (103419567/1000000000000) := by
  have hs : statisticsPayment ≤ (487201530507/125000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (99421953489117/1000000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12619 (1/10^6) (1/10^7) ((2049921/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 12619 : ℝ)*25238)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12619 : ℝ)*25238)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12619) (mW 12619)).real
      (goodDist 12619 (712/10000))ᶜ ≤ (103419567/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 12619) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (2049921/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12619 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (176361018457/250000000000000000)
  k0 := (496340908708039/125000000000000000)
  k6 := (190461934840293/15625000000000000)
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
  norm_lower := (window_guards (n := 12619) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12619) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((103419567/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12619 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12619) internalParameters :=
  BstLean.Part227.worldPackage (n := 12619) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (103419567/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12619) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world12619.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world12619, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world12619.frame := by
  exact frame.2.trans (by norm_num [Part268.world12619])

theorem moment_payment : internalParameters.moment ≤ Part268.world12619.moment := by
  exact moment.2.trans (by norm_num [Part268.world12619])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (73475239/62500000000) ∧
    internalParameters.frame ≤ (626733646961/1000000000000) ∧
    internalParameters.moment ≤ (9580475693/1000000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12619) (Part268.world12619) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world12619]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world12619])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world12619]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world12619]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12619).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12619).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow12619
namespace BstLean.Part268.WorldRow12620
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
    exp (-((mW 12620 : ℝ)*25240)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12620 : ℝ)*25240)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12620 : ℝ)*25240)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12620 : ℝ)*25240)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 25240 (mW 12620) i /
      (rowEps i * e1MeanBounds 25240 (mW 12620) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 25240 (mW 12620) (1/10^6) (1/10^7) rowEps ≤ (2049757/1000000000000) := by
  have hr : 0 ≤ firstRatio 25240 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 25240 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 25240) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12620 (1/10^6) (1/10^7) ((2049757/1000000000000))
      (712/10000) rowEps ≤ (103402721/1000000000000) := by
  have hs : statisticsPayment ≤ (48712423481/12500000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (1988114518201/20000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12620 (1/10^6) (1/10^7) ((2049757/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 12620 : ℝ)*25240)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12620 : ℝ)*25240)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12620) (mW 12620)).real
      (goodDist 12620 (712/10000))ᶜ ≤ (103402721/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 12620) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (2049757/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12620 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (88170028393/125000000000000000)
  k0 := (1985245644540519/500000000000000000)
  k6 := (12189080873942283/1000000000000000000)
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
  norm_lower := (window_guards (n := 12620) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12620) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((103402721/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12620 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12620) internalParameters :=
  BstLean.Part227.worldPackage (n := 12620) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (103402721/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12620) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world12620.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world12620, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world12620.frame := by
  exact frame.2.trans (by norm_num [Part268.world12620])

theorem moment_payment : internalParameters.moment ≤ Part268.world12620.moment := by
  exact moment.2.trans (by norm_num [Part268.world12620])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (587779637/500000000000) ∧
    internalParameters.frame ≤ (156679900861/250000000000) ∧
    internalParameters.moment ≤ (4789245431/500000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12620) (Part268.world12620) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world12620]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world12620])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world12620]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world12620]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12620).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12620).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow12620
namespace BstLean.Part268.WorldRow12621
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
    exp (-((mW 12621 : ℝ)*25242)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12621 : ℝ)*25242)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12621 : ℝ)*25242)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12621 : ℝ)*25242)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 25242 (mW 12621) i /
      (rowEps i * e1MeanBounds 25242 (mW 12621) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 25242 (mW 12621) (1/10^6) (1/10^7) rowEps ≤ (2049593/1000000000000) := by
  have hr : 0 ≤ firstRatio 25242 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 25242 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 25242) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12621 (1/10^6) (1/10^7) ((2049593/1000000000000))
      (712/10000) rowEps ≤ (6461617/62500000000) := by
  have hs : statisticsPayment ≤ (3896375696581/1000000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (24847373725639/250000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12621 (1/10^6) (1/10^7) ((2049593/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 12621 : ℝ)*25242)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12621 : ℝ)*25242)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12621) (mW 12621)).real
      (goodDist 12621 (712/10000))ᶜ ≤ (6461617/62500000000) := by
  apply le_trans (concrete_distance_charge (n := 12621) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (2049593/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12621 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (705276397069/1000000000000000000)
  k0 := (3970255341220783/1000000000000000000)
  k6 := (3047149493876507/250000000000000000)
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
  norm_lower := (window_guards (n := 12621) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12621) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((6461617/62500000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12621 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12621) internalParameters :=
  BstLean.Part227.worldPackage (n := 12621) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (6461617/62500000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12621) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world12621.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world12621, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world12621.frame := by
  exact frame.2.trans (by norm_num [Part268.world12621])

theorem moment_payment : internalParameters.moment ≤ Part268.world12621.moment := by
  exact moment.2.trans (by norm_num [Part268.world12621])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1175514737/1000000000000) ∧
    internalParameters.frame ≤ (626705562197/1000000000000) ∧
    internalParameters.moment ≤ (4788253303/500000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12621) (Part268.world12621) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world12621]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world12621])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world12621]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world12621]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12621).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12621).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow12621
namespace BstLean.Part268.WorldRow12622
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
    exp (-((mW 12622 : ℝ)*25244)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12622 : ℝ)*25244)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12622 : ℝ)*25244)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12622 : ℝ)*25244)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 25244 (mW 12622) i /
      (rowEps i * e1MeanBounds 25244 (mW 12622) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 25244 (mW 12622) (1/10^6) (1/10^7) rowEps ≤ (2049429/1000000000000) := by
  have hr : 0 ≤ firstRatio 25244 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 25244 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 25244) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12622 (1/10^6) (1/10^7) ((2049429/1000000000000))
      (712/10000) rowEps ≤ (5168451/50000000000) := by
  have hs : statisticsPayment ≤ (243484856143/62500000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (49686630234511/500000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12622 (1/10^6) (1/10^7) ((2049429/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 12622 : ℝ)*25244)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12622 : ℝ)*25244)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12622) (mW 12622)).real
      (goodDist 12622 (712/10000))ᶜ ≤ (5168451/50000000000) := by
  apply le_trans (concrete_distance_charge (n := 12622) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (2049429/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12622 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (705192583597/1000000000000000000)
  k0 := (3970019426072491/1000000000000000000)
  k6 := (6094057567229309/500000000000000000)
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
  norm_lower := (window_guards (n := 12622) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12622) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((5168451/50000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12622 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12622) internalParameters :=
  BstLean.Part227.worldPackage (n := 12622) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (5168451/50000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12622) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world12622.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world12622, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world12622.frame := by
  exact frame.2.trans (by norm_num [Part268.world12622])

theorem moment_payment : internalParameters.moment ≤ Part268.world12622.moment := by
  exact moment.2.trans (by norm_num [Part268.world12622])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1175470211/1000000000000) ∧
    internalParameters.frame ≤ (626691523219/1000000000000) ∧
    internalParameters.moment ≤ (2393630731/250000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12622) (Part268.world12622) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world12622]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world12622])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world12622]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world12622]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12622).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12622).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow12622
namespace BstLean.Part268.WorldRow12623
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
    exp (-((mW 12623 : ℝ)*25246)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12623 : ℝ)*25246)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12623 : ℝ)*25246)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12623 : ℝ)*25246)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 25246 (mW 12623) i /
      (rowEps i * e1MeanBounds 25246 (mW 12623) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 25246 (mW 12623) (1/10^6) (1/10^7) rowEps ≤ (409853/200000000000) := by
  have hr : 0 ≤ firstRatio 25246 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 25246 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 25246) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12623 (1/10^6) (1/10^7) ((409853/200000000000))
      (712/10000) rowEps ≤ (25838041/250000000000) := by
  have hs : statisticsPayment ≤ (155805595341/40000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (49678511305917/500000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12623 (1/10^6) (1/10^7) ((409853/200000000000))
      (712/10000) rowEps =
      exp (-((mW 12623 : ℝ)*25246)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12623 : ℝ)*25246)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12623) (mW 12623)).real
      (goodDist 12623 (712/10000))ᶜ ≤ (25838041/250000000000) := by
  apply le_trans (concrete_distance_charge (n := 12623) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (409853/200000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12623 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (176277196681/250000000000000000)
  k0 := (248111471476921/62500000000000000)
  k6 := (12187632350788687/1000000000000000000)
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
  norm_lower := (window_guards (n := 12623) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12623) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((25838041/250000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12623 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12623) internalParameters :=
  BstLean.Part227.worldPackage (n := 12623) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (25838041/250000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12623) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world12623.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world12623, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world12623.frame := by
  exact frame.2.trans (by norm_num [Part268.world12623])

theorem moment_payment : internalParameters.moment ≤ Part268.world12623.moment := by
  exact moment.2.trans (by norm_num [Part268.world12623])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1175425697/1000000000000) ∧
    internalParameters.frame ≤ (626677486511/1000000000000) ∧
    internalParameters.moment ≤ (1196567477/125000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12623) (Part268.world12623) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world12623]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world12623])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world12623]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world12623]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12623).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12623).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow12623
namespace BstLean.Part268.WorldRow12624
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
    exp (-((mW 12624 : ℝ)*25248)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12624 : ℝ)*25248)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12624 : ℝ)*25248)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12624 : ℝ)*25248)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 25248 (mW 12624) i /
      (rowEps i * e1MeanBounds 25248 (mW 12624) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 25248 (mW 12624) (1/10^6) (1/10^7) rowEps ≤ (2049101/1000000000000) := by
  have hr : 0 ≤ firstRatio 25248 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 25248 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 25248) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12624 (1/10^6) (1/10^7) ((2049101/1000000000000))
      (712/10000) rowEps ≤ (20667061/200000000000) := by
  have hs : statisticsPayment ≤ (1947261126109/500000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (49670390666691/500000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12624 (1/10^6) (1/10^7) ((2049101/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 12624 : ℝ)*25248)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12624 : ℝ)*25248)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12624) (mW 12624)).real
      (goodDist 12624 (712/10000))ᶜ ≤ (20667061/200000000000) := by
  apply le_trans (concrete_distance_charge (n := 12624) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (2049101/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12624 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (141005001289/200000000000000000)
  k0 := (3969547693887271/1000000000000000000)
  k6 := (1523393703060609/125000000000000000)
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
  norm_lower := (window_guards (n := 12624) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12624) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((20667061/200000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12624 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12624) internalParameters :=
  BstLean.Part227.worldPackage (n := 12624) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (20667061/200000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12624) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world12624.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world12624, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world12624.frame := by
  exact frame.2.trans (by norm_num [Part268.world12624])

theorem moment_payment : internalParameters.moment ≤ Part268.world12624.moment := by
  exact moment.2.trans (by norm_num [Part268.world12624])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (293845299/250000000000) ∧
    internalParameters.frame ≤ (626663452071/1000000000000) ∧
    internalParameters.moment ≤ (9570557283/1000000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12624) (Part268.world12624) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world12624]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world12624])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world12624]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world12624]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12624).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12624).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow12624
