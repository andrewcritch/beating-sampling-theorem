import BstLean.Part268World13Step5
namespace BstLean.Part268.WorldRow12675
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
    exp (-((mW 12675 : ℝ)*25350)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12675 : ℝ)*25350)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12675 : ℝ)*25350)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12675 : ℝ)*25350)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 25350 (mW 12675) i /
      (rowEps i * e1MeanBounds 25350 (mW 12675) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 25350 (mW 12675) (1/10^6) (1/10^7) rowEps ≤ (204077/100000000000) := by
  have hr : 0 ≤ firstRatio 25350 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 25350 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 25350) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12675 (1/10^6) (1/10^7) ((204077/100000000000))
      (712/10000) rowEps ≤ (4099221/40000000000) := by
  have hs : statisticsPayment ≤ (241454037007/62500000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (19703451816071/200000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12675 (1/10^6) (1/10^7) ((204077/100000000000))
      (712/10000) rowEps =
      exp (-((mW 12675 : ℝ)*25350)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12675 : ℝ)*25350)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12675) (mW 12675)).real
      (goodDist 12675 (712/10000))ᶜ ≤ (4099221/40000000000) := by
  apply le_trans (concrete_distance_charge (n := 12675) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (204077/100000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12675 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (700774109167/1000000000000000000)
  k0 := (98939063758591/25000000000000000)
  k6 := (6081303192631499/500000000000000000)
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
  norm_lower := (window_guards (n := 12675) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12675) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((4099221/40000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12675 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12675) internalParameters :=
  BstLean.Part227.worldPackage (n := 12675) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (4099221/40000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12675) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world12675.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world12675, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world12675.frame := by
  exact frame.2.trans (by norm_num [Part268.world12675])

theorem moment_payment : internalParameters.moment ≤ Part268.world12675.moment := by
  exact moment.2.trans (by norm_num [Part268.world12675])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (586563613/500000000000) ∧
    internalParameters.frame ≤ (312975345019/500000000000) ∧
    internalParameters.moment ≤ (4735102027/500000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12675) (Part268.world12675) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world12675]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world12675])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world12675]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world12675]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12675).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12675).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow12675
namespace BstLean.Part268.WorldRow12676
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
    exp (-((mW 12676 : ℝ)*25352)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12676 : ℝ)*25352)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12676 : ℝ)*25352)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12676 : ℝ)*25352)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 25352 (mW 12676) i /
      (rowEps i * e1MeanBounds 25352 (mW 12676) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 25352 (mW 12676) (1/10^6) (1/10^7) rowEps ≤ (2040607/1000000000000) := by
  have hr : 0 ≤ firstRatio 25352 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 25352 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 25352) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12676 (1/10^6) (1/10^7) ((2040607/1000000000000))
      (712/10000) rowEps ≤ (102463781/1000000000000) := by
  have hs : statisticsPayment ≤ (3862656399203/1000000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (49250561532919/500000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12676 (1/10^6) (1/10^7) ((2040607/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 12676 : ℝ)*25352)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12676 : ℝ)*25352)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12676) (mW 12676)).real
      (goodDist 12676 (712/10000))ᶜ ≤ (102463781/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 12676) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (2040607/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12676 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (350345592749/500000000000000000)
  k0 := (989332097802613/250000000000000000)
  k6 := (1520265828302097/125000000000000000)
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
  norm_lower := (window_guards (n := 12676) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12676) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((102463781/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12676 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12676) internalParameters :=
  BstLean.Part227.worldPackage (n := 12676) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (102463781/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12676) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world12676.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world12676, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world12676.frame := by
  exact frame.2.trans (by norm_num [Part268.world12676])

theorem moment_payment : internalParameters.moment ≤ Part268.world12676.moment := by
  exact moment.2.trans (by norm_num [Part268.world12676])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (146635417/125000000000) ∧
    internalParameters.frame ≤ (15648419319/25000000000) ∧
    internalParameters.moment ≤ (946825107/100000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12676) (Part268.world12676) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world12676]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world12676])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world12676]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world12676]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12676).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12676).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow12676
namespace BstLean.Part268.WorldRow12677
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
    exp (-((mW 12677 : ℝ)*25354)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12677 : ℝ)*25354)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12677 : ℝ)*25354)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12677 : ℝ)*25354)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 25354 (mW 12677) i /
      (rowEps i * e1MeanBounds 25354 (mW 12677) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 25354 (mW 12677) (1/10^6) (1/10^7) rowEps ≤ (510111/250000000000) := by
  have hr : 0 ≤ firstRatio 25354 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 25354 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 25354) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12677 (1/10^6) (1/10^7) ((510111/250000000000))
      (712/10000) rowEps ≤ (51223517/500000000000) := by
  have hs : statisticsPayment ≤ (3862048385871/1000000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (98484983707087/1000000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12677 (1/10^6) (1/10^7) ((510111/250000000000))
      (712/10000) rowEps =
      exp (-((mW 12677 : ℝ)*25354)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12677 : ℝ)*25354)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12677) (mW 12677)).real
      (goodDist 12677 (712/10000))ᶜ ≤ (51223517/500000000000) := by
  apply le_trans (concrete_distance_charge (n := 12677) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (510111/250000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12677 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (700608278181/1000000000000000000)
  k0 := (30914798940623/7812500000000000)
  k6 := (12161646924338911/1000000000000000000)
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
  norm_lower := (window_guards (n := 12677) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12677) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((51223517/500000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12677 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12677) internalParameters :=
  BstLean.Part227.worldPackage (n := 12677) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (51223517/500000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12677) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world12677.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world12677, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world12677.frame := by
  exact frame.2.trans (by norm_num [Part268.world12677])

theorem moment_payment : internalParameters.moment ≤ Part268.world12677.moment := by
  exact moment.2.trans (by norm_num [Part268.world12677])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (36657483/31250000000) ∧
    internalParameters.frame ≤ (625922857719/1000000000000) ∧
    internalParameters.moment ≤ (9466298649/1000000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12677) (Part268.world12677) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world12677]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world12677])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world12677]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world12677]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12677).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12677).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow12677
namespace BstLean.Part268.WorldRow12678
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
    exp (-((mW 12678 : ℝ)*25356)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12678 : ℝ)*25356)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12678 : ℝ)*25356)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12678 : ℝ)*25356)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 25356 (mW 12678) i /
      (rowEps i * e1MeanBounds 25356 (mW 12678) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 25356 (mW 12678) (1/10^6) (1/10^7) rowEps ≤ (1020141/500000000000) := by
  have hr : 0 ≤ firstRatio 25356 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 25356 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 25356) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12678 (1/10^6) (1/10^7) ((1020141/500000000000))
      (712/10000) rowEps ≤ (25607641/250000000000) := by
  have hs : statisticsPayment ≤ (3861440552043/1000000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (98469121657657/1000000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12678 (1/10^6) (1/10^7) ((1020141/500000000000))
      (712/10000) rowEps =
      exp (-((mW 12678 : ℝ)*25356)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12678 : ℝ)*25356)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12678) (mW 12678)).real
      (goodDist 12678 (712/10000))ᶜ ≤ (25607641/250000000000) := by
  apply le_trans (concrete_distance_charge (n := 12678) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (1020141/500000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12678 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (700525387213/1000000000000000000)
  k0 := (1978430084954391/500000000000000000)
  k6 := (12161167279018209/1000000000000000000)
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
  norm_lower := (window_guards (n := 12678) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12678) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((25607641/250000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12678 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12678) internalParameters :=
  BstLean.Part227.worldPackage (n := 12678) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (25607641/250000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12678) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world12678.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world12678, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world12678.frame := by
  exact frame.2.trans (by norm_num [Part268.world12678])

theorem moment_payment : internalParameters.moment ≤ Part268.world12678.moment := by
  exact moment.2.trans (by norm_num [Part268.world12678])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1172995589/1000000000000) ∧
    internalParameters.frame ≤ (125181788983/200000000000) ∧
    internalParameters.moment ≤ (9464346791/1000000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12678) (Part268.world12678) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world12678]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world12678])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world12678]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world12678]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12678).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12678).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow12678
namespace BstLean.Part268.WorldRow12679
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
    exp (-((mW 12679 : ℝ)*25358)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12679 : ℝ)*25358)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12679 : ℝ)*25358)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12679 : ℝ)*25358)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 25358 (mW 12679) i /
      (rowEps i * e1MeanBounds 25358 (mW 12679) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 25358 (mW 12679) (1/10^6) (1/10^7) rowEps ≤ (2040119/1000000000000) := by
  have hr : 0 ≤ firstRatio 25358 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 25358 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 25358) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12679 (1/10^6) (1/10^7) ((2040119/1000000000000))
      (712/10000) rowEps ≤ (10241381/100000000000) := by
  have hs : statisticsPayment ≤ (3860832897647/1000000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (49226487796491/500000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12679 (1/10^6) (1/10^7) ((2040119/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 12679 : ℝ)*25358)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12679 : ℝ)*25358)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12679) (mW 12679)).real
      (goodDist 12679 (712/10000))ᶜ ≤ (10241381/100000000000) := by
  apply le_trans (concrete_distance_charge (n := 12679) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (2040119/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12679 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (700442512589/1000000000000000000)
  k0 := (3956626107729179/1000000000000000000)
  k6 := (6080343845221739/500000000000000000)
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
  norm_lower := (window_guards (n := 12679) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12679) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((10241381/100000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12679 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12679) internalParameters :=
  BstLean.Part227.worldPackage (n := 12679) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (10241381/100000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12679) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world12679.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world12679, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world12679.frame := by
  exact frame.2.trans (by norm_num [Part268.world12679])

theorem moment_payment : internalParameters.moment ≤ Part268.world12679.moment := by
  exact moment.2.trans (by norm_num [Part268.world12679])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1172951733/1000000000000) ∧
    internalParameters.frame ≤ (156473758587/250000000000) ∧
    internalParameters.moment ≤ (1892479099/200000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12679) (Part268.world12679) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world12679]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world12679])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world12679]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world12679]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12679).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12679).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow12679
namespace BstLean.Part268.WorldRow12680
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
    exp (-((mW 12680 : ℝ)*25360)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12680 : ℝ)*25360)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12680 : ℝ)*25360)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12680 : ℝ)*25360)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 25360 (mW 12680) i /
      (rowEps i * e1MeanBounds 25360 (mW 12680) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 25360 (mW 12680) (1/10^6) (1/10^7) rowEps ≤ (509989/250000000000) := by
  have hr : 0 ≤ firstRatio 25360 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 25360 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 25360) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12680 (1/10^6) (1/10^7) ((509989/250000000000))
      (712/10000) rowEps ≤ (102397053/1000000000000) := by
  have hs : statisticsPayment ≤ (386022542261/100000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (98436826191151/1000000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12680 (1/10^6) (1/10^7) ((509989/250000000000))
      (712/10000) rowEps =
      exp (-((mW 12680 : ℝ)*25360)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12680 : ℝ)*25360)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12680) (mW 12680)).real
      (goodDist 12680 (712/10000))ᶜ ≤ (102397053/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 12680) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (509989/250000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12680 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (21886239197/31250000000000000)
  k0 := (989098019463137/250000000000000000)
  k6 := (12160208158603529/1000000000000000000)
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
  norm_lower := (window_guards (n := 12680) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12680) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((102397053/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12680 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12680) internalParameters :=
  BstLean.Part227.worldPackage (n := 12680) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (102397053/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12680) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world12680.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world12680, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world12680.frame := by
  exact frame.2.trans (by norm_num [Part268.world12680])

theorem moment_payment : internalParameters.moment ≤ Part268.world12680.moment := by
  exact moment.2.trans (by norm_num [Part268.world12680])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (73306743/62500000000) ∧
    internalParameters.frame ≤ (312940563009/500000000000) ∧
    internalParameters.moment ≤ (9460444761/1000000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12680) (Part268.world12680) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world12680]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world12680])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world12680]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world12680]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12680).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12680).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow12680
namespace BstLean.Part268.WorldRow12681
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
    exp (-((mW 12681 : ℝ)*25362)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12681 : ℝ)*25362)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12681 : ℝ)*25362)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12681 : ℝ)*25362)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 25362 (mW 12681) i /
      (rowEps i * e1MeanBounds 25362 (mW 12681) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 25362 (mW 12681) (1/10^6) (1/10^7) rowEps ≤ (1019897/500000000000) := by
  have hr : 0 ≤ firstRatio 25362 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 25362 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 25362) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12681 (1/10^6) (1/10^7) ((1019897/500000000000))
      (712/10000) rowEps ≤ (51190287/500000000000) := by
  have hs : statisticsPayment ≤ (1929809063431/500000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (49210477016549/500000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12681 (1/10^6) (1/10^7) ((1019897/500000000000))
      (712/10000) rowEps =
      exp (-((mW 12681 : ℝ)*25362)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12681 : ℝ)*25362)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12681) (mW 12681)).real
      (goodDist 12681 (712/10000))ᶜ ≤ (51190287/500000000000) := by
  apply le_trans (concrete_distance_charge (n := 12681) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (1019897/500000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12681 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (350138406177/500000000000000000)
  k0 := (3956158080273323/1000000000000000000)
  k6 := (6079864341743589/500000000000000000)
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
  norm_lower := (window_guards (n := 12681) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12681) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((51190287/500000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12681 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12681) internalParameters :=
  BstLean.Part227.worldPackage (n := 12681) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (51190287/500000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12681) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world12681.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world12681, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world12681.frame := by
  exact frame.2.trans (by norm_num [Part268.world12681])

theorem moment_payment : internalParameters.moment ≤ Part268.world12681.moment := by
  exact moment.2.trans (by norm_num [Part268.world12681])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (234572811/200000000000) ∧
    internalParameters.frame ≤ (312933609961/500000000000) ∧
    internalParameters.moment ≤ (9458494589/1000000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12681) (Part268.world12681) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world12681]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world12681])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world12681]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world12681]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12681).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12681).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow12681
namespace BstLean.Part268.WorldRow12682
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
    exp (-((mW 12682 : ℝ)*25364)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12682 : ℝ)*25364)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12682 : ℝ)*25364)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12682 : ℝ)*25364)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 25364 (mW 12682) i /
      (rowEps i * e1MeanBounds 25364 (mW 12682) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 25364 (mW 12682) (1/10^6) (1/10^7) rowEps ≤ (2039631/1000000000000) := by
  have hr : 0 ≤ firstRatio 25364 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 25364 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 25364) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12682 (1/10^6) (1/10^7) ((2039631/1000000000000))
      (712/10000) rowEps ≤ (10236381/100000000000) := by
  have hs : statisticsPayment ≤ (3859011010329/1000000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (12300599742429/125000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12682 (1/10^6) (1/10^7) ((2039631/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 12682 : ℝ)*25364)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12682 : ℝ)*25364)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12682) (mW 12682)).real
      (goodDist 12682 (712/10000))ᶜ ≤ (10236381/100000000000) := by
  apply le_trans (concrete_distance_charge (n := 12682) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (2039631/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12682 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (350096993367/500000000000000000)
  k0 := (395592411498311/100000000000000000)
  k6 := (12159249265083243/1000000000000000000)
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
  norm_lower := (window_guards (n := 12682) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12682) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((10236381/100000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12682 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12682) internalParameters :=
  BstLean.Part227.worldPackage (n := 12682) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (10236381/100000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12682) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world12682.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world12682, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world12682.frame := by
  exact frame.2.trans (by norm_num [Part268.world12682])

theorem moment_payment : internalParameters.moment ≤ Part268.world12682.moment := by
  exact moment.2.trans (by norm_num [Part268.world12682])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (586410117/500000000000) ∧
    internalParameters.frame ≤ (312926658031/500000000000) ∧
    internalParameters.moment ≤ (4728272489/500000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12682) (Part268.world12682) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world12682]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world12682])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world12682]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world12682]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12682).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12682).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow12682
namespace BstLean.Part268.WorldRow12683
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
    exp (-((mW 12683 : ℝ)*25366)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12683 : ℝ)*25366)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12683 : ℝ)*25366)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12683 : ℝ)*25366)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 25366 (mW 12683) i /
      (rowEps i * e1MeanBounds 25366 (mW 12683) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 25366 (mW 12683) (1/10^6) (1/10^7) rowEps ≤ (2039469/1000000000000) := by
  have hr : 0 ≤ firstRatio 25366 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 25366 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 25366) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12683 (1/10^6) (1/10^7) ((2039469/1000000000000))
      (712/10000) rowEps ≤ (4093893/40000000000) := by
  have hs : statisticsPayment ≤ (192920203647/50000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (6149307440381/62500000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12683 (1/10^6) (1/10^7) ((2039469/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 12683 : ℝ)*25366)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12683 : ℝ)*25366)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12683) (mW 12683)).real
      (goodDist 12683 (712/10000))ᶜ ≤ (4093893/40000000000) := by
  apply le_trans (concrete_distance_charge (n := 12683) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (2039469/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12683 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (4375694859/6250000000000000)
  k0 := (3955690181976339/1000000000000000000)
  k6 := (189980779740321/15625000000000000)
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
  norm_lower := (window_guards (n := 12683) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12683) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((4093893/40000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12683 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12683) internalParameters :=
  BstLean.Part227.worldPackage (n := 12683) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (4093893/40000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12683) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world12683.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world12683, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world12683.frame := by
  exact frame.2.trans (by norm_num [Part268.world12683])

theorem moment_payment : internalParameters.moment ≤ Part268.world12683.moment := by
  exact moment.2.trans (by norm_num [Part268.world12683])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (46911057/40000000000) ∧
    internalParameters.frame ≤ (156459853609/250000000000) ∧
    internalParameters.moment ≤ (9454595929/1000000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12683) (Part268.world12683) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world12683]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world12683])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world12683]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world12683]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12683).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12683).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow12683
namespace BstLean.Part268.WorldRow12684
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
    exp (-((mW 12684 : ℝ)*25368)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12684 : ℝ)*25368)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12684 : ℝ)*25368)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12684 : ℝ)*25368)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 25368 (mW 12684) i /
      (rowEps i * e1MeanBounds 25368 (mW 12684) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 25368 (mW 12684) (1/10^6) (1/10^7) rowEps ≤ (1019653/500000000000) := by
  have hr : 0 ≤ firstRatio 25368 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 25368 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 25368) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12684 (1/10^6) (1/10^7) ((1019653/500000000000))
      (712/10000) rowEps ≤ (20466111/200000000000) := by
  have hs : statisticsPayment ≤ (3857797314623/1000000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (98372756269981/1000000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12684 (1/10^6) (1/10^7) ((1019653/500000000000))
      (712/10000) rowEps =
      exp (-((mW 12684 : ℝ)*25368)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12684 : ℝ)*25368)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12684) (mW 12684)).real
      (goodDist 12684 (712/10000))ᶜ ≤ (20466111/200000000000) := by
  apply le_trans (concrete_distance_charge (n := 12684) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (1019653/500000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12684 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (700028384467/1000000000000000000)
  k0 := (988864070311153/250000000000000000)
  k6 := (6079145299183953/500000000000000000)
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
  norm_lower := (window_guards (n := 12684) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12684) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((20466111/200000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12684 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12684) internalParameters :=
  BstLean.Part227.worldPackage (n := 12684) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (20466111/200000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12684) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world12684.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world12684, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world12684.frame := by
  exact frame.2.trans (by norm_num [Part268.world12684])

theorem moment_payment : internalParameters.moment ≤ Part268.world12684.moment := by
  exact moment.2.trans (by norm_num [Part268.world12684])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1172732627/1000000000000) ∧
    internalParameters.frame ≤ (625825515043/1000000000000) ∧
    internalParameters.moment ≤ (9452647441/1000000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12684) (Part268.world12684) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world12684]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world12684])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world12684]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world12684]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12684).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12684).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow12684
namespace BstLean.Part268.WorldRow12685
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
    exp (-((mW 12685 : ℝ)*25370)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12685 : ℝ)*25370)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12685 : ℝ)*25370)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12685 : ℝ)*25370)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 25370 (mW 12685) i /
      (rowEps i * e1MeanBounds 25370 (mW 12685) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 25370 (mW 12685) (1/10^6) (1/10^7) rowEps ≤ (254893/125000000000) := by
  have hr : 0 ≤ firstRatio 25370 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 25370 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 25370) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12685 (1/10^6) (1/10^7) ((254893/125000000000))
      (712/10000) rowEps ≤ (102314063/1000000000000) := by
  have hs : statisticsPayment ≤ (771438147061/200000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (98356870650653/1000000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12685 (1/10^6) (1/10^7) ((254893/125000000000))
      (712/10000) rowEps =
      exp (-((mW 12685 : ℝ)*25370)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12685 : ℝ)*25370)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12685) (mW 12685)).real
      (goodDist 12685 (712/10000))ᶜ ≤ (102314063/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 12685) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (254893/125000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12685 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (699945607811/1000000000000000000)
  k0 := (247201400798897/62500000000000000)
  k6 := (2431562270006831/200000000000000000)
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
  norm_lower := (window_guards (n := 12685) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12685) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((102314063/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12685 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12685) internalParameters :=
  BstLean.Part227.worldPackage (n := 12685) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (102314063/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12685) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world12685.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world12685, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world12685.frame := by
  exact frame.2.trans (by norm_num [Part268.world12685])

theorem moment_payment : internalParameters.moment ≤ Part268.world12685.moment := by
  exact moment.2.trans (by norm_num [Part268.world12685])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (29317221/25000000000) ∧
    internalParameters.frame ≤ (156452904471/250000000000) ∧
    internalParameters.moment ≤ (1890139903/200000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12685) (Part268.world12685) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world12685]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world12685])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world12685]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world12685]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12685).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12685).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow12685
namespace BstLean.Part268.WorldRow12686
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
    exp (-((mW 12686 : ℝ)*25372)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12686 : ℝ)*25372)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12686 : ℝ)*25372)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12686 : ℝ)*25372)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 25372 (mW 12686) i /
      (rowEps i * e1MeanBounds 25372 (mW 12686) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 25372 (mW 12686) (1/10^6) (1/10^7) rowEps ≤ (2038981/1000000000000) := by
  have hr : 0 ≤ firstRatio 25372 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 25372 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 25372) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12686 (1/10^6) (1/10^7) ((2038981/1000000000000))
      (712/10000) rowEps ≤ (102297287/1000000000000) := by
  have hs : statisticsPayment ≤ (771316866983/200000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (49170350600741/500000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12686 (1/10^6) (1/10^7) ((2038981/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 12686 : ℝ)*25372)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12686 : ℝ)*25372)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12686) (mW 12686)).real
      (goodDist 12686 (712/10000))ᶜ ≤ (102297287/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 12686) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (2038981/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12686 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (699862847467/1000000000000000000)
  k0 := (1977494288290579/500000000000000000)
  k6 := (6078666079184061/500000000000000000)
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
  norm_lower := (window_guards (n := 12686) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12686) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((102297287/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12686 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12686) internalParameters :=
  BstLean.Part227.worldPackage (n := 12686) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (102297287/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12686) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world12686.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world12686, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world12686.frame := by
  exact frame.2.trans (by norm_num [Part268.world12686])

theorem moment_payment : internalParameters.moment ≤ Part268.world12686.moment := by
  exact moment.2.trans (by norm_num [Part268.world12686])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (586322533/500000000000) ∧
    internalParameters.frame ≤ (312898861479/500000000000) ∧
    internalParameters.moment ≤ (9448752149/1000000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12686) (Part268.world12686) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world12686]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world12686])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world12686]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world12686]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12686).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12686).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow12686
namespace BstLean.Part268.WorldRow12687
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
    exp (-((mW 12687 : ℝ)*25374)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12687 : ℝ)*25374)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12687 : ℝ)*25374)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12687 : ℝ)*25374)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 25374 (mW 12687) i /
      (rowEps i * e1MeanBounds 25374 (mW 12687) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 25374 (mW 12687) (1/10^6) (1/10^7) rowEps ≤ (2038819/1000000000000) := by
  have hr : 0 ≤ firstRatio 25374 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 25374 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 25374) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12687 (1/10^6) (1/10^7) ((2038819/1000000000000))
      (712/10000) rowEps ≤ (25570197/250000000000) := by
  have hs : statisticsPayment ≤ (192798905669/50000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (98324808865459/1000000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12687 (1/10^6) (1/10^7) ((2038819/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 12687 : ℝ)*25374)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12687 : ℝ)*25374)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12687) (mW 12687)).real
      (goodDist 12687 (712/10000))ᶜ ≤ (25570197/250000000000) := by
  apply le_trans (concrete_distance_charge (n := 12687) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (2038819/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12687 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (699780103431/1000000000000000000)
  k0 := (494344346579431/125000000000000000)
  k6 := (151960662791983/12500000000000000)
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
  norm_lower := (window_guards (n := 12687) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12687) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((25570197/250000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12687 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12687) internalParameters :=
  BstLean.Part227.worldPackage (n := 12687) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (25570197/250000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12687) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world12687.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world12687, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world12687.frame := by
  exact frame.2.trans (by norm_num [Part268.world12687])

theorem moment_payment : internalParameters.moment ≤ Part268.world12687.moment := by
  exact moment.2.trans (by norm_num [Part268.world12687])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1172601303/1000000000000) ∧
    internalParameters.frame ≤ (625783830263/1000000000000) ∧
    internalParameters.moment ≤ (295212667/31250000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12687) (Part268.world12687) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world12687]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world12687])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world12687]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world12687]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12687).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12687).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow12687
namespace BstLean.Part268.WorldRow12688
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
    exp (-((mW 12688 : ℝ)*25376)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12688 : ℝ)*25376)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12688 : ℝ)*25376)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12688 : ℝ)*25376)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 25376 (mW 12688) i /
      (rowEps i * e1MeanBounds 25376 (mW 12688) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 25376 (mW 12688) (1/10^6) (1/10^7) rowEps ≤ (2038657/1000000000000) := by
  have hr : 0 ≤ firstRatio 25376 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 25376 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 25376) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12688 (1/10^6) (1/10^7) ((2038657/1000000000000))
      (712/10000) rowEps ≤ (102264287/1000000000000) := by
  have hs : statisticsPayment ≤ (385537207063/100000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (98308913162747/1000000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12688 (1/10^6) (1/10^7) ((2038657/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 12688 : ℝ)*25376)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12688 : ℝ)*25376)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12688) (mW 12688)).real
      (goodDist 12688 (712/10000))ᶜ ≤ (102264287/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 12688) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (2038657/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12688 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (349848687849/500000000000000000)
  k0 := (1977260500468407/500000000000000000)
  k6 := (6078186972497273/500000000000000000)
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
  norm_lower := (window_guards (n := 12688) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12688) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((102264287/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12688 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12688) internalParameters :=
  BstLean.Part227.worldPackage (n := 12688) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (102264287/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12688) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world12688.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world12688, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world12688.frame := by
  exact frame.2.trans (by norm_num [Part268.world12688])

theorem moment_payment : internalParameters.moment ≤ Part268.world12688.moment := by
  exact moment.2.trans (by norm_num [Part268.world12688])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1172557551/1000000000000) ∧
    internalParameters.frame ≤ (3128849699/5000000000) ∧
    internalParameters.moment ≤ (9444859099/1000000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12688) (Part268.world12688) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world12688]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world12688])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world12688]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world12688]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12688).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12688).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow12688
namespace BstLean.Part268.WorldRow12689
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
    exp (-((mW 12689 : ℝ)*25378)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12689 : ℝ)*25378)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12689 : ℝ)*25378)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12689 : ℝ)*25378)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 25378 (mW 12689) i /
      (rowEps i * e1MeanBounds 25378 (mW 12689) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 25378 (mW 12689) (1/10^6) (1/10^7) rowEps ≤ (1019247/500000000000) := by
  have hr : 0 ≤ firstRatio 25378 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 25378 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 25378) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12689 (1/10^6) (1/10^7) ((1019247/500000000000))
      (712/10000) rowEps ≤ (102247501/1000000000000) := by
  have hs : statisticsPayment ≤ (30115360989/7812500000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (98292733709221/1000000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12689 (1/10^6) (1/10^7) ((1019247/500000000000))
      (712/10000) rowEps =
      exp (-((mW 12689 : ℝ)*25378)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12689 : ℝ)*25378)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12689) (mW 12689)).real
      (goodDist 12689 (712/10000))ᶜ ≤ (102247501/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 12689) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (1019247/500000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12689 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (139922932853/200000000000000000)
  k0 := (1977143630741249/500000000000000000)
  k6 := (6077947461632339/500000000000000000)
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
  norm_lower := (window_guards (n := 12689) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12689) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((102247501/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12689 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12689) internalParameters :=
  BstLean.Part227.worldPackage (n := 12689) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (102247501/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12689) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world12689.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world12689, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world12689.frame := by
  exact frame.2.trans (by norm_num [Part268.world12689])

theorem moment_payment : internalParameters.moment ≤ Part268.world12689.moment := by
  exact moment.2.trans (by norm_num [Part268.world12689])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1172513811/1000000000000) ∧
    internalParameters.frame ≤ (39109753223/62500000000) ∧
    internalParameters.moment ≤ (1888582683/200000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12689) (Part268.world12689) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world12689]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world12689])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world12689]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world12689]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12689).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12689).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow12689
namespace BstLean.Part268.WorldRow12690
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
    exp (-((mW 12690 : ℝ)*25380)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12690 : ℝ)*25380)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12690 : ℝ)*25380)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12690 : ℝ)*25380)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 25380 (mW 12690) i /
      (rowEps i * e1MeanBounds 25380 (mW 12690) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 25380 (mW 12690) (1/10^6) (1/10^7) rowEps ≤ (509583/250000000000) := by
  have hr : 0 ≤ firstRatio 25380 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 25380 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 25380) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12690 (1/10^6) (1/10^7) ((509583/250000000000))
      (712/10000) rowEps ≤ (102230993/1000000000000) := by
  have hs : statisticsPayment ≤ (1927080260597/500000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (12284603912969/125000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12690 (1/10^6) (1/10^7) ((509583/250000000000))
      (712/10000) rowEps =
      exp (-((mW 12690 : ℝ)*25380)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12690 : ℝ)*25380)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12690) (mW 12690)).real
      (goodDist 12690 (712/10000))ᶜ ≤ (102230993/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 12690) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (509583/250000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12690 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (5596255753/8000000000000000)
  k0 := (1977026777129217/500000000000000000)
  k6 := (303885398953947/25000000000000000)
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
  norm_lower := (window_guards (n := 12690) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12690) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((102230993/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12690 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12690) internalParameters :=
  BstLean.Part227.worldPackage (n := 12690) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (102230993/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12690) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world12690.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world12690, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world12690.frame := by
  exact frame.2.trans (by norm_num [Part268.world12690])

theorem moment_payment : internalParameters.moment ≤ Part268.world12690.moment := by
  exact moment.2.trans (by norm_num [Part268.world12690])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1172470083/1000000000000) ∧
    internalParameters.frame ≤ (312871082783/500000000000) ∧
    internalParameters.moment ≤ (944096829/100000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12690) (Part268.world12690) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world12690]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world12690])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world12690]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world12690]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12690).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12690).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow12690
namespace BstLean.Part268.WorldRow12691
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
    exp (-((mW 12691 : ℝ)*25382)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12691 : ℝ)*25382)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12691 : ℝ)*25382)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12691 : ℝ)*25382)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 25382 (mW 12691) i /
      (rowEps i * e1MeanBounds 25382 (mW 12691) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 25382 (mW 12691) (1/10^6) (1/10^7) rowEps ≤ (203817/100000000000) := by
  have hr : 0 ≤ firstRatio 25382 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 25382 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 25382) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12691 (1/10^6) (1/10^7) ((203817/100000000000))
      (712/10000) rowEps ≤ (51107241/500000000000) := by
  have hs : statisticsPayment ≤ (963388753591/250000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (98260925538531/1000000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12691 (1/10^6) (1/10^7) ((203817/100000000000))
      (712/10000) rowEps =
      exp (-((mW 12691 : ℝ)*25382)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12691 : ℝ)*25382)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12691) (mW 12691)).real
      (goodDist 12691 (712/10000))ᶜ ≤ (51107241/500000000000) := by
  apply le_trans (concrete_distance_charge (n := 12691) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (203817/100000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12691 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (27977971611/40000000000000000)
  k0 := (1976909939630929/500000000000000000)
  k6 := (12154937049662997/1000000000000000000)
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
  norm_lower := (window_guards (n := 12691) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12691) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((51107241/500000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12691 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12691) internalParameters :=
  BstLean.Part227.worldPackage (n := 12691) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (51107241/500000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12691) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world12691.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world12691, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world12691.frame := by
  exact frame.2.trans (by norm_num [Part268.world12691])

theorem moment_payment : internalParameters.moment ≤ Part268.world12691.moment := by
  exact moment.2.trans (by norm_num [Part268.world12691])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (586213183/500000000000) ∧
    internalParameters.frame ≤ (125145656359/200000000000) ∧
    internalParameters.moment ≤ (377560949/40000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12691) (Part268.world12691) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world12691]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world12691])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world12691]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world12691]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12691).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12691).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow12691
namespace BstLean.Part268.WorldRow12692
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
    exp (-((mW 12692 : ℝ)*25384)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12692 : ℝ)*25384)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12692 : ℝ)*25384)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12692 : ℝ)*25384)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 25384 (mW 12692) i /
      (rowEps i * e1MeanBounds 25384 (mW 12692) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 25384 (mW 12692) (1/10^6) (1/10^7) rowEps ≤ (2038007/1000000000000) := by
  have hr : 0 ≤ firstRatio 25384 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 25384 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 25384) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12692 (1/10^6) (1/10^7) ((2038007/1000000000000))
      (712/10000) rowEps ≤ (102197687/1000000000000) := by
  have hs : statisticsPayment ≤ (240809355377/62500000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (19648947220351/200000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12692 (1/10^6) (1/10^7) ((2038007/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 12692 : ℝ)*25384)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12692 : ℝ)*25384)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12692) (mW 12692)).real
      (goodDist 12692 (712/10000))ᶜ ≤ (102197687/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 12692) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (2038007/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12692 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (699366627711/1000000000000000000)
  k0 := (3953586236487179/1000000000000000000)
  k6 := (6077229098884439/500000000000000000)
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
  norm_lower := (window_guards (n := 12692) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12692) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((102197687/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12692 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12692) internalParameters :=
  BstLean.Part227.worldPackage (n := 12692) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (102197687/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12692) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world12692.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world12692, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world12692.frame := by
  exact frame.2.trans (by norm_num [Part268.world12692])

theorem moment_payment : internalParameters.moment ≤ Part268.world12692.moment := by
  exact moment.2.trans (by norm_num [Part268.world12692])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1172382661/1000000000000) ∧
    internalParameters.frame ≤ (156428600063/250000000000) ∧
    internalParameters.moment ≤ (235926993/25000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12692) (Part268.world12692) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world12692]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world12692])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world12692]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world12692]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12692).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12692).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow12692
namespace BstLean.Part268.WorldRow12693
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
    exp (-((mW 12693 : ℝ)*25386)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12693 : ℝ)*25386)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12693 : ℝ)*25386)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12693 : ℝ)*25386)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 25386 (mW 12693) i /
      (rowEps i * e1MeanBounds 25386 (mW 12693) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 25386 (mW 12693) (1/10^6) (1/10^7) rowEps ≤ (407569/200000000000) := by
  have hr : 0 ≤ firstRatio 25386 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 25386 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 25386) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12693 (1/10^6) (1/10^7) ((407569/200000000000))
      (712/10000) rowEps ≤ (10218117/100000000000) := by
  have hs : statisticsPayment ≤ (963086134031/250000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (9822882364773/100000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12693 (1/10^6) (1/10^7) ((407569/200000000000))
      (712/10000) rowEps =
      exp (-((mW 12693 : ℝ)*25386)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12693 : ℝ)*25386)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12693) (mW 12693)).real
      (goodDist 12693 (712/10000))ᶜ ≤ (10218117/100000000000) := by
  apply le_trans (concrete_distance_charge (n := 12693) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (407569/200000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12693 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (699283981427/1000000000000000000)
  k0 := (3953352625923149/1000000000000000000)
  k6 := (6076989701232187/500000000000000000)
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
  norm_lower := (window_guards (n := 12693) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12693) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((10218117/100000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12693 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12693) internalParameters :=
  BstLean.Part227.worldPackage (n := 12693) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (10218117/100000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12693) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world12693.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world12693, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world12693.frame := by
  exact frame.2.trans (by norm_num [Part268.world12693])

theorem moment_payment : internalParameters.moment ≤ Part268.world12693.moment := by
  exact moment.2.trans (by norm_num [Part268.world12693])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1172338967/1000000000000) ∧
    internalParameters.frame ≤ (312850260469/500000000000) ∧
    internalParameters.moment ≤ (4717568137/500000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12693) (Part268.world12693) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world12693]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world12693])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world12693]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world12693]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12693).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12693).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow12693
namespace BstLean.Part268.WorldRow12694
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
    exp (-((mW 12694 : ℝ)*25388)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12694 : ℝ)*25388)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12694 : ℝ)*25388)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12694 : ℝ)*25388)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 25388 (mW 12694) i /
      (rowEps i * e1MeanBounds 25388 (mW 12694) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 25388 (mW 12694) (1/10^6) (1/10^7) rowEps ≤ (2037683/1000000000000) := by
  have hr : 0 ≤ firstRatio 25388 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 25388 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 25388) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12694 (1/10^6) (1/10^7) ((2037683/1000000000000))
      (712/10000) rowEps ≤ (102164649/1000000000000) := by
  have hs : statisticsPayment ≤ (385173956457/100000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (98212907840897/1000000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12694 (1/10^6) (1/10^7) ((2037683/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 12694 : ℝ)*25388)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12694 : ℝ)*25388)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12694) (mW 12694)).real
      (goodDist 12694 (712/10000))ᶜ ≤ (102164649/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 12694) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (2037683/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12694 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (699201351419/1000000000000000000)
  k0 := (395311904756417/100000000000000000)
  k6 := (607675033186917/50000000000000000)
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
  norm_lower := (window_guards (n := 12694) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12694) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((102164649/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12694 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12694) internalParameters :=
  BstLean.Part227.worldPackage (n := 12694) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (102164649/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12694) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world12694.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world12694, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world12694.frame := by
  exact frame.2.trans (by norm_num [Part268.world12694])

theorem moment_payment : internalParameters.moment ≤ Part268.world12694.moment := by
  exact moment.2.trans (by norm_num [Part268.world12694])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (234459057/200000000000) ∧
    internalParameters.frame ≤ (156421660963/250000000000) ∧
    internalParameters.moment ≤ (2358298347/250000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12694) (Part268.world12694) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world12694]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world12694])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world12694]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world12694]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12694).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12694).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow12694
namespace BstLean.Part268.WorldRow12695
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
    exp (-((mW 12695 : ℝ)*25390)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12695 : ℝ)*25390)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12695 : ℝ)*25390)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12695 : ℝ)*25390)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 25390 (mW 12695) i /
      (rowEps i * e1MeanBounds 25390 (mW 12695) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 25390 (mW 12695) (1/10^6) (1/10^7) rowEps ≤ (2037521/1000000000000) := by
  have hr : 0 ≤ firstRatio 25390 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 25390 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 25390) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12695 (1/10^6) (1/10^7) ((2037521/1000000000000))
      (712/10000) rowEps ≤ (163437/1600000000) := by
  have hs : statisticsPayment ≤ (1925567385649/500000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (19639397736713/200000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12695 (1/10^6) (1/10^7) ((2037521/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 12695 : ℝ)*25390)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12695 : ℝ)*25390)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12695) (mW 12695)).real
      (goodDist 12695 (712/10000))ᶜ ≤ (163437/1600000000) := by
  apply le_trans (concrete_distance_charge (n := 12695) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (2037521/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12695 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (174779684421/250000000000000000)
  k0 := (247055343837967/62500000000000000)
  k6 := (2430604396315927/200000000000000000)
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
  norm_lower := (window_guards (n := 12695) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12695) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((163437/1600000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12695 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12695) internalParameters :=
  BstLean.Part227.worldPackage (n := 12695) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (163437/1600000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12695) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world12695.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world12695, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world12695.frame := by
  exact frame.2.trans (by norm_num [Part268.world12695])

theorem moment_payment : internalParameters.moment ≤ Part268.world12695.moment := by
  exact moment.2.trans (by norm_num [Part268.world12695])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (234450323/200000000000) ∧
    internalParameters.frame ≤ (625672768993/1000000000000) ∧
    internalParameters.moment ≤ (471562553/50000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12695) (Part268.world12695) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world12695]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world12695])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world12695]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world12695]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12695).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12695).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow12695
namespace BstLean.Part268.WorldRow12696
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
    exp (-((mW 12696 : ℝ)*25392)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12696 : ℝ)*25392)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12696 : ℝ)*25392)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12696 : ℝ)*25392)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 25392 (mW 12696) i /
      (rowEps i * e1MeanBounds 25392 (mW 12696) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 25392 (mW 12696) (1/10^6) (1/10^7) rowEps ≤ (2037359/1000000000000) := by
  have hr : 0 ≤ firstRatio 25392 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 25392 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 25392) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12696 (1/10^6) (1/10^7) ((2037359/1000000000000))
      (712/10000) rowEps ≤ (51065799/500000000000) := by
  have hs : statisticsPayment ≤ (962632539059/250000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (98181066178043/1000000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12696 (1/10^6) (1/10^7) ((2037359/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 12696 : ℝ)*25392)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12696 : ℝ)*25392)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12696) (mW 12696)).real
      (goodDist 12696 (712/10000))ᶜ ≤ (51065799/500000000000) := by
  apply le_trans (concrete_distance_charge (n := 12696) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (2037359/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12696 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (87379517527/125000000000000000)
  k0 := (3952651987441799/1000000000000000000)
  k6 := (6076271677988559/500000000000000000)
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
  norm_lower := (window_guards (n := 12696) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12696) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((51065799/500000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12696 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12696) internalParameters :=
  BstLean.Part227.worldPackage (n := 12696) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (51065799/500000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12696) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world12696.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world12696, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world12696.frame := by
  exact frame.2.trans (by norm_num [Part268.world12696])

theorem moment_payment : internalParameters.moment ≤ Part268.world12696.moment := by
  exact moment.2.trans (by norm_num [Part268.world12696])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (293051989/250000000000) ∧
    internalParameters.frame ≤ (312829448181/500000000000) ∧
    internalParameters.moment ≤ (2357327323/250000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12696) (Part268.world12696) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world12696]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world12696])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world12696]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world12696]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12696).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12696).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow12696
namespace BstLean.Part268.WorldRow12697
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
    exp (-((mW 12697 : ℝ)*25394)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12697 : ℝ)*25394)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12697 : ℝ)*25394)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12697 : ℝ)*25394)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 25394 (mW 12697) i /
      (rowEps i * e1MeanBounds 25394 (mW 12697) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 25394 (mW 12697) (1/10^6) (1/10^7) rowEps ≤ (2037197/1000000000000) := by
  have hr : 0 ≤ firstRatio 25394 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 25394 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 25394) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12697 (1/10^6) (1/10^7) ((2037197/1000000000000))
      (712/10000) rowEps ≤ (25528767/250000000000) := by
  have hs : statisticsPayment ≤ (3849925719313/1000000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (98165140326641/1000000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12697 (1/10^6) (1/10^7) ((2037197/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 12697 : ℝ)*25394)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12697 : ℝ)*25394)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12697) (mW 12697)).real
      (goodDist 12697 (712/10000))ᶜ ≤ (25528767/250000000000) := by
  apply le_trans (concrete_distance_charge (n := 12697) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (2037197/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12697 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (69895355901/100000000000000000)
  k0 := (3952418505658719/1000000000000000000)
  k6 := (2430412957383931/200000000000000000)
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
  norm_lower := (window_guards (n := 12697) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12697) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((25528767/250000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12697 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12697) internalParameters :=
  BstLean.Part227.worldPackage (n := 12697) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (25528767/250000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12697) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world12697.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world12697, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world12697.frame := by
  exact frame.2.trans (by norm_num [Part268.world12697])

theorem moment_payment : internalParameters.moment ≤ Part268.world12697.moment := by
  exact moment.2.trans (by norm_num [Part268.world12697])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1172164309/1000000000000) ∧
    internalParameters.frame ≤ (156411256489/250000000000) ∧
    internalParameters.moment ≤ (4713684041/500000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12697) (Part268.world12697) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world12697]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world12697])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world12697]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world12697]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12697).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12697).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow12697
namespace BstLean.Part268.WorldRow12698
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
    exp (-((mW 12698 : ℝ)*25396)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12698 : ℝ)*25396)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12698 : ℝ)*25396)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12698 : ℝ)*25396)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 25396 (mW 12698) i /
      (rowEps i * e1MeanBounds 25396 (mW 12698) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 25396 (mW 12698) (1/10^6) (1/10^7) rowEps ≤ (1018517/500000000000) := by
  have hr : 0 ≤ firstRatio 25396 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 25396 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 25396) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12698 (1/10^6) (1/10^7) ((1018517/500000000000))
      (712/10000) rowEps ≤ (51049127/500000000000) := by
  have hs : statisticsPayment ≤ (481165182557/125000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (24537232740439/250000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12698 (1/10^6) (1/10^7) ((1018517/500000000000))
      (712/10000) rowEps =
      exp (-((mW 12698 : ℝ)*25396)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12698 : ℝ)*25396)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12698) (mW 12698)).real
      (goodDist 12698 (712/10000))ᶜ ≤ (51049127/500000000000) := by
  apply le_trans (concrete_distance_charge (n := 12698) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (1018517/500000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12698 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (698870994063/1000000000000000000)
  k0 := (1976092528027727/500000000000000000)
  k6 := (12151586274396113/1000000000000000000)
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
  norm_lower := (window_guards (n := 12698) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12698) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((51049127/500000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12698 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12698) internalParameters :=
  BstLean.Part227.worldPackage (n := 12698) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (51049127/500000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12698) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world12698.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world12698, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world12698.frame := by
  exact frame.2.trans (by norm_num [Part268.world12698])

theorem moment_payment : internalParameters.moment ≤ Part268.world12698.moment := by
  exact moment.2.trans (by norm_num [Part268.world12698])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1172120673/1000000000000) ∧
    internalParameters.frame ≤ (625631157777/1000000000000) ∧
    internalParameters.moment ≤ (942542743/100000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12698) (Part268.world12698) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world12698]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world12698])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world12698]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world12698]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12698).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12698).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow12698
namespace BstLean.Part268.WorldRow12699
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
    exp (-((mW 12699 : ℝ)*25398)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12699 : ℝ)*25398)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12699 : ℝ)*25398)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12699 : ℝ)*25398)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 25398 (mW 12699) i /
      (rowEps i * e1MeanBounds 25398 (mW 12699) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 25398 (mW 12699) (1/10^6) (1/10^7) rowEps ≤ (254609/125000000000) := by
  have hr : 0 ≤ firstRatio 25398 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 25398 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 25398) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12699 (1/10^6) (1/10^7) ((254609/125000000000))
      (712/10000) rowEps ≤ (102081717/1000000000000) := by
  have hs : statisticsPayment ≤ (962179344899/250000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (98132998449463/1000000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12699 (1/10^6) (1/10^7) ((254609/125000000000))
      (712/10000) rowEps =
      exp (-((mW 12699 : ℝ)*25398)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12699 : ℝ)*25398)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12699) (mW 12699)).real
      (goodDist 12699 (712/10000))ᶜ ≤ (102081717/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 12699) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (254609/125000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12699 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (69878844537/100000000000000000)
  k0 := (246996977413973/62500000000000000)
  k6 := (75944423864971/6250000000000000)
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
  norm_lower := (window_guards (n := 12699) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12699) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((102081717/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12699 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12699) internalParameters :=
  BstLean.Part227.worldPackage (n := 12699) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (102081717/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12699) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part268.world12699.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part268.world12699, width]

theorem frame_payment : internalParameters.frame ≤ Part268.world12699.frame := by
  exact frame.2.trans (by norm_num [Part268.world12699])

theorem moment_payment : internalParameters.moment ≤ Part268.world12699.moment := by
  exact moment.2.trans (by norm_num [Part268.world12699])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1172077049/1000000000000) ∧
    internalParameters.frame ≤ (625617291823/1000000000000) ∧
    internalParameters.moment ≤ (1177935917/125000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12699) (Part268.world12699) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part268.world12699]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part268.world12699])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part268.world12699]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part268.world12699]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12699).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12699).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part268.WorldRow12699
