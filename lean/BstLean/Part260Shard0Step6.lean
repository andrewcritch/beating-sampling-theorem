import BstLean.Part260Shard0Step5
#eval (do IO.println s!"P260 START 12225 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12225
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
    e1MeanBound 24450 (mW 12225) (1/10^6) (1/10^7) rowEps ≤ (1058357/500000000000) := by
  have hr : 0 ≤ firstRatio 24450 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24450 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24450) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12225 (1/10^6) (1/10^7) ((1058357/500000000000))
      (712/10000) rowEps ≤ (690093/6250000000) := by
  have hs : statisticsPayment ≤ (1039085868153/250000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (21231707079279/200000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12225 (1/10^6) (1/10^7) ((1058357/500000000000))
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
      (goodDist 12225 (712/10000))ᶜ ≤ (690093/6250000000) := by
  apply le_trans (concrete_distance_charge (n := 12225) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (1058357/500000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12225 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (184955268567/250000000000000000)
  k0 := (4066325246446699/1000000000000000000)
  k6 := (12384435115451749/1000000000000000000)
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
  norm_lower := (window_guards (n := 12225) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12225) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((690093/6250000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12225 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12225) internalParameters :=
  BstLean.Part227.worldPackage (n := 12225) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (690093/6250000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12225) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12225.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12225, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12225.frame := by
  exact frame.2.trans (by norm_num [Part259.world12225])

theorem moment_payment : internalParameters.moment ≤ Part259.world12225.moment := by
  exact moment.2.trans (by norm_num [Part259.world12225])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1194124331/1000000000000) ∧
    internalParameters.frame ≤ (316224842567/500000000000) ∧
    internalParameters.moment ≤ (5204750099/500000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12225) (Part259.world12225) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12225]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12225])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12225]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12225]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12225).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12225).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12225
#eval (do IO.println s!"P260 END 12225 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12227 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12227
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
    exp (-((mW 12227 : ℝ)*24454)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12227 : ℝ)*24454)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12227 : ℝ)*24454)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12227 : ℝ)*24454)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24454 (mW 12227) i /
      (rowEps i * e1MeanBounds 24454 (mW 12227) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24454 (mW 12227) (1/10^6) (1/10^7) rowEps ≤ (529091/250000000000) := by
  have hr : 0 ≤ firstRatio 24454 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24454 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24454) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12227 (1/10^6) (1/10^7) ((529091/250000000000))
      (712/10000) rowEps ≤ (110377593/1000000000000) := by
  have hs : statisticsPayment ≤ (4154949856959/1000000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (2653066052811/25000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12227 (1/10^6) (1/10^7) ((529091/250000000000))
      (712/10000) rowEps =
      exp (-((mW 12227 : ℝ)*24454)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12227 : ℝ)*24454)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12227) (mW 12227)).real
      (goodDist 12227 (712/10000))ᶜ ≤ (110377593/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 12227) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (529091/250000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12227 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (184909890051/250000000000000000)
  k0 := (4065826382244993/1000000000000000000)
  k6 := (96745485921931/7812500000000000)
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
  norm_lower := (window_guards (n := 12227) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12227) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((110377593/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12227 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12227) internalParameters :=
  BstLean.Part227.worldPackage (n := 12227) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (110377593/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12227) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12227.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12227, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12227.frame := by
  exact frame.2.trans (by norm_num [Part259.world12227])

theorem moment_payment : internalParameters.moment ≤ Part259.world12227.moment := by
  exact moment.2.trans (by norm_num [Part259.world12227])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1194025209/1000000000000) ∧
    internalParameters.frame ≤ (316209858049/500000000000) ∧
    internalParameters.moment ≤ (10405043171/1000000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12227) (Part259.world12227) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12227]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12227])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12227]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12227]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12227).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12227).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12227
#eval (do IO.println s!"P260 END 12227 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12228 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12228
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
    exp (-((mW 12228 : ℝ)*24456)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12228 : ℝ)*24456)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12228 : ℝ)*24456)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12228 : ℝ)*24456)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24456 (mW 12228) i /
      (rowEps i * e1MeanBounds 24456 (mW 12228) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24456 (mW 12228) (1/10^6) (1/10^7) rowEps ≤ (2116189/1000000000000) := by
  have hr : 0 ≤ firstRatio 24456 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24456 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24456) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12228 (1/10^6) (1/10^7) ((2116189/1000000000000))
      (712/10000) rowEps ≤ (3448717/31250000000) := by
  have hs : statisticsPayment ≤ (4154253373111/1000000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (53052344812229/500000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12228 (1/10^6) (1/10^7) ((2116189/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 12228 : ℝ)*24456)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12228 : ℝ)*24456)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12228) (mW 12228)).real
      (goodDist 12228 (712/10000))ᶜ ≤ (3448717/31250000000) := by
  apply le_trans (concrete_distance_charge (n := 12228) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (2116189/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12228 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (184887207751/250000000000000000)
  k0 := (4065577003690793/1000000000000000000)
  k6 := (12382915832477811/1000000000000000000)
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
  norm_lower := (window_guards (n := 12228) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12228) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((3448717/31250000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12228 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12228) internalParameters :=
  BstLean.Part227.worldPackage (n := 12228) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (3448717/31250000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12228) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12228.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12228, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12228.frame := by
  exact frame.2.trans (by norm_num [Part259.world12228])

theorem moment_payment : internalParameters.moment ≤ Part259.world12228.moment := by
  exact moment.2.trans (by norm_num [Part259.world12228])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1193975669/1000000000000) ∧
    internalParameters.frame ≤ (158101183839/250000000000) ∧
    internalParameters.moment ≤ (5201407829/500000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12228) (Part259.world12228) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12228]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12228])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12228]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12228]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12228).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12228).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12228
#eval (do IO.println s!"P260 END 12228 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12229 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12229
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
    exp (-((mW 12229 : ℝ)*24458)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12229 : ℝ)*24458)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12229 : ℝ)*24458)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12229 : ℝ)*24458)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24458 (mW 12229) i /
      (rowEps i * e1MeanBounds 24458 (mW 12229) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24458 (mW 12229) (1/10^6) (1/10^7) rowEps ≤ (1058007/500000000000) := by
  have hr : 0 ≤ firstRatio 24458 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24458 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24458) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12229 (1/10^6) (1/10^7) ((1058007/500000000000))
      (712/10000) rowEps ≤ (27585073/250000000000) := by
  have hs : statisticsPayment ≤ (4153557105127/1000000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (53043366621453/500000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12229 (1/10^6) (1/10^7) ((1058007/500000000000))
      (712/10000) rowEps =
      exp (-((mW 12229 : ℝ)*24458)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12229 : ℝ)*24458)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12229) (mW 12229)).real
      (goodDist 12229 (712/10000))ᶜ ≤ (27585073/250000000000) := by
  apply le_trans (concrete_distance_charge (n := 12229) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (1058007/500000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12229 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (23108066261/31250000000000000)
  k0 := (1016331915206199/250000000000000000)
  k6 := (6191204764530071/500000000000000000)
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
  norm_lower := (window_guards (n := 12229) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12229) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((27585073/250000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12229 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12229) internalParameters :=
  BstLean.Part227.worldPackage (n := 12229) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (27585073/250000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12229) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12229.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12229, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12229.frame := by
  exact frame.2.trans (by norm_num [Part259.world12229])

theorem moment_payment : internalParameters.moment ≤ Part259.world12229.moment := by
  exact moment.2.trans (by norm_num [Part259.world12229])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1193926143/1000000000000) ∧
    internalParameters.frame ≤ (632389757131/1000000000000) ∧
    internalParameters.moment ≤ (1040058881/100000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12229) (Part259.world12229) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12229]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12229])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12229]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12229]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12229).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12229).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12229
#eval (do IO.println s!"P260 END 12229 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12230 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12230
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
    exp (-((mW 12230 : ℝ)*24460)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12230 : ℝ)*24460)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12230 : ℝ)*24460)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12230 : ℝ)*24460)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24460 (mW 12230) i /
      (rowEps i * e1MeanBounds 24460 (mW 12230) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24460 (mW 12230) (1/10^6) (1/10^7) rowEps ≤ (2115839/1000000000000) := by
  have hr : 0 ≤ firstRatio 24460 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24460 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24460) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12230 (1/10^6) (1/10^7) ((2115839/1000000000000))
      (712/10000) rowEps ≤ (27580409/250000000000) := by
  have hs : statisticsPayment ≤ (4152861052917/1000000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (10606877297061/100000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12230 (1/10^6) (1/10^7) ((2115839/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 12230 : ℝ)*24460)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12230 : ℝ)*24460)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12230) (mW 12230)).real
      (goodDist 12230 (712/10000))ᶜ ≤ (27580409/250000000000) := by
  apply le_trans (concrete_distance_charge (n := 12230) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (2115839/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12230 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (369683714121/500000000000000000)
  k0 := (2032539176818537/500000000000000000)
  k6 := (12381903287741463/1000000000000000000)
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
  norm_lower := (window_guards (n := 12230) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12230) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((27580409/250000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12230 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12230) internalParameters :=
  BstLean.Part227.worldPackage (n := 12230) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (27580409/250000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12230) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12230.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12230, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12230.frame := by
  exact frame.2.trans (by norm_num [Part259.world12230])

theorem moment_payment : internalParameters.moment ≤ Part259.world12230.moment := by
  exact moment.2.trans (by norm_num [Part259.world12230])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (119387663/100000000000) ∧
    internalParameters.frame ≤ (316187390711/500000000000) ∧
    internalParameters.moment ≤ (10398362629/1000000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12230) (Part259.world12230) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12230]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12230])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12230]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12230]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12230).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12230).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12230
#eval (do IO.println s!"P260 END 12230 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12231 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12231
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
    exp (-((mW 12231 : ℝ)*24462)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12231 : ℝ)*24462)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12231 : ℝ)*24462)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12231 : ℝ)*24462)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24462 (mW 12231) i /
      (rowEps i * e1MeanBounds 24462 (mW 12231) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24462 (mW 12231) (1/10^6) (1/10^7) rowEps ≤ (423133/200000000000) := by
  have hr : 0 ≤ firstRatio 24462 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24462 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24462) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12231 (1/10^6) (1/10^7) ((423133/200000000000))
      (712/10000) rowEps ≤ (110303267/1000000000000) := by
  have hs : statisticsPayment ≤ (415216521639/100000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (106051100678763/1000000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12231 (1/10^6) (1/10^7) ((423133/200000000000))
      (712/10000) rowEps =
      exp (-((mW 12231 : ℝ)*24462)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12231 : ℝ)*24462)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12231) (mW 12231)).real
      (goodDist 12231 (712/10000))ᶜ ≤ (110303267/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 12231) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (423133/200000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12231 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (739276754669/1000000000000000000)
  k0 := (4064829082120447/1000000000000000000)
  k6 := (12381397108509081/1000000000000000000)
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
  norm_lower := (window_guards (n := 12231) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12231) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((110303267/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12231 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12231) internalParameters :=
  BstLean.Part227.worldPackage (n := 12231) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (110303267/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12231) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12231.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12231, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12231.frame := by
  exact frame.2.trans (by norm_num [Part259.world12231])

theorem moment_payment : internalParameters.moment ≤ Part259.world12231.moment := by
  exact moment.2.trans (by norm_num [Part259.world12231])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1193827131/1000000000000) ∧
    internalParameters.frame ≤ (158089952057/250000000000) ∧
    internalParameters.moment ≤ (10396137113/1000000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12231) (Part259.world12231) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12231]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12231])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12231]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12231]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12231).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12231).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12231
#eval (do IO.println s!"P260 END 12231 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12232 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12232
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
    exp (-((mW 12232 : ℝ)*24464)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12232 : ℝ)*24464)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12232 : ℝ)*24464)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12232 : ℝ)*24464)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24464 (mW 12232) i /
      (rowEps i * e1MeanBounds 24464 (mW 12232) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24464 (mW 12232) (1/10^6) (1/10^7) rowEps ≤ (211549/100000000000) := by
  have hr : 0 ≤ firstRatio 24464 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24464 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24464) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12232 (1/10^6) (1/10^7) ((211549/100000000000))
      (712/10000) rowEps ≤ (27571151/250000000000) := by
  have hs : statisticsPayment ≤ (4151469595457/1000000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (26508283151803/250000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12232 (1/10^6) (1/10^7) ((211549/100000000000))
      (712/10000) rowEps =
      exp (-((mW 12232 : ℝ)*24464)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12232 : ℝ)*24464)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12232) (mW 12232)).real
      (goodDist 12232 (712/10000))ᶜ ≤ (27571151/250000000000) := by
  apply le_trans (concrete_distance_charge (n := 12232) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (211549/100000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12232 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (739186099627/1000000000000000000)
  k0 := (4064579846264981/1000000000000000000)
  k6 := (6190445495675153/500000000000000000)
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
  norm_lower := (window_guards (n := 12232) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12232) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((27571151/250000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12232 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12232) internalParameters :=
  BstLean.Part227.worldPackage (n := 12232) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (27571151/250000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12232) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12232.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12232, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12232.frame := by
  exact frame.2.trans (by norm_num [Part259.world12232])

theorem moment_payment : internalParameters.moment ≤ Part259.world12232.moment := by
  exact moment.2.trans (by norm_num [Part259.world12232])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (238755529/200000000000) ∧
    internalParameters.frame ≤ (158086209387/250000000000) ∧
    internalParameters.moment ≤ (10393912263/1000000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12232) (Part259.world12232) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12232]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12232])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12232]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12232]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12232).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12232).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12232
#eval (do IO.println s!"P260 END 12232 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12233 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12233
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
    exp (-((mW 12233 : ℝ)*24466)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12233 : ℝ)*24466)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12233 : ℝ)*24466)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12233 : ℝ)*24466)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24466 (mW 12233) i /
      (rowEps i * e1MeanBounds 24466 (mW 12233) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24466 (mW 12233) (1/10^6) (1/10^7) rowEps ≤ (423063/200000000000) := by
  have hr : 0 ≤ firstRatio 24466 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24466 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24466) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12233 (1/10^6) (1/10^7) ((423063/200000000000))
      (712/10000) rowEps ≤ (6891621/62500000000) := by
  have hs : statisticsPayment ≤ (2075387095013/500000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (848121285227/8000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12233 (1/10^6) (1/10^7) ((423063/200000000000))
      (712/10000) rowEps =
      exp (-((mW 12233 : ℝ)*24466)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12233 : ℝ)*24466)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12233) (mW 12233)).real
      (goodDist 12233 (712/10000))ᶜ ≤ (6891621/62500000000) := by
  apply le_trans (concrete_distance_charge (n := 12233) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (423063/200000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12233 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (92386932889/125000000000000000)
  k0 := (2032165323033119/500000000000000000)
  k6 := (12380384936252453/1000000000000000000)
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
  norm_lower := (window_guards (n := 12233) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12233) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((6891621/62500000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12233 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12233) internalParameters :=
  BstLean.Part227.worldPackage (n := 12233) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (6891621/62500000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12233) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12233.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12233, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12233.frame := by
  exact frame.2.trans (by norm_num [Part259.world12233])

theorem moment_payment : internalParameters.moment ≤ Part259.world12233.moment := by
  exact moment.2.trans (by norm_num [Part259.world12233])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1193728173/1000000000000) ∧
    internalParameters.frame ≤ (632329869383/1000000000000) ∧
    internalParameters.moment ≤ (5195844039/500000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12233) (Part259.world12233) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12233]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12233])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12233]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12233]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12233).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12233).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12233
#eval (do IO.println s!"P260 END 12233 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12234 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12234
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
    exp (-((mW 12234 : ℝ)*24468)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12234 : ℝ)*24468)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12234 : ℝ)*24468)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12234 : ℝ)*24468)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24468 (mW 12234) i /
      (rowEps i * e1MeanBounds 24468 (mW 12234) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24468 (mW 12234) (1/10^6) (1/10^7) rowEps ≤ (105757/50000000000) := by
  have hr : 0 ≤ firstRatio 24468 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24468 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24468) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12234 (1/10^6) (1/10^7) ((105757/50000000000))
      (712/10000) rowEps ≤ (22049453/200000000000) := by
  have hs : statisticsPayment ≤ (4150079000007/1000000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (26499296205021/250000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12234 (1/10^6) (1/10^7) ((105757/50000000000))
      (712/10000) rowEps =
      exp (-((mW 12234 : ℝ)*24468)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12234 : ℝ)*24468)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12234) (mW 12234)).real
      (goodDist 12234 (712/10000))ᶜ ≤ (22049453/200000000000) := by
  apply le_trans (concrete_distance_charge (n := 12234) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (105757/50000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12234 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (369502422559/500000000000000000)
  k0 := (101602037037857/25000000000000000)
  k6 := (12379878943202839/1000000000000000000)
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
  norm_lower := (window_guards (n := 12234) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12234) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((22049453/200000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12234 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12234) internalParameters :=
  BstLean.Part227.worldPackage (n := 12234) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (22049453/200000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12234) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12234.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12234, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12234.frame := by
  exact frame.2.trans (by norm_num [Part259.world12234])

theorem moment_payment : internalParameters.moment ≤ Part259.world12234.moment := by
  exact moment.2.trans (by norm_num [Part259.world12234])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (238735743/200000000000) ∧
    internalParameters.frame ≤ (632314903731/1000000000000) ∧
    internalParameters.moment ≤ (5194732279/500000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12234) (Part259.world12234) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12234]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12234])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12234]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12234]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12234).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12234).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12234
#eval (do IO.println s!"P260 END 12234 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12235 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12235
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
    exp (-((mW 12235 : ℝ)*24470)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12235 : ℝ)*24470)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12235 : ℝ)*24470)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12235 : ℝ)*24470)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24470 (mW 12235) i /
      (rowEps i * e1MeanBounds 24470 (mW 12235) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24470 (mW 12235) (1/10^6) (1/10^7) rowEps ≤ (422993/200000000000) := by
  have hr : 0 ≤ firstRatio 24470 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24470 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24470) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12235 (1/10^6) (1/10^7) ((422993/200000000000))
      (712/10000) rowEps ≤ (110228591/1000000000000) := by
  have hs : statisticsPayment ≤ (4149384025311/1000000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (10597920511017/100000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12235 (1/10^6) (1/10^7) ((422993/200000000000))
      (712/10000) rowEps =
      exp (-((mW 12235 : ℝ)*24470)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12235 : ℝ)*24470)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12235) (mW 12235)).real
      (goodDist 12235 (712/10000))ᶜ ≤ (110228591/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 12235) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (422993/200000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12235 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (18472856141/25000000000000000)
  k0 := (2031916176300957/500000000000000000)
  k6 := (6189686506094393/500000000000000000)
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
  norm_lower := (window_guards (n := 12235) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12235) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((110228591/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12235 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12235) internalParameters :=
  BstLean.Part227.worldPackage (n := 12235) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (110228591/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12235) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12235.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12235, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12235.frame := by
  exact frame.2.trans (by norm_num [Part259.world12235])

theorem moment_payment : internalParameters.moment ≤ Part259.world12235.moment := by
  exact moment.2.trans (by norm_num [Part259.world12235])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (119362927/100000000000) ∧
    internalParameters.frame ≤ (39518746287/62500000000) ∧
    internalParameters.moment ≤ (5193620851/500000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12235) (Part259.world12235) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12235]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12235])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12235]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12235]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12235).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12235).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12235
#eval (do IO.println s!"P260 END 12235 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12236 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12236
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
    exp (-((mW 12236 : ℝ)*24472)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12236 : ℝ)*24472)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12236 : ℝ)*24472)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12236 : ℝ)*24472)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24472 (mW 12236) i /
      (rowEps i * e1MeanBounds 24472 (mW 12236) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24472 (mW 12236) (1/10^6) (1/10^7) rowEps ≤ (211479/100000000000) := by
  have hr : 0 ≤ firstRatio 24472 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24472 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24472) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12236 (1/10^6) (1/10^7) ((211479/100000000000))
      (712/10000) rowEps ≤ (13776239/125000000000) := by
  have hs : statisticsPayment ≤ (2074344632923/500000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (26490305381617/250000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12236 (1/10^6) (1/10^7) ((211479/100000000000))
      (712/10000) rowEps =
      exp (-((mW 12236 : ℝ)*24472)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12236 : ℝ)*24472)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12236) (mW 12236)).real
      (goodDist 12236 (712/10000))ᶜ ≤ (13776239/125000000000) := by
  apply le_trans (concrete_distance_charge (n := 12236) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (211479/100000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12236 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (23088239521/31250000000000000)
  k0 := (2031791629659597/500000000000000000)
  k6 := (12378867143197619/1000000000000000000)
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
  norm_lower := (window_guards (n := 12236) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12236) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((13776239/125000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12236 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12236) internalParameters :=
  BstLean.Part227.worldPackage (n := 12236) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (13776239/125000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12236) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12236.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12236, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12236.frame := by
  exact frame.2.trans (by norm_num [Part259.world12236])

theorem moment_payment : internalParameters.moment ≤ Part259.world12236.moment := by
  exact moment.2.trans (by norm_num [Part259.world12236])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1193579839/1000000000000) ∧
    internalParameters.frame ≤ (158071244991/250000000000) ∧
    internalParameters.moment ≤ (10385019511/1000000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12236) (Part259.world12236) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12236]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12236])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12236]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12236]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12236).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12236).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12236
#eval (do IO.println s!"P260 END 12236 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12237 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12237
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
    exp (-((mW 12237 : ℝ)*24474)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12237 : ℝ)*24474)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12237 : ℝ)*24474)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12237 : ℝ)*24474)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24474 (mW 12237) i /
      (rowEps i * e1MeanBounds 24474 (mW 12237) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24474 (mW 12237) (1/10^6) (1/10^7) rowEps ≤ (264327/125000000000) := by
  have hr : 0 ≤ firstRatio 24474 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24474 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24474) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12237 (1/10^6) (1/10^7) ((264327/125000000000))
      (712/10000) rowEps ≤ (55095761/500000000000) := by
  have hs : statisticsPayment ≤ (2073997360761/500000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (847548206267/8000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12237 (1/10^6) (1/10^7) ((264327/125000000000))
      (712/10000) rowEps =
      exp (-((mW 12237 : ℝ)*24474)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12237 : ℝ)*24474)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12237) (mW 12237)).real
      (goodDist 12237 (712/10000))ᶜ ≤ (55095761/500000000000) := by
  apply le_trans (concrete_distance_charge (n := 12237) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (264327/125000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12237 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (738733102209/1000000000000000000)
  k0 := (4063334201658923/1000000000000000000)
  k6 := (2475672267243333/200000000000000000)
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
  norm_lower := (window_guards (n := 12237) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12237) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((55095761/500000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12237 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12237) internalParameters :=
  BstLean.Part227.worldPackage (n := 12237) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (55095761/500000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12237) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12237.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12237, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12237.frame := by
  exact frame.2.trans (by norm_num [Part259.world12237])

theorem moment_payment : internalParameters.moment ≤ Part259.world12237.moment := by
  exact moment.2.trans (by norm_num [Part259.world12237])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1193530421/1000000000000) ∧
    internalParameters.frame ≤ (79033752731/125000000000) ∧
    internalParameters.moment ≤ (324462437/31250000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12237) (Part259.world12237) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12237]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12237])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12237]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12237]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12237).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12237).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12237
#eval (do IO.println s!"P260 END 12237 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12238 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12238
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
    exp (-((mW 12238 : ℝ)*24476)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12238 : ℝ)*24476)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12238 : ℝ)*24476)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12238 : ℝ)*24476)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24476 (mW 12238) i /
      (rowEps i * e1MeanBounds 24476 (mW 12238) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24476 (mW 12238) (1/10^6) (1/10^7) rowEps ≤ (2114441/1000000000000) := by
  have hr : 0 ≤ firstRatio 24476 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24476 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24476) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12238 (1/10^6) (1/10^7) ((2114441/1000000000000))
      (712/10000) rowEps ≤ (27543209/250000000000) := by
  have hs : statisticsPayment ≤ (16589201569/4000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (13240691804273/125000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12238 (1/10^6) (1/10^7) ((2114441/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 12238 : ℝ)*24476)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12238 : ℝ)*24476)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12238) (mW 12238)).real
      (goodDist 12238 (712/10000))ᶜ ≤ (27543209/250000000000) := by
  apply le_trans (concrete_distance_charge (n := 12238) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (2114441/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12238 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (369321279123/500000000000000000)
  k0 := (2031542589806949/500000000000000000)
  k6 := (6188927795616629/500000000000000000)
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
  norm_lower := (window_guards (n := 12238) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12238) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((27543209/250000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12238 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12238) internalParameters :=
  BstLean.Part227.worldPackage (n := 12238) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (27543209/250000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12238) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12238.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12238, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12238.frame := by
  exact frame.2.trans (by norm_num [Part259.world12238])

theorem moment_payment : internalParameters.moment ≤ Part259.world12238.moment := by
  exact moment.2.trans (by norm_num [Part259.world12238])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1193481017/1000000000000) ∧
    internalParameters.frame ≤ (316127533121/500000000000) ∧
    internalParameters.moment ≤ (10380577121/1000000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12238) (Part259.world12238) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12238]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12238])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12238]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12238]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12238).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12238).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12238
#eval (do IO.println s!"P260 END 12238 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12239 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12239
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
    exp (-((mW 12239 : ℝ)*24478)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12239 : ℝ)*24478)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12239 : ℝ)*24478)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12239 : ℝ)*24478)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24478 (mW 12239) i /
      (rowEps i * e1MeanBounds 24478 (mW 12239) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24478 (mW 12239) (1/10^6) (1/10^7) rowEps ≤ (1057133/500000000000) := by
  have hr : 0 ≤ firstRatio 24478 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24478 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24478) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12239 (1/10^6) (1/10^7) ((1057133/500000000000))
      (712/10000) rowEps ≤ (110154147/1000000000000) := by
  have hs : statisticsPayment ≤ (207330313897/50000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (26476884804921/250000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12239 (1/10^6) (1/10^7) ((1057133/500000000000))
      (712/10000) rowEps =
      exp (-((mW 12239 : ℝ)*24478)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12239 : ℝ)*24478)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12239) (mW 12239)).real
      (goodDist 12239 (712/10000))ᶜ ≤ (110154147/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 12239) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (1057133/500000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12239 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (369276016389/500000000000000000)
  k0 := (4062836193176917/1000000000000000000)
  k6 := (12377349908234733/1000000000000000000)
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
  norm_lower := (window_guards (n := 12239) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12239) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((110154147/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12239 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12239) internalParameters :=
  BstLean.Part227.worldPackage (n := 12239) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (110154147/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12239) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12239.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12239, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12239.frame := by
  exact frame.2.trans (by norm_num [Part259.world12239])

theorem moment_payment : internalParameters.moment ≤ Part259.world12239.moment := by
  exact moment.2.trans (by norm_num [Part259.world12239])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1193431627/1000000000000) ∧
    internalParameters.frame ≤ (316120056573/500000000000) ∧
    internalParameters.moment ≤ (10378356921/1000000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12239) (Part259.world12239) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12239]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12239])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12239]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12239]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12239).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12239).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12239
#eval (do IO.println s!"P260 END 12239 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12240 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12240
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
    exp (-((mW 12240 : ℝ)*24480)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12240 : ℝ)*24480)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12240 : ℝ)*24480)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12240 : ℝ)*24480)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24480 (mW 12240) i /
      (rowEps i * e1MeanBounds 24480 (mW 12240) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24480 (mW 12240) (1/10^6) (1/10^7) rowEps ≤ (528523/250000000000) := by
  have hr : 0 ≤ firstRatio 24480 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24480 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24480) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12240 (1/10^6) (1/10^7) ((528523/250000000000))
      (712/10000) rowEps ≤ (55067873/500000000000) := by
  have hs : statisticsPayment ≤ (8291824757/2000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (52944915888031/500000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12240 (1/10^6) (1/10^7) ((528523/250000000000))
      (712/10000) rowEps =
      exp (-((mW 12240 : ℝ)*24480)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12240 : ℝ)*24480)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12240) (mW 12240)).real
      (goodDist 12240 (712/10000))ᶜ ≤ (55067873/500000000000) := by
  apply le_trans (concrete_distance_charge (n := 12240) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (528523/250000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12240 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (738461525799/1000000000000000000)
  k0 := (2031293621169011/500000000000000000)
  k6 := (12376844287208429/1000000000000000000)
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
  norm_lower := (window_guards (n := 12240) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12240) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((55067873/500000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12240 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12240) internalParameters :=
  BstLean.Part227.worldPackage (n := 12240) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (55067873/500000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12240) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12240.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12240, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12240.frame := by
  exact frame.2.trans (by norm_num [Part259.world12240])

theorem moment_payment : internalParameters.moment ≤ Part259.world12240.moment := by
  exact moment.2.trans (by norm_num [Part259.world12240])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (4773529/4000000000) ∧
    internalParameters.frame ≤ (1975703633/3125000000) ∧
    internalParameters.moment ≤ (2075227477/200000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12240) (Part259.world12240) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12240]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12240])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12240]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12240]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12240).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12240).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12240
#eval (do IO.println s!"P260 END 12240 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12241 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12241
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
    exp (-((mW 12241 : ℝ)*24482)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12241 : ℝ)*24482)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12241 : ℝ)*24482)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12241 : ℝ)*24482)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24482 (mW 12241) i /
      (rowEps i * e1MeanBounds 24482 (mW 12241) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24482 (mW 12241) (1/10^6) (1/10^7) rowEps ≤ (2113917/1000000000000) := by
  have hr : 0 ≤ firstRatio 24482 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24482 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24482) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12241 (1/10^6) (1/10^7) ((2113917/1000000000000))
      (712/10000) rowEps ≤ (110117049/1000000000000) := by
  have hs : statisticsPayment ≤ (4145218693841/1000000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (661698930081/6250000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12241 (1/10^6) (1/10^7) ((2113917/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 12241 : ℝ)*24482)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12241 : ℝ)*24482)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12241) (mW 12241)).real
      (goodDist 12241 (712/10000))ᶜ ≤ (110117049/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 12241) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (2113917/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12241 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (92296379663/125000000000000000)
  k0 := (4062338327090003/1000000000000000000)
  k6 := (1237633872814169/100000000000000000)
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
  norm_lower := (window_guards (n := 12241) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12241) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((110117049/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12241 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12241) internalParameters :=
  BstLean.Part227.worldPackage (n := 12241) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (110117049/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12241) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12241.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12241, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12241.frame := by
  exact frame.2.trans (by norm_num [Part259.world12241])

theorem moment_payment : internalParameters.moment ≤ Part259.world12241.moment := by
  exact moment.2.trans (by norm_num [Part259.world12241])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1193332887/1000000000000) ∧
    internalParameters.frame ≤ (316105107241/500000000000) ∧
    internalParameters.moment ≤ (648369907/62500000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12241) (Part259.world12241) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12241]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12241])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12241]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12241]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12241).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12241).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12241
#eval (do IO.println s!"P260 END 12241 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12242 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12242
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
    exp (-((mW 12242 : ℝ)*24484)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12242 : ℝ)*24484)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12242 : ℝ)*24484)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12242 : ℝ)*24484)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24484 (mW 12242) i /
      (rowEps i * e1MeanBounds 24484 (mW 12242) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24484 (mW 12242) (1/10^6) (1/10^7) rowEps ≤ (2113743/1000000000000) := by
  have hr : 0 ≤ firstRatio 24484 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24484 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24484) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12242 (1/10^6) (1/10^7) ((2113743/1000000000000))
      (712/10000) rowEps ≤ (1376233/12500000000) := by
  have hs : statisticsPayment ≤ (2072262611937/500000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (52927056787241/500000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12242 (1/10^6) (1/10^7) ((2113743/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 12242 : ℝ)*24484)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12242 : ℝ)*24484)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12242) (mW 12242)).real
      (goodDist 12242 (712/10000))ᶜ ≤ (1376233/12500000000) := by
  apply le_trans (concrete_distance_charge (n := 12242) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (2113743/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12242 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (92285070911/125000000000000000)
  k0 := (253880590464103/62500000000000000)
  k6 := (12375833231021863/1000000000000000000)
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
  norm_lower := (window_guards (n := 12242) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12242) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((1376233/12500000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12242 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12242) internalParameters :=
  BstLean.Part227.worldPackage (n := 12242) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (1376233/12500000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12242) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12242.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12242, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12242.frame := by
  exact frame.2.trans (by norm_num [Part259.world12242])

theorem moment_payment : internalParameters.moment ≤ Part259.world12242.moment := by
  exact moment.2.trans (by norm_num [Part259.world12242])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1193283537/1000000000000) ∧
    internalParameters.frame ≤ (39512204307/62500000000) ∧
    internalParameters.moment ≤ (5185850151/500000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12242) (Part259.world12242) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12242]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12242])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12242]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12242]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12242).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12242).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12242
#eval (do IO.println s!"P260 END 12242 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12243 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12243
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
    exp (-((mW 12243 : ℝ)*24486)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12243 : ℝ)*24486)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12243 : ℝ)*24486)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12243 : ℝ)*24486)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24486 (mW 12243) i /
      (rowEps i * e1MeanBounds 24486 (mW 12243) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24486 (mW 12243) (1/10^6) (1/10^7) rowEps ≤ (66049/31250000000) := by
  have hr : 0 ≤ firstRatio 24486 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24486 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24486) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12243 (1/10^6) (1/10^7) ((66049/31250000000))
      (712/10000) rowEps ≤ (1719999/15625000000) := by
  have hs : statisticsPayment ≤ (4143831968507/1000000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (10583610287403/100000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12243 (1/10^6) (1/10^7) ((66049/31250000000))
      (712/10000) rowEps =
      exp (-((mW 12243 : ℝ)*24486)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12243 : ℝ)*24486)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12243) (mW 12243)).real
      (goodDist 12243 (712/10000))ᶜ ≤ (1719999/15625000000) := by
  apply le_trans (concrete_distance_charge (n := 12243) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (66049/31250000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12243 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (369095057873/500000000000000000)
  k0 := (4061840603337741/1000000000000000000)
  k6 := (1546915974479537/125000000000000000)
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
  norm_lower := (window_guards (n := 12243) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12243) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((1719999/15625000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12243 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12243) internalParameters :=
  BstLean.Part227.worldPackage (n := 12243) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (1719999/15625000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12243) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12243.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12243, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12243.frame := by
  exact frame.2.trans (by norm_num [Part259.world12243])

theorem moment_payment : internalParameters.moment ≤ Part259.world12243.moment := by
  exact moment.2.trans (by norm_num [Part259.world12243])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1193234201/1000000000000) ∧
    internalParameters.frame ≤ (632180325849/1000000000000) ∧
    internalParameters.moment ≤ (5184741377/500000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12243) (Part259.world12243) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12243]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12243])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12243]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12243]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12243).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12243).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12243
#eval (do IO.println s!"P260 END 12243 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12244 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12244
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
    exp (-((mW 12244 : ℝ)*24488)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12244 : ℝ)*24488)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12244 : ℝ)*24488)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12244 : ℝ)*24488)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24488 (mW 12244) i /
      (rowEps i * e1MeanBounds 24488 (mW 12244) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24488 (mW 12244) (1/10^6) (1/10^7) rowEps ≤ (2113393/1000000000000) := by
  have hr : 0 ≤ firstRatio 24488 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24488 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24488) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12244 (1/10^6) (1/10^7) ((2113393/1000000000000))
      (712/10000) rowEps ≤ (110061229/1000000000000) := by
  have hs : statisticsPayment ≤ (1035784731913/250000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (105818088322419/1000000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12244 (1/10^6) (1/10^7) ((2113393/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 12244 : ℝ)*24488)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12244 : ℝ)*24488)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12244) (mW 12244)).real
      (goodDist 12244 (712/10000))ᶜ ≤ (110061229/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 12244) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (2113393/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12244 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (738099682671/1000000000000000000)
  k0 := (2030795897406781/500000000000000000)
  k6 := (2474964484514469/200000000000000000)
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
  norm_lower := (window_guards (n := 12244) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12244) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((110061229/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12244 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12244) internalParameters :=
  BstLean.Part227.worldPackage (n := 12244) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (110061229/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12244) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12244.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12244, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12244.frame := by
  exact frame.2.trans (by norm_num [Part259.world12244])

theorem moment_payment : internalParameters.moment ≤ Part259.world12244.moment := by
  exact moment.2.trans (by norm_num [Part259.world12244])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (596592439/500000000000) ∧
    internalParameters.frame ≤ (632165385293/1000000000000) ∧
    internalParameters.moment ≤ (10367265869/1000000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12244) (Part259.world12244) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12244]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12244])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12244]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12244]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12244).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12244).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12244
#eval (do IO.println s!"P260 END 12244 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12245 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12245
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
    exp (-((mW 12245 : ℝ)*24490)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12245 : ℝ)*24490)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12245 : ℝ)*24490)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12245 : ℝ)*24490)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24490 (mW 12245) i /
      (rowEps i * e1MeanBounds 24490 (mW 12245) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24490 (mW 12245) (1/10^6) (1/10^7) rowEps ≤ (2113219/1000000000000) := by
  have hr : 0 ≤ firstRatio 24490 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24490 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24490) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12245 (1/10^6) (1/10^7) ((2113219/1000000000000))
      (712/10000) rowEps ≤ (110042809/1000000000000) := by
  have hs : statisticsPayment ≤ (4142446101219/1000000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (52900180712651/500000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12245 (1/10^6) (1/10^7) ((2113219/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 12245 : ℝ)*24490)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12245 : ℝ)*24490)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12245) (mW 12245)).real
      (goodDist 12245 (712/10000))ᶜ ≤ (110042809/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 12245) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (2113219/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12245 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (738009268059/1000000000000000000)
  k0 := (4061343021848641/1000000000000000000)
  k6 := (1546789638902171/125000000000000000)
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
  norm_lower := (window_guards (n := 12245) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12245) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((110042809/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12245 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12245) internalParameters :=
  BstLean.Part227.worldPackage (n := 12245) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (110042809/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12245) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12245.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12245, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12245.frame := by
  exact frame.2.trans (by norm_num [Part259.world12245])

theorem moment_payment : internalParameters.moment ≤ Part259.world12245.moment := by
  exact moment.2.trans (by norm_num [Part259.world12245])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (119313557/100000000000) ∧
    internalParameters.frame ≤ (632150447243/1000000000000) ∧
    internalParameters.moment ≤ (5182524823/500000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12245) (Part259.world12245) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12245]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12245])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12245]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12245]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12245).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12245).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12245
#eval (do IO.println s!"P260 END 12245 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12246 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12246
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
    exp (-((mW 12246 : ℝ)*24492)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12246 : ℝ)*24492)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12246 : ℝ)*24492)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12246 : ℝ)*24492)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24492 (mW 12246) i /
      (rowEps i * e1MeanBounds 24492 (mW 12246) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24492 (mW 12246) (1/10^6) (1/10^7) rowEps ≤ (528261/250000000000) := by
  have hr : 0 ≤ firstRatio 24492 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24492 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24492) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12246 (1/10^6) (1/10^7) ((528261/250000000000))
      (712/10000) rowEps ≤ (55012047/500000000000) := by
  have hs : statisticsPayment ≤ (4141753489117/1000000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (52891169576633/500000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12246 (1/10^6) (1/10^7) ((528261/250000000000))
      (712/10000) rowEps =
      exp (-((mW 12246 : ℝ)*24492)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12246 : ℝ)*24492)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12246) (mW 12246)).real
      (goodDist 12246 (712/10000))ᶜ ≤ (55012047/500000000000) := by
  apply le_trans (concrete_distance_charge (n := 12246) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (528261/250000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12246 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (147583774381/200000000000000000)
  k0 := (812218856887151/200000000000000000)
  k6 := (3093452965439681/250000000000000000)
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
  norm_lower := (window_guards (n := 12246) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12246) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((55012047/500000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12246 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12246) internalParameters :=
  BstLean.Part227.worldPackage (n := 12246) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (55012047/500000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12246) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12246.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12246, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12246.frame := by
  exact frame.2.trans (by norm_num [Part259.world12246])

theorem moment_payment : internalParameters.moment ≤ Part259.world12246.moment := by
  exact moment.2.trans (by norm_num [Part259.world12246])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (596543137/500000000000) ∧
    internalParameters.frame ≤ (632135511697/1000000000000) ∧
    internalParameters.moment ≤ (2072566817/200000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12246) (Part259.world12246) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12246]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12246])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12246]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12246]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12246).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12246).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12246
#eval (do IO.println s!"P260 END 12246 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12247 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12247
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
    exp (-((mW 12247 : ℝ)*24494)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12247 : ℝ)*24494)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12247 : ℝ)*24494)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12247 : ℝ)*24494)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24494 (mW 12247) i /
      (rowEps i * e1MeanBounds 24494 (mW 12247) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24494 (mW 12247) (1/10^6) (1/10^7) rowEps ≤ (211287/100000000000) := by
  have hr : 0 ≤ firstRatio 24494 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24494 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24494) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12247 (1/10^6) (1/10^7) ((211287/100000000000))
      (712/10000) rowEps ≤ (110005667/1000000000000) := by
  have hs : statisticsPayment ≤ (4141061091257/1000000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (105764604489203/1000000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12247 (1/10^6) (1/10^7) ((211287/100000000000))
      (712/10000) rowEps =
      exp (-((mW 12247 : ℝ)*24494)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12247 : ℝ)*24494)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12247) (mW 12247)).real
      (goodDist 12247 (712/10000))ᶜ ≤ (110005667/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 12247) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (211287/100000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12247 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (184457123551/250000000000000000)
  k0 := (1015211395641919/250000000000000000)
  k6 := (12373306674183779/1000000000000000000)
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
  norm_lower := (window_guards (n := 12247) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12247) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((110005667/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12247 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12247) internalParameters :=
  BstLean.Part227.worldPackage (n := 12247) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (110005667/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12247) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12247.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12247, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12247.frame := by
  exact frame.2.trans (by norm_num [Part259.world12247])

theorem moment_payment : internalParameters.moment ≤ Part259.world12247.moment := by
  exact moment.2.trans (by norm_num [Part259.world12247])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (18641203/15625000000) ∧
    internalParameters.frame ≤ (632120578657/1000000000000) ∧
    internalParameters.moment ≤ (2072123837/200000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12247) (Part259.world12247) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12247]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12247])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12247]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12247]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12247).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12247).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12247
#eval (do IO.println s!"P260 END 12247 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12248 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12248
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
    exp (-((mW 12248 : ℝ)*24496)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12248 : ℝ)*24496)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12248 : ℝ)*24496)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12248 : ℝ)*24496)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24496 (mW 12248) i /
      (rowEps i * e1MeanBounds 24496 (mW 12248) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24496 (mW 12248) (1/10^6) (1/10^7) rowEps ≤ (264087/125000000000) := by
  have hr : 0 ≤ firstRatio 24496 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24496 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24496) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12248 (1/10^6) (1/10^7) ((264087/125000000000))
      (712/10000) rowEps ≤ (27496809/250000000000) := by
  have hs : statisticsPayment ≤ (4140368907549/1000000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (105746865933071/1000000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12248 (1/10^6) (1/10^7) ((264087/125000000000))
      (712/10000) rowEps =
      exp (-((mW 12248 : ℝ)*24496)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12248 : ℝ)*24496)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12248) (mW 12248)).real
      (goodDist 12248 (712/10000))ᶜ ≤ (27496809/250000000000) := by
  apply le_trans (concrete_distance_charge (n := 12248) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (264087/125000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12248 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (737738134949/1000000000000000000)
  k0 := (4060596916231671/1000000000000000000)
  k6 := (12372801548479901/1000000000000000000)
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
  norm_lower := (window_guards (n := 12248) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12248) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((27496809/250000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12248 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12248) internalParameters :=
  BstLean.Part227.worldPackage (n := 12248) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (27496809/250000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12248) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12248.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12248, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12248.frame := by
  exact frame.2.trans (by norm_num [Part259.world12248])

theorem moment_payment : internalParameters.moment ≤ Part259.world12248.moment := by
  exact moment.2.trans (by norm_num [Part259.world12248])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (298246931/250000000000) ∧
    internalParameters.frame ≤ (15802641203/25000000000) ∧
    internalParameters.moment ≤ (10358404947/1000000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12248) (Part259.world12248) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12248]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12248])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12248]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12248]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12248).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12248).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12248
#eval (do IO.println s!"P260 END 12248 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12249 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12249
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
    exp (-((mW 12249 : ℝ)*24498)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12249 : ℝ)*24498)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12249 : ℝ)*24498)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12249 : ℝ)*24498)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24498 (mW 12249) i /
      (rowEps i * e1MeanBounds 24498 (mW 12249) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24498 (mW 12249) (1/10^6) (1/10^7) rowEps ≤ (2112521/1000000000000) := by
  have hr : 0 ≤ firstRatio 24498 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24498 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24498) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12249 (1/10^6) (1/10^7) ((2112521/1000000000000))
      (712/10000) rowEps ≤ (109968511/1000000000000) := by
  have hs : statisticsPayment ≤ (258729808619/62500000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (105728832088181/1000000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12249 (1/10^6) (1/10^7) ((2112521/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 12249 : ℝ)*24498)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12249 : ℝ)*24498)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12249) (mW 12249)).real
      (goodDist 12249 (712/10000))ᶜ ≤ (109968511/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 12249) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (2112521/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12249 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (92205974267/125000000000000000)
  k0 := (203017414271163/50000000000000000)
  k6 := (6186148242317231/500000000000000000)
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
  norm_lower := (window_guards (n := 12249) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12249) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((109968511/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12249 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12249) internalParameters :=
  BstLean.Part227.worldPackage (n := 12249) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (109968511/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12249) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12249.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12249, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12249.frame := by
  exact frame.2.trans (by norm_num [Part259.world12249])

theorem moment_payment : internalParameters.moment ≤ Part259.world12249.moment := by
  exact moment.2.trans (by norm_num [Part259.world12249])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1192938469/1000000000000) ∧
    internalParameters.frame ≤ (632090720087/1000000000000) ∧
    internalParameters.moment ≤ (1035619137/100000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12249) (Part259.world12249) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12249]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12249])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12249]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12249]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12249).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12249).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12249
#eval (do IO.println s!"P260 END 12249 6 {← IO.monoMsNow}" : IO Unit)
