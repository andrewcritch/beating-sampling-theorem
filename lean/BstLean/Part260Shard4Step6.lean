import BstLean.Part260Shard4Step5
#eval (do IO.println s!"P260 START 12325 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12325
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
    exp (-((mW 12325 : ℝ)*24650)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12325 : ℝ)*24650)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12325 : ℝ)*24650)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12325 : ℝ)*24650)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24650 (mW 12325) i /
      (rowEps i * e1MeanBounds 24650 (mW 12325) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24650 (mW 12325) (1/10^6) (1/10^7) rowEps ≤ (262419/125000000000) := by
  have hr : 0 ≤ firstRatio 24650 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24650 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24650) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12325 (1/10^6) (1/10^7) ((262419/125000000000))
      (712/10000) rowEps ≤ (54286433/500000000000) := by
  have hs : statisticsPayment ≤ (408770683929/100000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (104385157589969/1000000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12325 (1/10^6) (1/10^7) ((262419/125000000000))
      (712/10000) rowEps =
      exp (-((mW 12325 : ℝ)*24650)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12325 : ℝ)*24650)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12325) (mW 12325)).real
      (goodDist 12325 (712/10000))ᶜ ≤ (54286433/500000000000) := by
  apply le_trans (concrete_distance_charge (n := 12325) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (262419/125000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12325 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (730835454947/1000000000000000000)
  k0 := (505194461600949/125000000000000000)
  k6 := (12334091674874931/1000000000000000000)
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
  norm_lower := (window_guards (n := 12325) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12325) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((54286433/500000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12325 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12325) internalParameters :=
  BstLean.Part227.worldPackage (n := 12325) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (54286433/500000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12325) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12325.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12325, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12325.frame := by
  exact frame.2.trans (by norm_num [Part259.world12325])

theorem moment_payment : internalParameters.moment ≤ Part259.world12325.moment := by
  exact moment.2.trans (by norm_num [Part259.world12325])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1189234363/1000000000000) ∧
    internalParameters.frame ≤ (630963463397/1000000000000) ∧
    internalParameters.moment ≤ (2547468691/250000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12325) (Part259.world12325) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12325]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12325])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12325]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12325]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12325).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12325).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12325
#eval (do IO.println s!"P260 END 12325 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12326 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12326
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
    exp (-((mW 12326 : ℝ)*24652)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12326 : ℝ)*24652)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12326 : ℝ)*24652)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12326 : ℝ)*24652)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24652 (mW 12326) i /
      (rowEps i * e1MeanBounds 24652 (mW 12326) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24652 (mW 12326) (1/10^6) (1/10^7) rowEps ≤ (104959/50000000000) := by
  have hr : 0 ≤ firstRatio 24652 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24652 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24652) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12326 (1/10^6) (1/10^7) ((104959/50000000000))
      (712/10000) rowEps ≤ (54277367/500000000000) := by
  have hs : statisticsPayment ≤ (2043515543403/500000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (52183850694193/500000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12326 (1/10^6) (1/10^7) ((104959/50000000000))
      (712/10000) rowEps =
      exp (-((mW 12326 : ℝ)*24652)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12326 : ℝ)*24652)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12326) (mW 12326)).real
      (goodDist 12326 (712/10000))ᶜ ≤ (54277367/500000000000) := by
  apply le_trans (concrete_distance_charge (n := 12326) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (104959/50000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12326 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (182686629619/250000000000000000)
  k0 := (4041309773815737/1000000000000000000)
  k6 := (385424729265333/31250000000000000)
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
  norm_lower := (window_guards (n := 12326) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12326) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((54277367/500000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12326 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12326) internalParameters :=
  BstLean.Part227.worldPackage (n := 12326) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (54277367/500000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12326) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12326.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12326, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12326.frame := by
  exact frame.2.trans (by norm_num [Part259.world12326])

theorem moment_payment : internalParameters.moment ≤ Part259.world12326.moment := by
  exact moment.2.trans (by norm_num [Part259.world12326])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1189186137/1000000000000) ∧
    internalParameters.frame ≤ (15773718153/25000000000) ∧
    internalParameters.moment ≤ (10187711339/1000000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12326) (Part259.world12326) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12326]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12326])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12326]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12326]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12326).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12326).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12326
#eval (do IO.println s!"P260 END 12326 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12327 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12327
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
    exp (-((mW 12327 : ℝ)*24654)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12327 : ℝ)*24654)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12327 : ℝ)*24654)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12327 : ℝ)*24654)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24654 (mW 12327) i /
      (rowEps i * e1MeanBounds 24654 (mW 12327) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24654 (mW 12327) (1/10^6) (1/10^7) rowEps ≤ (32797/15625000000) := by
  have hr : 0 ≤ firstRatio 24654 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24654 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24654) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12327 (1/10^6) (1/10^7) ((32797/15625000000))
      (712/10000) rowEps ≤ (54268299/500000000000) := by
  have hs : statisticsPayment ≤ (408635554153/100000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (104350241408967/1000000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12327 (1/10^6) (1/10^7) ((32797/15625000000))
      (712/10000) rowEps =
      exp (-((mW 12327 : ℝ)*24654)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12327 : ℝ)*24654)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12327) (mW 12327)).real
      (goodDist 12327 (712/10000))ᶜ ≤ (54268299/500000000000) := by
  apply le_trans (concrete_distance_charge (n := 12327) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (32797/15625000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12327 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (730657600041/1000000000000000000)
  k0 := (31570811638551/7812500000000000)
  k6 := (6166545529495423/500000000000000000)
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
  norm_lower := (window_guards (n := 12327) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12327) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((54268299/500000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12327 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12327) internalParameters :=
  BstLean.Part227.worldPackage (n := 12327) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (54268299/500000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12327) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12327.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12327, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12327.frame := by
  exact frame.2.trans (by norm_num [Part259.world12327])

theorem moment_payment : internalParameters.moment ≤ Part259.world12327.moment := by
  exact moment.2.trans (by norm_num [Part259.world12327])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1189137923/1000000000000) ∧
    internalParameters.frame ≤ (126186798259/200000000000) ∧
    internalParameters.moment ≤ (10185548557/1000000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12327) (Part259.world12327) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12327]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12327])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12327]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12327]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12327).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12327).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12327
#eval (do IO.println s!"P260 END 12327 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12328 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12328
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
    exp (-((mW 12328 : ℝ)*24656)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12328 : ℝ)*24656)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12328 : ℝ)*24656)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12328 : ℝ)*24656)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24656 (mW 12328) i /
      (rowEps i * e1MeanBounds 24656 (mW 12328) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24656 (mW 12328) (1/10^6) (1/10^7) rowEps ≤ (419767/200000000000) := by
  have hr : 0 ≤ firstRatio 24656 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24656 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24656) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12328 (1/10^6) (1/10^7) ((419767/200000000000))
      (712/10000) rowEps ≤ (10851817/100000000000) := by
  have hs : statisticsPayment ≤ (4085680203377/1000000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (52166244148463/500000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12328 (1/10^6) (1/10^7) ((419767/200000000000))
      (712/10000) rowEps =
      exp (-((mW 12328 : ℝ)*24656)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12328 : ℝ)*24656)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12328) (mW 12328)).real
      (goodDist 12328 (712/10000))ᶜ ≤ (10851817/100000000000) := by
  apply le_trans (concrete_distance_charge (n := 12328) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (419767/200000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12328 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (365284349819/500000000000000000)
  k0 := (1010204510139819/250000000000000000)
  k6 := (6166295421181577/500000000000000000)
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
  norm_lower := (window_guards (n := 12328) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12328) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((10851817/100000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12328 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12328) internalParameters :=
  BstLean.Part227.worldPackage (n := 12328) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (10851817/100000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12328) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12328.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12328, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12328.frame := by
  exact frame.2.trans (by norm_num [Part259.world12328])

theorem moment_payment : internalParameters.moment ≤ Part259.world12328.moment := by
  exact moment.2.trans (by norm_num [Part259.world12328])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1189089723/1000000000000) ∧
    internalParameters.frame ≤ (630919258921/1000000000000) ∧
    internalParameters.moment ≤ (2036677283/200000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12328) (Part259.world12328) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12328]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12328])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12328]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12328]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12328).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12328).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12328
#eval (do IO.println s!"P260 END 12328 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12329 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12329
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
    exp (-((mW 12329 : ℝ)*24658)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12329 : ℝ)*24658)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12329 : ℝ)*24658)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12329 : ℝ)*24658)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24658 (mW 12329) i /
      (rowEps i * e1MeanBounds 24658 (mW 12329) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24658 (mW 12329) (1/10^6) (1/10^7) rowEps ≤ (2098663/1000000000000) := by
  have hr : 0 ≤ firstRatio 24658 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24658 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24658) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12329 (1/10^6) (1/10^7) ((2098663/1000000000000))
      (712/10000) rowEps ≤ (108500027/1000000000000) := by
  have hs : statisticsPayment ≤ (204250253613/50000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (104315020795471/1000000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12329 (1/10^6) (1/10^7) ((2098663/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 12329 : ℝ)*24658)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12329 : ℝ)*24658)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12329) (mW 12329)).real
      (goodDist 12329 (712/10000))ᶜ ≤ (108500027/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 12329) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (2098663/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12329 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (36523990863/50000000000000000)
  k0 := (31566970517789/7812500000000000)
  k6 := (3083022671648809/250000000000000000)
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
  norm_lower := (window_guards (n := 12329) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12329) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((108500027/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12329 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12329) internalParameters :=
  BstLean.Part227.worldPackage (n := 12329) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (108500027/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12329) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12329.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12329, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12329.frame := by
  exact frame.2.trans (by norm_num [Part259.world12329])

theorem moment_payment : internalParameters.moment ≤ Part259.world12329.moment := by
  exact moment.2.trans (by norm_num [Part259.world12329])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (9289387/7812500000) ∧
    internalParameters.frame ≤ (315452264499/500000000000) ∧
    internalParameters.moment ≤ (2036244983/200000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12329) (Part259.world12329) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12329]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12329])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12329]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12329]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12329).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12329).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12329
#eval (do IO.println s!"P260 END 12329 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12330 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12330
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
    exp (-((mW 12330 : ℝ)*24660)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12330 : ℝ)*24660)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12330 : ℝ)*24660)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12330 : ℝ)*24660)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24660 (mW 12330) i /
      (rowEps i * e1MeanBounds 24660 (mW 12330) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24660 (mW 12330) (1/10^6) (1/10^7) rowEps ≤ (2098491/1000000000000) := by
  have hr : 0 ≤ firstRatio 24660 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24660 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24660) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12330 (1/10^6) (1/10^7) ((2098491/1000000000000))
      (712/10000) rowEps ≤ (108481881/1000000000000) := by
  have hs : statisticsPayment ≤ (2042165074047/500000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (104297549524299/1000000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12330 (1/10^6) (1/10^7) ((2098491/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 12330 : ℝ)*24660)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12330 : ℝ)*24660)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12330) (mW 12330)).real
      (goodDist 12330 (712/10000))ᶜ ≤ (108481881/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 12330) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (2098491/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12330 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (91298869113/125000000000000000)
  k0 := (4040326446885747/1000000000000000000)
  k6 := (12331590591674753/1000000000000000000)
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
  norm_lower := (window_guards (n := 12330) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12330) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((108481881/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12330 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12330) internalParameters :=
  BstLean.Part227.worldPackage (n := 12330) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (108481881/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12330) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12330.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12330, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12330.frame := by
  exact frame.2.trans (by norm_num [Part259.world12330])

theorem moment_payment : internalParameters.moment ≤ Part259.world12330.moment := by
  exact moment.2.trans (by norm_num [Part259.world12330])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (594496681/500000000000) ∧
    internalParameters.frame ≤ (157722450381/250000000000) ∧
    internalParameters.moment ≤ (2035812811/200000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12330) (Part259.world12330) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12330]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12330])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12330]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12330]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12330).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12330).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12330
#eval (do IO.println s!"P260 END 12330 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12331 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12331
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
    exp (-((mW 12331 : ℝ)*24662)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12331 : ℝ)*24662)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12331 : ℝ)*24662)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12331 : ℝ)*24662)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24662 (mW 12331) i /
      (rowEps i * e1MeanBounds 24662 (mW 12331) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24662 (mW 12331) (1/10^6) (1/10^7) rowEps ≤ (2098319/1000000000000) := by
  have hr : 0 ≤ firstRatio 24662 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24662 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24662) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12331 (1/10^6) (1/10^7) ((2098319/1000000000000))
      (712/10000) rowEps ≤ (108463731/1000000000000) := by
  have hs : statisticsPayment ≤ (510456928849/125000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (26070018621527/250000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12331 (1/10^6) (1/10^7) ((2098319/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 12331 : ℝ)*24662)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12331 : ℝ)*24662)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12331) (mW 12331)).real
      (goodDist 12331 (712/10000))ᶜ ≤ (108463731/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 12331) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (2098319/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12331 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (146060421313/200000000000000000)
  k0 := (4040080702378079/1000000000000000000)
  k6 := (12331090557589367/1000000000000000000)
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
  norm_lower := (window_guards (n := 12331) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12331) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((108463731/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12331 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12331) internalParameters :=
  BstLean.Part227.worldPackage (n := 12331) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (108463731/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12331) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12331.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12331, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12331.frame := by
  exact frame.2.trans (by norm_num [Part259.world12331])

theorem moment_payment : internalParameters.moment ≤ Part259.world12331.moment := by
  exact moment.2.trans (by norm_num [Part259.world12331])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (594472601/500000000000) ∧
    internalParameters.frame ≤ (1261750153/2000000000) ∧
    internalParameters.moment ≤ (10176903837/1000000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12331) (Part259.world12331) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12331]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12331])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12331]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12331]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12331).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12331).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12331
#eval (do IO.println s!"P260 END 12331 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12332 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12332
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
    exp (-((mW 12332 : ℝ)*24664)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12332 : ℝ)*24664)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12332 : ℝ)*24664)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12332 : ℝ)*24664)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24664 (mW 12332) i /
      (rowEps i * e1MeanBounds 24664 (mW 12332) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24664 (mW 12332) (1/10^6) (1/10^7) rowEps ≤ (2098147/1000000000000) := by
  have hr : 0 ≤ firstRatio 24664 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24664 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24664) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12332 (1/10^6) (1/10^7) ((2098147/1000000000000))
      (712/10000) rowEps ≤ (54222789/500000000000) := by
  have hs : statisticsPayment ≤ (4082980920269/1000000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (52131297841799/500000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12332 (1/10^6) (1/10^7) ((2098147/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 12332 : ℝ)*24664)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12332 : ℝ)*24664)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12332) (mW 12332)).real
      (goodDist 12332 (712/10000))ᶜ ≤ (54222789/500000000000) := by
  apply le_trans (concrete_distance_charge (n := 12332) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (2098147/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12332 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (182553319559/250000000000000000)
  k0 := (4039834992740991/1000000000000000000)
  k6 := (6165295292163373/500000000000000000)
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
  norm_lower := (window_guards (n := 12332) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12332) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((54222789/500000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12332 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12332) internalParameters :=
  BstLean.Part227.worldPackage (n := 12332) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (54222789/500000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12332) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12332.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12332, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12332.frame := by
  exact frame.2.trans (by norm_num [Part259.world12332])

theorem moment_payment : internalParameters.moment ≤ Part259.world12332.moment := by
  exact moment.2.trans (by norm_num [Part259.world12332])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (594448527/500000000000) ∧
    internalParameters.frame ≤ (157715088481/250000000000) ∧
    internalParameters.moment ≤ (5087372129/500000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12332) (Part259.world12332) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12332]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12332])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12332]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12332]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12332).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12332).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12332
#eval (do IO.println s!"P260 END 12332 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12333 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12333
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
    exp (-((mW 12333 : ℝ)*24666)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12333 : ℝ)*24666)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12333 : ℝ)*24666)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12333 : ℝ)*24666)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24666 (mW 12333) i /
      (rowEps i * e1MeanBounds 24666 (mW 12333) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24666 (mW 12333) (1/10^6) (1/10^7) rowEps ≤ (83919/40000000000) := by
  have hr : 0 ≤ firstRatio 24666 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24666 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24666) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12333 (1/10^6) (1/10^7) ((83919/40000000000))
      (712/10000) rowEps ≤ (108427421/1000000000000) := by
  have hs : statisticsPayment ≤ (4082306616439/1000000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (10424511311947/100000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12333 (1/10^6) (1/10^7) ((83919/40000000000))
      (712/10000) rowEps =
      exp (-((mW 12333 : ℝ)*24666)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12333 : ℝ)*24666)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12333) (mW 12333)).real
      (goodDist 12333 (712/10000))ᶜ ≤ (108427421/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 12333) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (83919/40000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12333 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (730124467913/1000000000000000000)
  k0 := (201979465898489/50000000000000000)
  k6 := (4816441668701/390625000000000)
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
  norm_lower := (window_guards (n := 12333) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12333) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((108427421/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12333 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12333) internalParameters :=
  BstLean.Part227.worldPackage (n := 12333) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (108427421/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12333) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12333.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12333, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12333.frame := by
  exact frame.2.trans (by norm_num [Part259.world12333])

theorem moment_payment : internalParameters.moment ≤ Part259.world12333.moment := by
  exact moment.2.trans (by norm_num [Part259.world12333])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (29721223/25000000000) ∧
    internalParameters.frame ≤ (126169126759/200000000000) ∧
    internalParameters.moment ≤ (10172585321/1000000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12333) (Part259.world12333) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12333]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12333])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12333]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12333]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12333).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12333).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12333
#eval (do IO.println s!"P260 END 12333 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12334 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12334
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
    exp (-((mW 12334 : ℝ)*24668)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12334 : ℝ)*24668)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12334 : ℝ)*24668)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12334 : ℝ)*24668)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24668 (mW 12334) i /
      (rowEps i * e1MeanBounds 24668 (mW 12334) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24668 (mW 12334) (1/10^6) (1/10^7) rowEps ≤ (2097803/1000000000000) := by
  have hr : 0 ≤ firstRatio 24668 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24668 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24668) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12334 (1/10^6) (1/10^7) ((2097803/1000000000000))
      (712/10000) rowEps ≤ (108409261/1000000000000) := by
  have hs : statisticsPayment ≤ (816326503843/200000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (104227626796427/1000000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12334 (1/10^6) (1/10^7) ((2097803/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 12334 : ℝ)*24668)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12334 : ℝ)*24668)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12334) (mW 12334)).real
      (goodDist 12334 (712/10000))ᶜ ≤ (108409261/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 12334) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (2097803/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12334 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (73003567559/100000000000000000)
  k0 := (4039343678054209/1000000000000000000)
  k6 := (12329590820220483/1000000000000000000)
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
  norm_lower := (window_guards (n := 12334) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12334) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((108409261/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12334 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12334) internalParameters :=
  BstLean.Part227.worldPackage (n := 12334) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (108409261/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12334) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12334.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12334, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12334.frame := by
  exact frame.2.trans (by norm_num [Part259.world12334])

theorem moment_payment : internalParameters.moment ≤ Part259.world12334.moment := by
  exact moment.2.trans (by norm_num [Part259.world12334])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (594400399/500000000000) ∧
    internalParameters.frame ≤ (315415458057/500000000000) ∧
    internalParameters.moment ≤ (10170427023/1000000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12334) (Part259.world12334) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12334]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12334])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12334]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12334]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12334).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12334).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12334
#eval (do IO.println s!"P260 END 12334 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12335 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12335
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
    exp (-((mW 12335 : ℝ)*24670)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12335 : ℝ)*24670)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12335 : ℝ)*24670)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12335 : ℝ)*24670)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24670 (mW 12335) i /
      (rowEps i * e1MeanBounds 24670 (mW 12335) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24670 (mW 12335) (1/10^6) (1/10^7) rowEps ≤ (2097631/1000000000000) := by
  have hr : 0 ≤ firstRatio 24670 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24670 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24670) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12335 (1/10^6) (1/10^7) ((2097631/1000000000000))
      (712/10000) rowEps ≤ (108391097/1000000000000) := by
  have hs : statisticsPayment ≤ (127529957141/31250000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (52105068358587/500000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12335 (1/10^6) (1/10^7) ((2097631/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 12335 : ℝ)*24670)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12335 : ℝ)*24670)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12335) (mW 12335)).real
      (goodDist 12335 (712/10000))ᶜ ≤ (108391097/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 12335) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (2097631/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12335 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (45621681329/62500000000000000)
  k0 := (252443629562021/62500000000000000)
  k6 := (12329091029352193/1000000000000000000)
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
  norm_lower := (window_guards (n := 12335) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12335) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((108391097/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12335 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12335) internalParameters :=
  BstLean.Part227.worldPackage (n := 12335) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (108391097/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12335) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12335.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12335, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12335.frame := by
  exact frame.2.trans (by norm_num [Part259.world12335])

theorem moment_payment : internalParameters.moment ≤ Part259.world12335.moment := by
  exact moment.2.trans (by norm_num [Part259.world12335])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (118875269/100000000000) ∧
    internalParameters.frame ≤ (7885202511/12500000000) ∧
    internalParameters.moment ≤ (2542067341/250000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12335) (Part259.world12335) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12335]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12335])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12335]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12335]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12335).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12335).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12335
#eval (do IO.println s!"P260 END 12335 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12336 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12336
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
    exp (-((mW 12336 : ℝ)*24672)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12336 : ℝ)*24672)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12336 : ℝ)*24672)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12336 : ℝ)*24672)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24672 (mW 12336) i /
      (rowEps i * e1MeanBounds 24672 (mW 12336) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24672 (mW 12336) (1/10^6) (1/10^7) rowEps ≤ (2097459/1000000000000) := by
  have hr : 0 ≤ firstRatio 24672 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24672 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24672) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12336 (1/10^6) (1/10^7) ((2097459/1000000000000))
      (712/10000) rowEps ≤ (108372929/1000000000000) := by
  have hs : statisticsPayment ≤ (1020071236061/250000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (104192642884413/1000000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12336 (1/10^6) (1/10^7) ((2097459/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 12336 : ℝ)*24672)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12336 : ℝ)*24672)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12336) (mW 12336)).real
      (goodDist 12336 (712/10000))ᶜ ≤ (108372929/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 12336) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (2097459/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12336 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (22808067029/31250000000000000)
  k0 := (4038852502771153/1000000000000000000)
  k6 := (1232859129925737/100000000000000000)
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
  norm_lower := (window_guards (n := 12336) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12336) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((108372929/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12336 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12336) internalParameters :=
  BstLean.Part227.worldPackage (n := 12336) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (108372929/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12336) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12336.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12336, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12336.frame := by
  exact frame.2.trans (by norm_num [Part259.world12336])

theorem moment_payment : internalParameters.moment ≤ Part259.world12336.moment := by
  exact moment.2.trans (by norm_num [Part259.world12336])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (237740919/200000000000) ∧
    internalParameters.frame ≤ (157700372023/250000000000) ∧
    internalParameters.moment ≤ (5083056173/500000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12336) (Part259.world12336) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12336]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12336])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12336]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12336]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12336).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12336).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12336
#eval (do IO.println s!"P260 END 12336 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12337 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12337
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
    exp (-((mW 12337 : ℝ)*24674)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12337 : ℝ)*24674)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12337 : ℝ)*24674)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12337 : ℝ)*24674)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24674 (mW 12337) i /
      (rowEps i * e1MeanBounds 24674 (mW 12337) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24674 (mW 12337) (1/10^6) (1/10^7) rowEps ≤ (262161/125000000000) := by
  have hr : 0 ≤ firstRatio 24674 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24674 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24674) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12337 (1/10^6) (1/10^7) ((262161/125000000000))
      (712/10000) rowEps ≤ (108355047/1000000000000) := by
  have hs : statisticsPayment ≤ (2039805733163/500000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (26043858606857/250000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12337 (1/10^6) (1/10^7) ((262161/125000000000))
      (712/10000) rowEps =
      exp (-((mW 12337 : ℝ)*24674)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12337 : ℝ)*24674)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12337) (mW 12337)).real
      (goodDist 12337 (712/10000))ᶜ ≤ (108355047/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 12337) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (262161/125000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12337 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (729769406577/1000000000000000000)
  k0 := (4038606967383179/1000000000000000000)
  k6 := (12328091629923699/1000000000000000000)
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
  norm_lower := (window_guards (n := 12337) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12337) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((108355047/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12337 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12337) internalParameters :=
  BstLean.Part227.worldPackage (n := 12337) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (108355047/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12337) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12337.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12337, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12337.frame := by
  exact frame.2.trans (by norm_num [Part259.world12337])

theorem moment_payment : internalParameters.moment ≤ Part259.world12337.moment := by
  exact moment.2.trans (by norm_num [Part259.world12337])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1188656513/1000000000000) ∧
    internalParameters.frame ≤ (157696694437/250000000000) ∧
    internalParameters.moment ≤ (5081977983/500000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12337) (Part259.world12337) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12337]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12337])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12337]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12337]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12337).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12337).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12337
#eval (do IO.println s!"P260 END 12337 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12338 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12338
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
    exp (-((mW 12338 : ℝ)*24676)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12338 : ℝ)*24676)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12338 : ℝ)*24676)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12338 : ℝ)*24676)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24676 (mW 12338) i /
      (rowEps i * e1MeanBounds 24676 (mW 12338) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24676 (mW 12338) (1/10^6) (1/10^7) rowEps ≤ (524279/250000000000) := by
  have hr : 0 ≤ firstRatio 24676 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24676 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24676) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12338 (1/10^6) (1/10^7) ((524279/250000000000))
      (712/10000) rowEps ≤ (108336873/1000000000000) := by
  have hs : statisticsPayment ≤ (254933637167/62500000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (52078966534991/500000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12338 (1/10^6) (1/10^7) ((524279/250000000000))
      (712/10000) rowEps =
      exp (-((mW 12338 : ℝ)*24676)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12338 : ℝ)*24676)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12338) (mW 12338)).real
      (goodDist 12338 (712/10000))ᶜ ≤ (108336873/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 12338) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (524279/250000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12338 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (729680686207/1000000000000000000)
  k0 := (4038361466823699/1000000000000000000)
  k6 := (12327592021338869/1000000000000000000)
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
  norm_lower := (window_guards (n := 12338) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12338) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((108336873/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12338 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12338) internalParameters :=
  BstLean.Part227.worldPackage (n := 12338) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (108336873/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12338) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12338.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12338, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12338.frame := by
  exact frame.2.trans (by norm_num [Part259.world12338])

theorem moment_payment : internalParameters.moment ≤ Part259.world12338.moment := by
  exact moment.2.trans (by norm_num [Part259.world12338])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (297152111/250000000000) ∧
    internalParameters.frame ≤ (12615441397/20000000000) ∧
    internalParameters.moment ≤ (5080900113/500000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12338) (Part259.world12338) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12338]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12338])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12338]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12338]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12338).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12338).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12338
#eval (do IO.println s!"P260 END 12338 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12339 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12339
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
    exp (-((mW 12339 : ℝ)*24678)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12339 : ℝ)*24678)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12339 : ℝ)*24678)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12339 : ℝ)*24678)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24678 (mW 12339) i /
      (rowEps i * e1MeanBounds 24678 (mW 12339) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24678 (mW 12339) (1/10^6) (1/10^7) rowEps ≤ (131059/62500000000) := by
  have hr : 0 ≤ firstRatio 24678 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24678 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24678) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12339 (1/10^6) (1/10^7) ((131059/62500000000))
      (712/10000) rowEps ≤ (21663739/200000000000) := by
  have hs : statisticsPayment ≤ (1019566282299/250000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (26035106991781/250000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12339 (1/10^6) (1/10^7) ((131059/62500000000))
      (712/10000) rowEps =
      exp (-((mW 12339 : ℝ)*24678)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12339 : ℝ)*24678)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12339) (mW 12339)).real
      (goodDist 12339 (712/10000))ᶜ ≤ (21663739/200000000000) := by
  apply le_trans (concrete_distance_charge (n := 12339) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (131059/62500000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12339 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (729591983811/1000000000000000000)
  k0 := (4038116001079693/1000000000000000000)
  k6 := (1232709247349057/100000000000000000)
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
  norm_lower := (window_guards (n := 12339) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12339) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((21663739/200000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12339 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12339) internalParameters :=
  BstLean.Part227.worldPackage (n := 12339) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (21663739/200000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12339) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12339.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12339, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12339.frame := by
  exact frame.2.trans (by norm_num [Part259.world12339])

theorem moment_payment : internalParameters.moment ≤ Part259.world12339.moment := by
  exact moment.2.trans (by norm_num [Part259.world12339])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1188560389/1000000000000) ∧
    internalParameters.frame ≤ (126151472879/200000000000) ∧
    internalParameters.moment ≤ (2539911281/250000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12339) (Part259.world12339) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12339]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12339])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12339]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12339]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12339).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12339).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12339
#eval (do IO.println s!"P260 END 12339 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12340 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12340
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
    exp (-((mW 12340 : ℝ)*24680)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12340 : ℝ)*24680)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12340 : ℝ)*24680)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12340 : ℝ)*24680)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24680 (mW 12340) i /
      (rowEps i * e1MeanBounds 24680 (mW 12340) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24680 (mW 12340) (1/10^6) (1/10^7) rowEps ≤ (524193/250000000000) := by
  have hr : 0 ≤ firstRatio 24680 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24680 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24680) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12340 (1/10^6) (1/10^7) ((524193/250000000000))
      (712/10000) rowEps ≤ (108300513/1000000000000) := by
  have hs : statisticsPayment ≤ (4077592269813/1000000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (26030729780391/250000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12340 (1/10^6) (1/10^7) ((524193/250000000000))
      (712/10000) rowEps =
      exp (-((mW 12340 : ℝ)*24680)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12340 : ℝ)*24680)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12340) (mW 12340)).real
      (goodDist 12340 (712/10000))ᶜ ≤ (108300513/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 12340) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (524193/250000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12340 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (729503299387/1000000000000000000)
  k0 := (4037870570151977/1000000000000000000)
  k6 := (12326592986366497/1000000000000000000)
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
  norm_lower := (window_guards (n := 12340) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12340) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((108300513/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12340 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12340) internalParameters :=
  BstLean.Part227.worldPackage (n := 12340) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (108300513/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12340) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12340.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12340, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12340.frame := by
  exact frame.2.trans (by norm_num [Part259.world12340])

theorem moment_payment : internalParameters.moment ≤ Part259.world12340.moment := by
  exact moment.2.trans (by norm_num [Part259.world12340])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (594256173/500000000000) ∧
    internalParameters.frame ≤ (78842832673/125000000000) ∧
    internalParameters.moment ≤ (10157490661/1000000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12340) (Part259.world12340) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12340]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12340])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12340]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12340]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12340).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12340).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12340
#eval (do IO.println s!"P260 END 12340 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12341 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12341
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
    exp (-((mW 12341 : ℝ)*24682)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12341 : ℝ)*24682)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12341 : ℝ)*24682)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12341 : ℝ)*24682)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24682 (mW 12341) i /
      (rowEps i * e1MeanBounds 24682 (mW 12341) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24682 (mW 12341) (1/10^6) (1/10^7) rowEps ≤ (10483/5000000000) := by
  have hr : 0 ≤ firstRatio 24682 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24682 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24682) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12341 (1/10^6) (1/10^7) ((10483/5000000000))
      (712/10000) rowEps ≤ (13535291/125000000000) := by
  have hs : statisticsPayment ≤ (1019229904109/250000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (26026351634003/250000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12341 (1/10^6) (1/10^7) ((10483/5000000000))
      (712/10000) rowEps =
      exp (-((mW 12341 : ℝ)*24682)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12341 : ℝ)*24682)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12341) (mW 12341)).real
      (goodDist 12341 (712/10000))ᶜ ≤ (13535291/125000000000) := by
  apply le_trans (concrete_distance_charge (n := 12341) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (10483/5000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12341 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (729414632927/1000000000000000000)
  k0 := (2018812587012379/500000000000000000)
  k6 := (12326093559954349/1000000000000000000)
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
  norm_lower := (window_guards (n := 12341) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12341) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((13535291/125000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12341 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12341) internalParameters :=
  BstLean.Part227.worldPackage (n := 12341) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (13535291/125000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12341) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12341.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12341, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12341.frame := by
  exact frame.2.trans (by norm_num [Part259.world12341])

theorem moment_payment : internalParameters.moment ≤ Part259.world12341.moment := by
  exact moment.2.trans (by norm_num [Part259.world12341])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1188464317/1000000000000) ∧
    internalParameters.frame ≤ (126145592163/200000000000) ∧
    internalParameters.moment ≤ (2538834209/250000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12341) (Part259.world12341) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12341]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12341])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12341]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12341]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12341).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12341).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12341
#eval (do IO.println s!"P260 END 12341 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12342 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12342
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
    exp (-((mW 12342 : ℝ)*24684)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12342 : ℝ)*24684)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12342 : ℝ)*24684)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12342 : ℝ)*24684)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24684 (mW 12342) i /
      (rowEps i * e1MeanBounds 24684 (mW 12342) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24684 (mW 12342) (1/10^6) (1/10^7) rowEps ≤ (2096429/1000000000000) := by
  have hr : 0 ≤ firstRatio 24684 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24684 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24684) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12342 (1/10^6) (1/10^7) ((2096429/1000000000000))
      (712/10000) rowEps ≤ (27066107/250000000000) := by
  have hs : statisticsPayment ≤ (2038123584491/500000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (104088179211647/1000000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12342 (1/10^6) (1/10^7) ((2096429/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 12342 : ℝ)*24684)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12342 : ℝ)*24684)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12342) (mW 12342)).real
      (goodDist 12342 (712/10000))ᶜ ≤ (27066107/250000000000) := by
  apply le_trans (concrete_distance_charge (n := 12342) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (2096429/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12342 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (729325984427/1000000000000000000)
  k0 := (1009344953173327/250000000000000000)
  k6 := (3081398548560457/250000000000000000)
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
  norm_lower := (window_guards (n := 12342) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12342) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((27066107/250000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12342 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12342) internalParameters :=
  BstLean.Part227.worldPackage (n := 12342) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (27066107/250000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12342) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12342.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12342, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12342.frame := by
  exact frame.2.trans (by norm_num [Part259.world12342])

theorem moment_payment : internalParameters.moment ≤ Part259.world12342.moment := by
  exact moment.2.trans (by norm_num [Part259.world12342])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (11884163/10000000000) ∧
    internalParameters.frame ≤ (630713262689/1000000000000) ∧
    internalParameters.moment ≤ (10153183649/1000000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12342) (Part259.world12342) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12342]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12342])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12342]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12342]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12342).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12342).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12342
#eval (do IO.println s!"P260 END 12342 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12343 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12343
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
    exp (-((mW 12343 : ℝ)*24686)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12343 : ℝ)*24686)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12343 : ℝ)*24686)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12343 : ℝ)*24686)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24686 (mW 12343) i /
      (rowEps i * e1MeanBounds 24686 (mW 12343) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24686 (mW 12343) (1/10^6) (1/10^7) rowEps ≤ (2096257/1000000000000) := by
  have hr : 0 ≤ firstRatio 24686 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24686 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24686) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12343 (1/10^6) (1/10^7) ((2096257/1000000000000))
      (712/10000) rowEps ≤ (27061559/250000000000) := by
  have hs : statisticsPayment ≤ (4075574927363/1000000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (104070659128321/1000000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12343 (1/10^6) (1/10^7) ((2096257/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 12343 : ℝ)*24686)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12343 : ℝ)*24686)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12343) (mW 12343)).real
      (goodDist 12343 (712/10000))ᶜ ≤ (27061559/250000000000) := by
  apply le_trans (concrete_distance_charge (n := 12343) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (2096257/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12343 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (364618676941/500000000000000000)
  k0 := (2018567243075067/500000000000000000)
  k6 := (19257960764401/1562500000000000)
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
  norm_lower := (window_guards (n := 12343) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12343) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((27061559/250000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12343 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12343) internalParameters :=
  BstLean.Part227.worldPackage (n := 12343) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (27061559/250000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12343) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12343.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12343, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12343.frame := by
  exact frame.2.trans (by norm_num [Part259.world12343])

theorem moment_payment : internalParameters.moment ≤ Part259.world12343.moment := by
  exact moment.2.trans (by norm_num [Part259.world12343])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1188368297/1000000000000) ∧
    internalParameters.frame ≤ (630698567003/1000000000000) ∧
    internalParameters.moment ≤ (101510311/10000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12343) (Part259.world12343) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12343]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12343])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12343]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12343]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12343).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12343).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12343
#eval (do IO.println s!"P260 END 12343 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12344 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12344
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
    exp (-((mW 12344 : ℝ)*24688)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12344 : ℝ)*24688)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12344 : ℝ)*24688)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12344 : ℝ)*24688)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24688 (mW 12344) i /
      (rowEps i * e1MeanBounds 24688 (mW 12344) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24688 (mW 12344) (1/10^6) (1/10^7) rowEps ≤ (419217/200000000000) := by
  have hr : 0 ≤ firstRatio 24688 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24688 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24688) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12344 (1/10^6) (1/10^7) ((419217/200000000000))
      (712/10000) rowEps ≤ (2705701/25000000000) := by
  have hs : statisticsPayment ≤ (814980578299/200000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (52026567656557/500000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12344 (1/10^6) (1/10^7) ((419217/200000000000))
      (712/10000) rowEps =
      exp (-((mW 12344 : ℝ)*24688)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12344 : ℝ)*24688)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12344) (mW 12344)).real
      (goodDist 12344 (712/10000))ᶜ ≤ (2705701/25000000000) := by
  apply le_trans (concrete_distance_charge (n := 12344) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (419217/200000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12344 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (364574370643/500000000000000000)
  k0 := (4036889194384967/1000000000000000000)
  k6 := (3081148911216623/250000000000000000)
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
  norm_lower := (window_guards (n := 12344) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12344) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((2705701/25000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12344 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12344) internalParameters :=
  BstLean.Part227.worldPackage (n := 12344) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (2705701/25000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12344) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12344.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12344, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12344.frame := by
  exact frame.2.trans (by norm_num [Part259.world12344])

theorem moment_payment : internalParameters.moment ≤ Part259.world12344.moment := by
  exact moment.2.trans (by norm_num [Part259.world12344])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1188320307/1000000000000) ∧
    internalParameters.frame ≤ (630683873759/1000000000000) ∧
    internalParameters.moment ≤ (2537219797/250000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12344) (Part259.world12344) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12344]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12344])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12344]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12344]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12344).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12344).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12344
#eval (do IO.println s!"P260 END 12344 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12345 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12345
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
    exp (-((mW 12345 : ℝ)*24690)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12345 : ℝ)*24690)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12345 : ℝ)*24690)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12345 : ℝ)*24690)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24690 (mW 12345) i /
      (rowEps i * e1MeanBounds 24690 (mW 12345) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24690 (mW 12345) (1/10^6) (1/10^7) rowEps ≤ (1047957/500000000000) := by
  have hr : 0 ≤ firstRatio 24690 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24690 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24690) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12345 (1/10^6) (1/10^7) ((1047957/500000000000))
      (712/10000) rowEps ≤ (108210129/1000000000000) := by
  have hs : statisticsPayment ≤ (4074231061293/1000000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (10403589669047/100000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12345 (1/10^6) (1/10^7) ((1047957/500000000000))
      (712/10000) rowEps =
      exp (-((mW 12345 : ℝ)*24690)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12345 : ℝ)*24690)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12345) (mW 12345)).real
      (goodDist 12345 (712/10000))ᶜ ≤ (108210129/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 12345) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (1047957/500000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12345 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (182265036659/250000000000000000)
  k0 := (2018321968697921/500000000000000000)
  k6 := (6162048230589549/500000000000000000)
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
  norm_lower := (window_guards (n := 12345) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12345) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((108210129/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12345 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12345) internalParameters :=
  BstLean.Part227.worldPackage (n := 12345) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (108210129/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12345) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12345.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12345, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12345.frame := by
  exact frame.2.trans (by norm_num [Part259.world12345])

theorem moment_payment : internalParameters.moment ≤ Part259.world12345.moment := by
  exact moment.2.trans (by norm_num [Part259.world12345])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (118827233/100000000000) ∧
    internalParameters.frame ≤ (126133836591/200000000000) ∧
    internalParameters.moment ≤ (5073363957/500000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12345) (Part259.world12345) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12345]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12345])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12345]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12345]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12345).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12345).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12345
#eval (do IO.println s!"P260 END 12345 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12346 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12346
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
    exp (-((mW 12346 : ℝ)*24692)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12346 : ℝ)*24692)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12346 : ℝ)*24692)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12346 : ℝ)*24692)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24692 (mW 12346) i /
      (rowEps i * e1MeanBounds 24692 (mW 12346) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24692 (mW 12346) (1/10^6) (1/10^7) rowEps ≤ (1047871/500000000000) := by
  have hr : 0 ≤ firstRatio 24692 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24692 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24692) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12346 (1/10^6) (1/10^7) ((1047871/500000000000))
      (712/10000) rowEps ≤ (54095963/500000000000) := by
  have hs : statisticsPayment ≤ (407355943667/100000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (104018365393641/1000000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12346 (1/10^6) (1/10^7) ((1047871/500000000000))
      (712/10000) rowEps =
      exp (-((mW 12346 : ℝ)*24692)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12346 : ℝ)*24692)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12346) (mW 12346)).real
      (goodDist 12346 (712/10000))ᶜ ≤ (54095963/500000000000) := by
  apply le_trans (concrete_distance_charge (n := 12346) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (1047871/500000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12346 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (182242892481/250000000000000000)
  k0 := (80727974303339/20000000000000000)
  k6 := (12323597338142173/1000000000000000000)
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
  norm_lower := (window_guards (n := 12346) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12346) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((54095963/500000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12346 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12346) internalParameters :=
  BstLean.Part227.worldPackage (n := 12346) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (54095963/500000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12346) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12346.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12346, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12346.frame := by
  exact frame.2.trans (by norm_num [Part259.world12346])

theorem moment_payment : internalParameters.moment ≤ Part259.world12346.moment := by
  exact moment.2.trans (by norm_num [Part259.world12346])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (237644873/200000000000) ∧
    internalParameters.frame ≤ (630654494589/1000000000000) ∧
    internalParameters.moment ≤ (10144577277/1000000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12346) (Part259.world12346) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12346]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12346])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12346]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12346]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12346).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12346).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12346
#eval (do IO.println s!"P260 END 12346 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12347 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12347
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
    exp (-((mW 12347 : ℝ)*24694)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12347 : ℝ)*24694)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12347 : ℝ)*24694)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12347 : ℝ)*24694)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24694 (mW 12347) i /
      (rowEps i * e1MeanBounds 24694 (mW 12347) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24694 (mW 12347) (1/10^6) (1/10^7) rowEps ≤ (209557/100000000000) := by
  have hr : 0 ≤ firstRatio 24694 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24694 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24694) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12347 (1/10^6) (1/10^7) ((209557/100000000000))
      (712/10000) rowEps ≤ (2704343/25000000000) := by
  have hs : statisticsPayment ≤ (4072888017543/1000000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (1625012974579/15625000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12347 (1/10^6) (1/10^7) ((209557/100000000000))
      (712/10000) rowEps =
      exp (-((mW 12347 : ℝ)*24694)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12347 : ℝ)*24694)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12347) (mW 12347)).real
      (goodDist 12347 (712/10000))ᶜ ≤ (2704343/25000000000) := by
  apply le_trans (concrete_distance_charge (n := 12347) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (209557/100000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12347 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (182220752787/250000000000000000)
  k0 := (4036153527699089/1000000000000000000)
  k6 := (3080774568935859/250000000000000000)
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
  norm_lower := (window_guards (n := 12347) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12347) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((2704343/25000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12347 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12347) internalParameters :=
  BstLean.Part227.worldPackage (n := 12347) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (2704343/25000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12347) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12347.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12347, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12347.frame := by
  exact frame.2.trans (by norm_num [Part259.world12347])

theorem moment_payment : internalParameters.moment ≤ Part259.world12347.moment := by
  exact moment.2.trans (by norm_num [Part259.world12347])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (594088207/500000000000) ∧
    internalParameters.frame ≤ (630639808663/1000000000000) ∧
    internalParameters.moment ≤ (2535606819/250000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12347) (Part259.world12347) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12347]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12347])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12347]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12347]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12347).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12347).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12347
#eval (do IO.println s!"P260 END 12347 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12348 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12348
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
    exp (-((mW 12348 : ℝ)*24696)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12348 : ℝ)*24696)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12348 : ℝ)*24696)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12348 : ℝ)*24696)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24696 (mW 12348) i /
      (rowEps i * e1MeanBounds 24696 (mW 12348) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24696 (mW 12348) (1/10^6) (1/10^7) rowEps ≤ (2095399/1000000000000) := by
  have hr : 0 ≤ firstRatio 24696 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24696 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24696) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12348 (1/10^6) (1/10^7) ((2095399/1000000000000))
      (712/10000) rowEps ≤ (108155799/1000000000000) := by
  have hs : statisticsPayment ≤ (162888672153/40000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (25995895119043/250000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12348 (1/10^6) (1/10^7) ((2095399/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 12348 : ℝ)*24696)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12348 : ℝ)*24696)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12348) (mW 12348)).real
      (goodDist 12348 (712/10000))ᶜ ≤ (108155799/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 12348) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (2095399/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12348 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (728794470301/1000000000000000000)
  k0 := (4035908374979213/1000000000000000000)
  k6 := (3080649818492653/250000000000000000)
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
  norm_lower := (window_guards (n := 12348) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12348) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((108155799/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12348 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12348) internalParameters :=
  BstLean.Part227.worldPackage (n := 12348) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (108155799/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12348) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12348.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12348, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12348.frame := by
  exact frame.2.trans (by norm_num [Part259.world12348])

theorem moment_payment : internalParameters.moment ≤ Part259.world12348.moment := by
  exact moment.2.trans (by norm_num [Part259.world12348])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1188128477/1000000000000) ∧
    internalParameters.frame ≤ (25225005007/40000000000) ∧
    internalParameters.moment ≤ (10140277913/1000000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12348) (Part259.world12348) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12348]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12348])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12348]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12348]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12348).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12348).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12348
#eval (do IO.println s!"P260 END 12348 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12349 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12349
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
    exp (-((mW 12349 : ℝ)*24698)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12349 : ℝ)*24698)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12349 : ℝ)*24698)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12349 : ℝ)*24698)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24698 (mW 12349) i /
      (rowEps i * e1MeanBounds 24698 (mW 12349) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24698 (mW 12349) (1/10^6) (1/10^7) rowEps ≤ (2095227/1000000000000) := by
  have hr : 0 ≤ firstRatio 24698 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24698 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24698) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12349 (1/10^6) (1/10^7) ((2095227/1000000000000))
      (712/10000) rowEps ≤ (21627517/200000000000) := by
  have hs : statisticsPayment ≤ (4071545795431/1000000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (51983018995069/500000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12349 (1/10^6) (1/10^7) ((2095227/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 12349 : ℝ)*24698)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12349 : ℝ)*24698)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12349) (mW 12349)).real
      (goodDist 12349 (712/10000))ᶜ ≤ (21627517/200000000000) := by
  apply le_trans (concrete_distance_charge (n := 12349) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (2095227/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12349 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (364352973689/500000000000000000)
  k0 := (4035663256999809/1000000000000000000)
  k6 := (492884013312457/40000000000000000)
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
  norm_lower := (window_guards (n := 12349) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12349) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((21627517/200000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12349 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12349) internalParameters :=
  BstLean.Part227.worldPackage (n := 12349) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (21627517/200000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12349) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12349.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12349, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12349.frame := by
  exact frame.2.trans (by norm_num [Part259.world12349])

theorem moment_payment : internalParameters.moment ≤ Part259.world12349.moment := by
  exact moment.2.trans (by norm_num [Part259.world12349])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (148510069/125000000000) ∧
    internalParameters.frame ≤ (5044883553/8000000000) ∧
    internalParameters.moment ≤ (2027625837/200000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12349) (Part259.world12349) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12349]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12349])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12349]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12349]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12349).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12349).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12349
#eval (do IO.println s!"P260 END 12349 6 {← IO.monoMsNow}" : IO Unit)
