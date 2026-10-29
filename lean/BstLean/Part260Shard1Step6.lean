import BstLean.Part260Shard1Step5
#eval (do IO.println s!"P260 START 12250 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12250
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
    exp (-((mW 12250 : ℝ)*24500)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12250 : ℝ)*24500)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12250 : ℝ)*24500)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12250 : ℝ)*24500)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24500 (mW 12250) i /
      (rowEps i * e1MeanBounds 24500 (mW 12250) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24500 (mW 12250) (1/10^6) (1/10^7) rowEps ≤ (2112347/1000000000000) := by
  have hr : 0 ≤ firstRatio 24500 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24500 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24500) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12250 (1/10^6) (1/10^7) ((2112347/1000000000000))
      (712/10000) rowEps ≤ (13743759/125000000000) := by
  have hs : statisticsPayment ≤ (4138985182231/1000000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (52855542890917/500000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12250 (1/10^6) (1/10^7) ((2112347/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 12250 : ℝ)*24500)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12250 : ℝ)*24500)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12250) (mW 12250)).real
      (goodDist 12250 (712/10000))ᶜ ≤ (13743759/125000000000) := by
  apply le_trans (concrete_distance_charge (n := 12250) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (2112347/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12250 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (9219468397/12500000000000000)
  k0 := (4060099690135207/1000000000000000000)
  k6 := (6185895741317419/500000000000000000)
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
  norm_lower := (window_guards (n := 12250) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12250) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((13743759/125000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12250 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12250) internalParameters :=
  BstLean.Part227.worldPackage (n := 12250) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (13743759/125000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12250) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12250.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12250, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12250.frame := by
  exact frame.2.trans (by norm_num [Part259.world12250])

theorem moment_payment : internalParameters.moment ≤ Part259.world12250.moment := by
  exact moment.2.trans (by norm_num [Part259.world12250])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (298222307/250000000000) ∧
    internalParameters.frame ≤ (158018948639/250000000000) ∧
    internalParameters.moment ≤ (5176989227/500000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12250) (Part259.world12250) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12250]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12250])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12250]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12250]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12250).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12250).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12250
#eval (do IO.println s!"P260 END 12250 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12251 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12251
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
    exp (-((mW 12251 : ℝ)*24502)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12251 : ℝ)*24502)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12251 : ℝ)*24502)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12251 : ℝ)*24502)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24502 (mW 12251) i /
      (rowEps i * e1MeanBounds 24502 (mW 12251) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24502 (mW 12251) (1/10^6) (1/10^7) rowEps ≤ (2112173/1000000000000) := by
  have hr : 0 ≤ firstRatio 24502 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24502 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24502) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12251 (1/10^6) (1/10^7) ((2112173/1000000000000))
      (712/10000) rowEps ≤ (109931631/1000000000000) := by
  have hs : statisticsPayment ≤ (2069146820221/500000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (105693335591747/1000000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12251 (1/10^6) (1/10^7) ((2112173/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 12251 : ℝ)*24502)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12251 : ℝ)*24502)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12251) (mW 12251)).real
      (goodDist 12251 (712/10000))ᶜ ≤ (109931631/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 12251) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (2112173/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12251 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (147493433563/200000000000000000)
  k0 := (4059851130357523/1000000000000000000)
  k6 := (1546410817808551/125000000000000000)
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
  norm_lower := (window_guards (n := 12251) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12251) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((109931631/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12251 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12251) internalParameters :=
  BstLean.Part227.worldPackage (n := 12251) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (109931631/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12251) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12251.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12251, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12251.frame := by
  exact frame.2.trans (by norm_num [Part259.world12251])

theorem moment_payment : internalParameters.moment ≤ Part259.world12251.moment := by
  exact moment.2.trans (by norm_num [Part259.world12251])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (29821/25000000) ∧
    internalParameters.frame ≤ (632060871527/1000000000000) ∧
    internalParameters.moment ≤ (5175883099/500000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12251) (Part259.world12251) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12251]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12251])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12251]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12251]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12251).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12251).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12251
#eval (do IO.println s!"P260 END 12251 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12252 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12252
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
    exp (-((mW 12252 : ℝ)*24504)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12252 : ℝ)*24504)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12252 : ℝ)*24504)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12252 : ℝ)*24504)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24504 (mW 12252) i /
      (rowEps i * e1MeanBounds 24504 (mW 12252) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24504 (mW 12252) (1/10^6) (1/10^7) rowEps ≤ (1055999/500000000000) := by
  have hr : 0 ≤ firstRatio 24504 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24504 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24504) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12252 (1/10^6) (1/10^7) ((1055999/500000000000))
      (712/10000) rowEps ≤ (54956447/500000000000) := by
  have hs : statisticsPayment ≤ (4137602312447/1000000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (105675290199323/1000000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12252 (1/10^6) (1/10^7) ((1055999/500000000000))
      (712/10000) rowEps =
      exp (-((mW 12252 : ℝ)*24504)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12252 : ℝ)*24504)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12252) (mW 12252)).real
      (goodDist 12252 (712/10000))ᶜ ≤ (54956447/500000000000) := by
  apply le_trans (concrete_distance_charge (n := 12252) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (1055999/500000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12252 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (92172110287/125000000000000000)
  k0 := (811920521216593/200000000000000000)
  k6 := (2474156332824511/200000000000000000)
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
  norm_lower := (window_guards (n := 12252) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12252) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((54956447/500000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12252 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12252) internalParameters :=
  BstLean.Part227.worldPackage (n := 12252) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (54956447/500000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12252) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12252.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12252, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12252.frame := by
  exact frame.2.trans (by norm_num [Part259.world12252])

theorem moment_payment : internalParameters.moment ≤ Part259.world12252.moment := by
  exact moment.2.trans (by norm_num [Part259.world12252])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (596395393/500000000000) ∧
    internalParameters.frame ≤ (632045950999/1000000000000) ∧
    internalParameters.moment ≤ (10349554603/1000000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12252) (Part259.world12252) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12252]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12252])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12252]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12252]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12252).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12252).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12252
#eval (do IO.println s!"P260 END 12252 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12253 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12253
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
    exp (-((mW 12253 : ℝ)*24506)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12253 : ℝ)*24506)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12253 : ℝ)*24506)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12253 : ℝ)*24506)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24506 (mW 12253) i /
      (rowEps i * e1MeanBounds 24506 (mW 12253) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24506 (mW 12253) (1/10^6) (1/10^7) rowEps ≤ (131989/62500000000) := by
  have hr : 0 ≤ firstRatio 24506 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24506 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24506) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12253 (1/10^6) (1/10^7) ((131989/62500000000))
      (712/10000) rowEps ≤ (21978889/200000000000) := by
  have hs : statisticsPayment ≤ (1034227799539/250000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (52828766137887/500000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12253 (1/10^6) (1/10^7) ((131989/62500000000))
      (712/10000) rowEps =
      exp (-((mW 12253 : ℝ)*24506)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12253 : ℝ)*24506)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12253) (mW 12253)).real
      (goodDist 12253 (712/10000))ᶜ ≤ (21978889/200000000000) := by
  apply le_trans (concrete_distance_charge (n := 12253) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (131989/62500000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12253 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (737286615197/1000000000000000000)
  k0 := (4059354117301539/1000000000000000000)
  k6 := (1546284605948083/125000000000000000)
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
  norm_lower := (window_guards (n := 12253) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12253) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((21978889/200000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12253 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12253) internalParameters :=
  BstLean.Part227.worldPackage (n := 12253) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (21978889/200000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12253) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12253.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12253, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12253.frame := by
  exact frame.2.trans (by norm_num [Part259.world12253])

theorem moment_payment : internalParameters.moment ≤ Part259.world12253.moment := by
  exact moment.2.trans (by norm_num [Part259.world12253])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (596370793/500000000000) ∧
    internalParameters.frame ≤ (158007758243/250000000000) ∧
    internalParameters.moment ≤ (10347343667/1000000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12253) (Part259.world12253) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12253]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12253])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12253]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12253]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12253).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12253).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12253
#eval (do IO.println s!"P260 END 12253 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12254 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12254
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
    exp (-((mW 12254 : ℝ)*24508)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12254 : ℝ)*24508)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12254 : ℝ)*24508)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12254 : ℝ)*24508)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24508 (mW 12254) i /
      (rowEps i * e1MeanBounds 24508 (mW 12254) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24508 (mW 12254) (1/10^6) (1/10^7) rowEps ≤ (42233/20000000000) := by
  have hr : 0 ≤ firstRatio 24508 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24508 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24508) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12254 (1/10^6) (1/10^7) ((42233/20000000000))
      (712/10000) rowEps ≤ (13734499/125000000000) := by
  have hs : statisticsPayment ≤ (103405507437/25000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (52819885238413/500000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12254 (1/10^6) (1/10^7) ((42233/20000000000))
      (712/10000) rowEps =
      exp (-((mW 12254 : ℝ)*24508)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12254 : ℝ)*24508)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12254) (mW 12254)).real
      (goodDist 12254 (712/10000))ᶜ ≤ (13734499/125000000000) := by
  apply le_trans (concrete_distance_charge (n := 12254) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (42233/20000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12254 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (147439273303/200000000000000000)
  k0 := (2029552832005751/500000000000000000)
  k6 := (12369772092842127/1000000000000000000)
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
  norm_lower := (window_guards (n := 12254) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12254) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((13734499/125000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12254 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12254) internalParameters :=
  BstLean.Part227.worldPackage (n := 12254) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (13734499/125000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12254) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12254.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12254, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12254.frame := by
  exact frame.2.trans (by norm_num [Part259.world12254])

theorem moment_payment : internalParameters.moment ≤ Part259.world12254.moment := by
  exact moment.2.trans (by norm_num [Part259.world12254])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (596346199/500000000000) ∧
    internalParameters.frame ≤ (158004029361/250000000000) ∧
    internalParameters.moment ≤ (646570837/62500000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12254) (Part259.world12254) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12254]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12254])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12254]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12254]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12254).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12254).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12254
#eval (do IO.println s!"P260 END 12254 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12255 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12255
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
    exp (-((mW 12255 : ℝ)*24510)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12255 : ℝ)*24510)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12255 : ℝ)*24510)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12255 : ℝ)*24510)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24510 (mW 12255) i /
      (rowEps i * e1MeanBounds 24510 (mW 12255) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24510 (mW 12255) (1/10^6) (1/10^7) rowEps ≤ (84459/40000000000) := by
  have hr : 0 ≤ firstRatio 24510 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24510 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24510) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12255 (1/10^6) (1/10^7) ((84459/40000000000))
      (712/10000) rowEps ≤ (21971449/200000000000) := by
  have hs : statisticsPayment ≤ (413552961033/100000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (4224868542489/40000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12255 (1/10^6) (1/10^7) ((84459/40000000000))
      (712/10000) rowEps =
      exp (-((mW 12255 : ℝ)*24510)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12255 : ℝ)*24510)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12255) (mW 12255)).real
      (goodDist 12255 (712/10000))ᶜ ≤ (21971449/200000000000) := by
  apply le_trans (concrete_distance_charge (n := 12255) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (84459/40000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12255 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (368553068121/500000000000000000)
  k0 := (2029428623098673/500000000000000000)
  k6 := (386539606246323/31250000000000000)
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
  norm_lower := (window_guards (n := 12255) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12255) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((21971449/200000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12255 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12255) internalParameters :=
  BstLean.Part227.worldPackage (n := 12255) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (21971449/200000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12255) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12255.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12255, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12255.frame := by
  exact frame.2.trans (by norm_num [Part259.world12255])

theorem moment_payment : internalParameters.moment ≤ Part259.world12255.moment := by
  exact moment.2.trans (by norm_num [Part259.world12255])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (47705729/40000000000) ∧
    internalParameters.frame ≤ (9875018819/15625000000) ∧
    internalParameters.moment ≤ (20201023/1953125000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12255) (Part259.world12255) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12255]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12255])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12255]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12255]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12255).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12255).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12255
#eval (do IO.println s!"P260 END 12255 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12256 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12256
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
    exp (-((mW 12256 : ℝ)*24512)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12256 : ℝ)*24512)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12256 : ℝ)*24512)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12256 : ℝ)*24512)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24512 (mW 12256) i /
      (rowEps i * e1MeanBounds 24512 (mW 12256) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24512 (mW 12256) (1/10^6) (1/10^7) rowEps ≤ (2111301/1000000000000) := by
  have hr : 0 ≤ firstRatio 24512 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24512 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24512) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12256 (1/10^6) (1/10^7) ((2111301/1000000000000))
      (712/10000) rowEps ≤ (21967757/200000000000) := by
  have hs : statisticsPayment ≤ (826967827323/200000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (10560394404659/100000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12256 (1/10^6) (1/10^7) ((2111301/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 12256 : ℝ)*24512)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12256 : ℝ)*24512)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12256) (mW 12256)).real
      (goodDist 12256 (712/10000))ᶜ ≤ (21967757/200000000000) := by
  apply le_trans (concrete_distance_charge (n := 12256) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (2111301/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12256 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (368507962187/500000000000000000)
  k0 := (4058608863854573/1000000000000000000)
  k6 := (12368762768692689/1000000000000000000)
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
  norm_lower := (window_guards (n := 12256) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12256) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((21967757/200000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12256 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12256) internalParameters :=
  BstLean.Part227.worldPackage (n := 12256) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (21967757/200000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12256) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12256.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12256, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12256.frame := by
  exact frame.2.trans (by norm_num [Part259.world12256])

theorem moment_payment : internalParameters.moment ≤ Part259.world12256.moment := by
  exact moment.2.trans (by norm_num [Part259.world12256])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (238518813/200000000000) ∧
    internalParameters.frame ≤ (315993146943/500000000000) ∧
    internalParameters.moment ≤ (10340714819/1000000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12256) (Part259.world12256) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12256]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12256])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12256]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12256]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12256).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12256).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12256
#eval (do IO.println s!"P260 END 12256 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12257 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12257
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
    exp (-((mW 12257 : ℝ)*24514)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12257 : ℝ)*24514)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12257 : ℝ)*24514)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12257 : ℝ)*24514)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24514 (mW 12257) i /
      (rowEps i * e1MeanBounds 24514 (mW 12257) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24514 (mW 12257) (1/10^6) (1/10^7) rowEps ≤ (2111127/1000000000000) := by
  have hr : 0 ≤ firstRatio 24514 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24514 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24514) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12257 (1/10^6) (1/10^7) ((2111127/1000000000000))
      (712/10000) rowEps ≤ (109820321/1000000000000) := by
  have hs : statisticsPayment ≤ (516768609531/125000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (21117234132781/200000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12257 (1/10^6) (1/10^7) ((2111127/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 12257 : ℝ)*24514)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12257 : ℝ)*24514)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12257) (mW 12257)).real
      (goodDist 12257 (712/10000))ᶜ ≤ (109820321/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 12257) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (2111127/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12257 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (368462865453/500000000000000000)
  k0 := (2029180258487963/500000000000000000)
  k6 := (12368258199260587/1000000000000000000)
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
  norm_lower := (window_guards (n := 12257) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12257) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((109820321/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12257 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12257) internalParameters :=
  BstLean.Part227.worldPackage (n := 12257) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (109820321/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12257) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12257.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12257, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12257.frame := by
  exact frame.2.trans (by norm_num [Part259.world12257])

theorem moment_payment : internalParameters.moment ≤ Part259.world12257.moment := by
  exact moment.2.trans (by norm_num [Part259.world12257])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (596272459/500000000000) ∧
    internalParameters.frame ≤ (126394277171/200000000000) ∧
    internalParameters.moment ≤ (5169253261/500000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12257) (Part259.world12257) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12257]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12257])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12257]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12257]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12257).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12257).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12257
#eval (do IO.println s!"P260 END 12257 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12258 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12258
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
    exp (-((mW 12258 : ℝ)*24516)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12258 : ℝ)*24516)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12258 : ℝ)*24516)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12258 : ℝ)*24516)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24516 (mW 12258) i /
      (rowEps i * e1MeanBounds 24516 (mW 12258) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24516 (mW 12258) (1/10^6) (1/10^7) rowEps ≤ (2110953/1000000000000) := by
  have hr : 0 ≤ firstRatio 24516 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24516 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24516) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12258 (1/10^6) (1/10^7) ((2110953/1000000000000))
      (712/10000) rowEps ≤ (54900927/500000000000) := by
  have hs : statisticsPayment ≤ (2066729414569/500000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (105568393416949/1000000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12258 (1/10^6) (1/10^7) ((2110953/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 12258 : ℝ)*24516)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12258 : ℝ)*24516)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12258) (mW 12258)).real
      (goodDist 12258 (712/10000))ᶜ ≤ (54900927/500000000000) := by
  apply le_trans (concrete_distance_charge (n := 12258) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (2110953/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12258 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (736835555833/1000000000000000000)
  k0 := (1014528051388537/250000000000000000)
  k6 := (6183876845786717/500000000000000000)
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
  norm_lower := (window_guards (n := 12258) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12258) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((54900927/500000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12258 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12258) internalParameters :=
  BstLean.Part227.worldPackage (n := 12258) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (54900927/500000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12258) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12258.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12258, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12258.frame := by
  exact frame.2.trans (by norm_num [Part259.world12258])

theorem moment_payment : internalParameters.moment ≤ Part259.world12258.moment := by
  exact moment.2.trans (by norm_num [Part259.world12258])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (238499157/200000000000) ∧
    internalParameters.frame ≤ (1974864001/3125000000) ∧
    internalParameters.moment ≤ (10336298883/1000000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12258) (Part259.world12258) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12258]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12258])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12258]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12258]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12258).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12258).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12258
#eval (do IO.println s!"P260 END 12258 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12259 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12259
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
    exp (-((mW 12259 : ℝ)*24518)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12259 : ℝ)*24518)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12259 : ℝ)*24518)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12259 : ℝ)*24518)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24518 (mW 12259) i /
      (rowEps i * e1MeanBounds 24518 (mW 12259) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24518 (mW 12259) (1/10^6) (1/10^7) rowEps ≤ (2110779/1000000000000) := by
  have hr : 0 ≤ firstRatio 24518 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24518 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24518) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12259 (1/10^6) (1/10^7) ((2110779/1000000000000))
      (712/10000) rowEps ≤ (109783383/1000000000000) := by
  have hs : statisticsPayment ≤ (4132768995197/1000000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (105550612308499/1000000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12259 (1/10^6) (1/10^7) ((2110779/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 12259 : ℝ)*24518)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12259 : ℝ)*24518)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12259) (mW 12259)).real
      (goodDist 12259 (712/10000))ᶜ ≤ (109783383/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 12259) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (2110779/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12259 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (184186349787/250000000000000000)
  k0 := (507232991197059/125000000000000000)
  k6 := (6183624622809319/500000000000000000)
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
  norm_lower := (window_guards (n := 12259) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12259) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((109783383/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12259 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12259) internalParameters :=
  BstLean.Part227.worldPackage (n := 12259) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (109783383/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12259) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12259.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12259, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12259.frame := by
  exact frame.2.trans (by norm_num [Part259.world12259])

theorem moment_payment : internalParameters.moment ≤ Part259.world12259.moment := by
  exact moment.2.trans (by norm_num [Part259.world12259])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (238489333/200000000000) ∧
    internalParameters.frame ≤ (315970788641/500000000000) ∧
    internalParameters.moment ≤ (10334091903/1000000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12259) (Part259.world12259) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12259]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12259])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12259]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12259]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12259).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12259).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12259
#eval (do IO.println s!"P260 END 12259 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12260 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12260
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
    exp (-((mW 12260 : ℝ)*24520)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12260 : ℝ)*24520)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12260 : ℝ)*24520)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12260 : ℝ)*24520)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24520 (mW 12260) i /
      (rowEps i * e1MeanBounds 24520 (mW 12260) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24520 (mW 12260) (1/10^6) (1/10^7) rowEps ≤ (422121/200000000000) := by
  have hr : 0 ≤ firstRatio 24520 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24520 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24520) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12260 (1/10^6) (1/10^7) ((422121/200000000000))
      (712/10000) rowEps ≤ (27441227/250000000000) := by
  have hs : statisticsPayment ≤ (826415874867/200000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (21106565468267/200000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12260 (1/10^6) (1/10^7) ((422121/200000000000))
      (712/10000) rowEps =
      exp (-((mW 12260 : ℝ)*24520)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12260 : ℝ)*24520)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12260) (mW 12260)).real
      (goodDist 12260 (712/10000))ᶜ ≤ (27441227/250000000000) := by
  apply le_trans (concrete_distance_charge (n := 12260) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (422121/200000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12260 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (46040953803/62500000000000000)
  k0 := (202880784452057/50000000000000000)
  k6 := (1236674486138361/100000000000000000)
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
  norm_lower := (window_guards (n := 12260) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12260) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((27441227/250000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12260 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12260) internalParameters :=
  BstLean.Part227.worldPackage (n := 12260) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (27441227/250000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12260) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12260.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12260, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12260.frame := by
  exact frame.2.trans (by norm_num [Part259.world12260])

theorem moment_payment : internalParameters.moment ≤ Part259.world12260.moment := by
  exact moment.2.trans (by norm_num [Part259.world12260])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1192397559/1000000000000) ∧
    internalParameters.frame ≤ (31596333837/50000000000) ∧
    internalParameters.moment ≤ (10331885581/1000000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12260) (Part259.world12260) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12260]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12260])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12260]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12260]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12260).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12260).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12260
#eval (do IO.println s!"P260 END 12260 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12261 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12261
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
    exp (-((mW 12261 : ℝ)*24522)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12261 : ℝ)*24522)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12261 : ℝ)*24522)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12261 : ℝ)*24522)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24522 (mW 12261) i /
      (rowEps i * e1MeanBounds 24522 (mW 12261) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24522 (mW 12261) (1/10^6) (1/10^7) rowEps ≤ (2110431/1000000000000) := by
  have hr : 0 ≤ firstRatio 24522 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24522 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24522) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12261 (1/10^6) (1/10^7) ((2110431/1000000000000))
      (712/10000) rowEps ≤ (10974643/100000000000) := by
  have hs : statisticsPayment ≤ (4131389966463/1000000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (26378759629559/250000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12261 (1/10^6) (1/10^7) ((2110431/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 12261 : ℝ)*24522)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12261 : ℝ)*24522)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12261) (mW 12261)).real
      (goodDist 12261 (712/10000))ᶜ ≤ (10974643/100000000000) := by
  apply le_trans (concrete_distance_charge (n := 12261) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (2110431/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12261 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (368282570463/500000000000000000)
  k0 := (4057367483935379/1000000000000000000)
  k6 := (6183120269427883/500000000000000000)
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
  norm_lower := (window_guards (n := 12261) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12261) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((10974643/100000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12261 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12261) internalParameters :=
  BstLean.Part227.worldPackage (n := 12261) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (10974643/100000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12261) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12261.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12261, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12261.frame := by
  exact frame.2.trans (by norm_num [Part259.world12261])

theorem moment_payment : internalParameters.moment ≤ Part259.world12261.moment := by
  exact moment.2.trans (by norm_num [Part259.world12261])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1192348467/1000000000000) ∧
    internalParameters.frame ≤ (631911778693/1000000000000) ∧
    internalParameters.moment ≤ (10329679917/1000000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12261) (Part259.world12261) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12261]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12261])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12261]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12261]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12261).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12261).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12261
#eval (do IO.println s!"P260 END 12261 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12262 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12262
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
    exp (-((mW 12262 : ℝ)*24524)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12262 : ℝ)*24524)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12262 : ℝ)*24524)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12262 : ℝ)*24524)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24524 (mW 12262) i /
      (rowEps i * e1MeanBounds 24524 (mW 12262) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24524 (mW 12262) (1/10^6) (1/10^7) rowEps ≤ (2110257/1000000000000) := by
  have hr : 0 ≤ firstRatio 24524 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24524 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24524) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12262 (1/10^6) (1/10^7) ((2110257/1000000000000))
      (712/10000) rowEps ≤ (27431987/250000000000) := by
  have hs : statisticsPayment ≤ (1032675192873/250000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (52748622920993/500000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12262 (1/10^6) (1/10^7) ((2110257/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 12262 : ℝ)*24524)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12262 : ℝ)*24524)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12262) (mW 12262)).real
      (goodDist 12262 (712/10000))ᶜ ≤ (27431987/250000000000) := by
  apply le_trans (concrete_distance_charge (n := 12262) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (2110257/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12262 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (368237519689/500000000000000000)
  k0 := (4057119314254673/1000000000000000000)
  k6 := (494629451120901/40000000000000000)
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
  norm_lower := (window_guards (n := 12262) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12262) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((27431987/250000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12262 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12262) internalParameters :=
  BstLean.Part227.worldPackage (n := 12262) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (27431987/250000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12262) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12262.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12262, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12262.frame := by
  exact frame.2.trans (by norm_num [Part259.world12262])

theorem moment_payment : internalParameters.moment ≤ Part259.world12262.moment := by
  exact moment.2.trans (by norm_num [Part259.world12262])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (298074847/250000000000) ∧
    internalParameters.frame ≤ (31594844157/50000000000) ∧
    internalParameters.moment ≤ (10327474911/1000000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12262) (Part259.world12262) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12262]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12262])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12262]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12262]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12262).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12262).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12262
#eval (do IO.println s!"P260 END 12262 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12263 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12263
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
    exp (-((mW 12263 : ℝ)*24526)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12263 : ℝ)*24526)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12263 : ℝ)*24526)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12263 : ℝ)*24526)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24526 (mW 12263) i /
      (rowEps i * e1MeanBounds 24526 (mW 12263) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24526 (mW 12263) (1/10^6) (1/10^7) rowEps ≤ (2110083/1000000000000) := by
  have hr : 0 ≤ firstRatio 24526 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24526 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24526) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12263 (1/10^6) (1/10^7) ((2110083/1000000000000))
      (712/10000) rowEps ≤ (109709463/1000000000000) := by
  have hs : statisticsPayment ≤ (4130011789333/1000000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (52739724657683/500000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12263 (1/10^6) (1/10^7) ((2110083/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 12263 : ℝ)*24526)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12263 : ℝ)*24526)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12263) (mW 12263)).real
      (goodDist 12263 (712/10000))ᶜ ≤ (109709463/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 12263) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (2110083/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12263 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (368192478099/500000000000000000)
  k0 := (811374235997799/200000000000000000)
  k6 := (3091308019717827/250000000000000000)
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
  norm_lower := (window_guards (n := 12263) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12263) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((109709463/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12263 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12263) internalParameters :=
  BstLean.Part227.worldPackage (n := 12263) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (109709463/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12263) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12263.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12263, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12263.frame := by
  exact frame.2.trans (by norm_num [Part259.world12263])

theorem moment_payment : internalParameters.moment ≤ Part259.world12263.moment := by
  exact moment.2.trans (by norm_num [Part259.world12263])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (596125161/500000000000) ∧
    internalParameters.frame ≤ (315940995041/500000000000) ∧
    internalParameters.moment ≤ (10325270563/1000000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12263) (Part259.world12263) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12263]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12263])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12263]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12263]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12263).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12263).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12263
#eval (do IO.println s!"P260 END 12263 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12264 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12264
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
    exp (-((mW 12264 : ℝ)*24528)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12264 : ℝ)*24528)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12264 : ℝ)*24528)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12264 : ℝ)*24528)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24528 (mW 12264) i /
      (rowEps i * e1MeanBounds 24528 (mW 12264) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24528 (mW 12264) (1/10^6) (1/10^7) rowEps ≤ (2109909/1000000000000) := by
  have hr : 0 ≤ firstRatio 24528 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24528 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24528) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12264 (1/10^6) (1/10^7) ((2109909/1000000000000))
      (712/10000) rowEps ≤ (109690973/1000000000000) := by
  have hs : statisticsPayment ≤ (2064661509949/500000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (52730824470581/500000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12264 (1/10^6) (1/10^7) ((2109909/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 12264 : ℝ)*24528)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12264 : ℝ)*24528)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12264) (mW 12264)).real
      (goodDist 12264 (712/10000))ᶜ ≤ (109690973/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 12264) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (2109909/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12264 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (736294891381/1000000000000000000)
  k0 := (63384735642673/15625000000000000)
  k6 := (6182363970694771/500000000000000000)
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
  norm_lower := (window_guards (n := 12264) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12264) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((109690973/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12264 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12264) internalParameters :=
  BstLean.Part227.worldPackage (n := 12264) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (109690973/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12264) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12264.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12264, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12264.frame := by
  exact frame.2.trans (by norm_num [Part259.world12264])

theorem moment_payment : internalParameters.moment ≤ Part259.world12264.moment := by
  exact moment.2.trans (by norm_num [Part259.world12264])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (119220127/100000000000) ∧
    internalParameters.frame ≤ (631867099517/1000000000000) ∧
    internalParameters.moment ≤ (1290383359/125000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12264) (Part259.world12264) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12264]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12264])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12264]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12264]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12264).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12264).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12264
#eval (do IO.println s!"P260 END 12264 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12265 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12265
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
    exp (-((mW 12265 : ℝ)*24530)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12265 : ℝ)*24530)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12265 : ℝ)*24530)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12265 : ℝ)*24530)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24530 (mW 12265) i /
      (rowEps i * e1MeanBounds 24530 (mW 12265) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24530 (mW 12265) (1/10^6) (1/10^7) rowEps ≤ (421947/200000000000) := by
  have hr : 0 ≤ firstRatio 24530 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24530 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24530) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12265 (1/10^6) (1/10^7) ((421947/200000000000))
      (712/10000) rowEps ≤ (109672481/1000000000000) := by
  have hs : statisticsPayment ≤ (516079307887/125000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (52721922361079/500000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12265 (1/10^6) (1/10^7) ((421947/200000000000))
      (712/10000) rowEps =
      exp (-((mW 12265 : ℝ)*24530)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12265 : ℝ)*24530)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12265) (mW 12265)).real
      (goodDist 12265 (712/10000))ᶜ ≤ (109672481/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 12265) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (421947/200000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12265 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (736204844921/1000000000000000000)
  k0 := (405637501767087/100000000000000000)
  k6 := (12364223865564657/1000000000000000000)
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
  norm_lower := (window_guards (n := 12265) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12265) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((109672481/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12265 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12265) internalParameters :=
  BstLean.Part227.worldPackage (n := 12265) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (109672481/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12265) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12265.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12265, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12265.frame := by
  exact frame.2.trans (by norm_num [Part259.world12265])

theorem moment_payment : internalParameters.moment ≤ Part259.world12265.moment := by
  exact moment.2.trans (by norm_num [Part259.world12265])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1192152231/1000000000000) ∧
    internalParameters.frame ≤ (157963052861/250000000000) ∧
    internalParameters.moment ≤ (5160431919/500000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12265) (Part259.world12265) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12265]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12265])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12265]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12265]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12265).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12265).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12265
#eval (do IO.println s!"P260 END 12265 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12266 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12266
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
    exp (-((mW 12266 : ℝ)*24532)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12266 : ℝ)*24532)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12266 : ℝ)*24532)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12266 : ℝ)*24532)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24532 (mW 12266) i /
      (rowEps i * e1MeanBounds 24532 (mW 12266) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24532 (mW 12266) (1/10^6) (1/10^7) rowEps ≤ (2109561/1000000000000) := by
  have hr : 0 ≤ firstRatio 24532 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24532 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24532) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12266 (1/10^6) (1/10^7) ((2109561/1000000000000))
      (712/10000) rowEps ≤ (3426687/31250000000) := by
  have hs : statisticsPayment ≤ (103198652971/25000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (105426036661141/1000000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12266 (1/10^6) (1/10^7) ((2109561/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 12266 : ℝ)*24532)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12266 : ℝ)*24532)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12266) (mW 12266)).real
      (goodDist 12266 (712/10000))ᶜ ≤ (3426687/31250000000) := by
  apply le_trans (concrete_distance_charge (n := 12266) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (2109561/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12266 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (368057408407/500000000000000000)
  k0 := (507015873700483/125000000000000000)
  k6 := (2472743970276817/200000000000000000)
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
  norm_lower := (window_guards (n := 12266) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12266) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((3426687/31250000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12266 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12266) internalParameters :=
  BstLean.Part227.worldPackage (n := 12266) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (3426687/31250000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12266) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12266.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12266, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12266.frame := by
  exact frame.2.trans (by norm_num [Part259.world12266])

theorem moment_payment : internalParameters.moment ≤ Part259.world12266.moment := by
  exact moment.2.trans (by norm_num [Part259.world12266])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (596051603/500000000000) ∧
    internalParameters.frame ≤ (631837325863/1000000000000) ∧
    internalParameters.moment ≤ (10318661461/1000000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12266) (Part259.world12266) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12266]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12266])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12266]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12266]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12266).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12266).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12266
#eval (do IO.println s!"P260 END 12266 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12267 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12267
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
    exp (-((mW 12267 : ℝ)*24534)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12267 : ℝ)*24534)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12267 : ℝ)*24534)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12267 : ℝ)*24534)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24534 (mW 12267) i /
      (rowEps i * e1MeanBounds 24534 (mW 12267) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24534 (mW 12267) (1/10^6) (1/10^7) rowEps ≤ (2109387/1000000000000) := by
  have hr : 0 ≤ firstRatio 24534 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24534 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24534) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12267 (1/10^6) (1/10^7) ((2109387/1000000000000))
      (712/10000) rowEps ≤ (27408871/250000000000) := by
  have hs : statisticsPayment ≤ (4127257987041/1000000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (1054082247609/10000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12267 (1/10^6) (1/10^7) ((2109387/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 12267 : ℝ)*24534)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12267 : ℝ)*24534)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12267) (mW 12267)).real
      (goodDist 12267 (712/10000))ᶜ ≤ (27408871/250000000000) := by
  apply le_trans (concrete_distance_charge (n := 12267) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (2109387/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12267 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (147204961411/200000000000000000)
  k0 := (405587899692277/100000000000000000)
  k6 := (12363215898835263/1000000000000000000)
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
  norm_lower := (window_guards (n := 12267) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12267) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((27408871/250000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12267 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12267) internalParameters :=
  BstLean.Part227.worldPackage (n := 12267) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (27408871/250000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12267) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12267.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12267, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12267.frame := by
  exact frame.2.trans (by norm_num [Part259.world12267])

theorem moment_payment : internalParameters.moment ≤ Part259.world12267.moment := by
  exact moment.2.trans (by norm_num [Part259.world12267])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (596027097/500000000000) ∧
    internalParameters.frame ≤ (631822442773/1000000000000) ∧
    internalParameters.moment ≤ (515822987/50000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12267) (Part259.world12267) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12267]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12267])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12267]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12267]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12267).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12267).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12267
#eval (do IO.println s!"P260 END 12267 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12268 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12268
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
    exp (-((mW 12268 : ℝ)*24536)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12268 : ℝ)*24536)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12268 : ℝ)*24536)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12268 : ℝ)*24536)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24536 (mW 12268) i /
      (rowEps i * e1MeanBounds 24536 (mW 12268) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24536 (mW 12268) (1/10^6) (1/10^7) rowEps ≤ (2109213/1000000000000) := by
  have hr : 0 ≤ firstRatio 24536 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24536 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24536) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12268 (1/10^6) (1/10^7) ((2109213/1000000000000))
      (712/10000) rowEps ≤ (109616981/1000000000000) := by
  have hs : statisticsPayment ≤ (4126570067609/1000000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (52695204512111/500000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12268 (1/10^6) (1/10^7) ((2109213/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 12268 : ℝ)*24536)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12268 : ℝ)*24536)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12268) (mW 12268)).real
      (goodDist 12268 (712/10000))ᶜ ≤ (109616981/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 12268) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (2109213/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12268 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (735934815637/1000000000000000000)
  k0 := (4055631039614791/1000000000000000000)
  k6 := (386334750247051/31250000000000000)
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
  norm_lower := (window_guards (n := 12268) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12268) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((109616981/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12268 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12268) internalParameters :=
  BstLean.Part227.worldPackage (n := 12268) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (109616981/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12268) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12268.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12268, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12268.frame := by
  exact frame.2.trans (by norm_num [Part259.world12268])

theorem moment_payment : internalParameters.moment ≤ Part259.world12268.moment := by
  exact moment.2.trans (by norm_num [Part259.world12268])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (238401039/200000000000) ∧
    internalParameters.frame ≤ (315903781087/500000000000) ∧
    internalParameters.moment ≤ (2578564669/250000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12268) (Part259.world12268) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12268]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12268])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12268]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12268]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12268).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12268).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12268
#eval (do IO.println s!"P260 END 12268 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12269 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12269
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
    exp (-((mW 12269 : ℝ)*24538)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12269 : ℝ)*24538)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12269 : ℝ)*24538)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12269 : ℝ)*24538)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24538 (mW 12269) i /
      (rowEps i * e1MeanBounds 24538 (mW 12269) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24538 (mW 12269) (1/10^6) (1/10^7) rowEps ≤ (26363/12500000000) := by
  have hr : 0 ≤ firstRatio 24538 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24538 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24538) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12269 (1/10^6) (1/10^7) ((26363/12500000000))
      (712/10000) rowEps ≤ (27399691/250000000000) := by
  have hs : statisticsPayment ≤ (515735295057/125000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (105372880333297/1000000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12269 (1/10^6) (1/10^7) ((26363/12500000000))
      (712/10000) rowEps =
      exp (-((mW 12269 : ℝ)*24538)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12269 : ℝ)*24538)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12269) (mW 12269)).real
      (goodDist 12269 (712/10000))ᶜ ≤ (27399691/250000000000) := by
  apply le_trans (concrete_distance_charge (n := 12269) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (26363/12500000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12269 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (183961210639/250000000000000000)
  k0 := (811076623535079/200000000000000000)
  k6 := (2472441635716527/200000000000000000)
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
  norm_lower := (window_guards (n := 12269) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12269) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((27399691/250000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12269 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12269) internalParameters :=
  BstLean.Part227.worldPackage (n := 12269) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (27399691/250000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12269) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12269.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12269, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12269.frame := by
  exact frame.2.trans (by norm_num [Part259.world12269])

theorem moment_payment : internalParameters.moment ≤ Part259.world12269.moment := by
  exact moment.2.trans (by norm_num [Part259.world12269])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (119195621/100000000000) ∧
    internalParameters.frame ≤ (19743521377/31250000000) ∧
    internalParameters.moment ≤ (10312058267/1000000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12269) (Part259.world12269) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12269]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12269])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12269]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12269]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12269).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12269).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12269
#eval (do IO.println s!"P260 END 12269 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12270 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12270
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
    exp (-((mW 12270 : ℝ)*24540)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12270 : ℝ)*24540)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12270 : ℝ)*24540)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12270 : ℝ)*24540)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24540 (mW 12270) i /
      (rowEps i * e1MeanBounds 24540 (mW 12270) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24540 (mW 12270) (1/10^6) (1/10^7) rowEps ≤ (1054433/500000000000) := by
  have hr : 0 ≤ firstRatio 24540 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24540 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24540) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12270 (1/10^6) (1/10^7) ((1054433/500000000000))
      (712/10000) rowEps ≤ (109580253/1000000000000) := by
  have hs : statisticsPayment ≤ (4125194865493/1000000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (105355056905939/1000000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12270 (1/10^6) (1/10^7) ((1054433/500000000000))
      (712/10000) rowEps =
      exp (-((mW 12270 : ℝ)*24540)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12270 : ℝ)*24540)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12270) (mW 12270)).real
      (goodDist 12270 (712/10000))ᶜ ≤ (109580253/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 12270) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (1054433/500000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12270 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (735754887807/1000000000000000000)
  k0 := (506891903887161/125000000000000000)
  k6 := (309042610271343/25000000000000000)
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
  norm_lower := (window_guards (n := 12270) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12270) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((109580253/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12270 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12270) internalParameters :=
  BstLean.Part227.worldPackage (n := 12270) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (109580253/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12270) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12270.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12270, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12270.frame := by
  exact frame.2.trans (by norm_num [Part259.world12270])

theorem moment_payment : internalParameters.moment ≤ Part259.world12270.moment := by
  exact moment.2.trans (by norm_num [Part259.world12270])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1191907239/1000000000000) ∧
    internalParameters.frame ≤ (157944452111/250000000000) ∧
    internalParameters.moment ≤ (2061971703/200000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12270) (Part259.world12270) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12270]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12270])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12270]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12270]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12270).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12270).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12270
#eval (do IO.println s!"P260 END 12270 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12271 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12271
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
    exp (-((mW 12271 : ℝ)*24542)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12271 : ℝ)*24542)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12271 : ℝ)*24542)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12271 : ℝ)*24542)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24542 (mW 12271) i /
      (rowEps i * e1MeanBounds 24542 (mW 12271) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24542 (mW 12271) (1/10^6) (1/10^7) rowEps ≤ (527173/250000000000) := by
  have hr : 0 ≤ firstRatio 24542 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24542 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24542) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12271 (1/10^6) (1/10^7) ((527173/250000000000))
      (712/10000) rowEps ≤ (109561739/1000000000000) := by
  have hs : statisticsPayment ≤ (515563447829/125000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (105337229650491/1000000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12271 (1/10^6) (1/10^7) ((527173/250000000000))
      (712/10000) rowEps =
      exp (-((mW 12271 : ℝ)*24542)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12271 : ℝ)*24542)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12271) (mW 12271)).real
      (goodDist 12271 (712/10000))ᶜ ≤ (109561739/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 12271) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (527173/250000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12271 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (91958118923/125000000000000000)
  k0 := (4054887379870421/1000000000000000000)
  k6 := (12361200704706337/1000000000000000000)
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
  norm_lower := (window_guards (n := 12271) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12271) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((109561739/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12271 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12271) internalParameters :=
  BstLean.Part227.worldPackage (n := 12271) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (109561739/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12271) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12271.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12271, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12271.frame := by
  exact frame.2.trans (by norm_num [Part259.world12271])

theorem moment_payment : internalParameters.moment ≤ Part259.world12271.moment := by
  exact moment.2.trans (by norm_num [Part259.world12271])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1191858281/1000000000000) ∧
    internalParameters.frame ≤ (631762935313/1000000000000) ∧
    internalParameters.moment ≤ (5153829709/500000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12271) (Part259.world12271) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12271]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12271])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12271]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12271]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12271).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12271).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12271
#eval (do IO.println s!"P260 END 12271 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12272 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12272
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
    exp (-((mW 12272 : ℝ)*24544)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12272 : ℝ)*24544)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12272 : ℝ)*24544)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12272 : ℝ)*24544)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24544 (mW 12272) i /
      (rowEps i * e1MeanBounds 24544 (mW 12272) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24544 (mW 12272) (1/10^6) (1/10^7) rowEps ≤ (1054259/500000000000) := by
  have hr : 0 ≤ firstRatio 24544 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24544 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24544) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12272 (1/10^6) (1/10^7) ((1054259/500000000000))
      (712/10000) rowEps ≤ (109543221/1000000000000) := by
  have hs : statisticsPayment ≤ (4123820511783/1000000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (26329849642437/250000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12272 (1/10^6) (1/10^7) ((1054259/500000000000))
      (712/10000) rowEps =
      exp (-((mW 12272 : ℝ)*24544)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12272 : ℝ)*24544)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12272) (mW 12272)).real
      (goodDist 12272 (712/10000))ᶜ ≤ (109543221/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 12272) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (1054259/500000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12272 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (367787516641/500000000000000000)
  k0 := (810927912797499/200000000000000000)
  k6 := (6180348530063971/500000000000000000)
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
  norm_lower := (window_guards (n := 12272) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12272) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((109543221/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12272 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12272) internalParameters :=
  BstLean.Part227.worldPackage (n := 12272) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (109543221/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12272) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12272.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12272, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12272.frame := by
  exact frame.2.trans (by norm_num [Part259.world12272])

theorem moment_payment : internalParameters.moment ≤ Part259.world12272.moment := by
  exact moment.2.trans (by norm_num [Part259.world12272])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (148976167/125000000000) ∧
    internalParameters.frame ≤ (631748064669/1000000000000) ∧
    internalParameters.moment ≤ (644091311/62500000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12272) (Part259.world12272) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12272]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12272])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12272]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12272]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12272).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12272).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12272
#eval (do IO.println s!"P260 END 12272 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12273 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12273
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
    exp (-((mW 12273 : ℝ)*24546)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12273 : ℝ)*24546)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12273 : ℝ)*24546)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12273 : ℝ)*24546)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24546 (mW 12273) i /
      (rowEps i * e1MeanBounds 24546 (mW 12273) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24546 (mW 12273) (1/10^6) (1/10^7) rowEps ≤ (421669/200000000000) := by
  have hr : 0 ≤ firstRatio 24546 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24546 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24546) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12273 (1/10^6) (1/10^7) ((421669/200000000000))
      (712/10000) rowEps ≤ (10952499/100000000000) := by
  have hs : statisticsPayment ≤ (4123133652859/1000000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (5265092722107/50000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12273 (1/10^6) (1/10^7) ((421669/200000000000))
      (712/10000) rowEps =
      exp (-((mW 12273 : ℝ)*24546)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12273 : ℝ)*24546)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12273) (mW 12273)).real
      (goodDist 12273 (712/10000))ᶜ ≤ (10952499/100000000000) := by
  apply le_trans (concrete_distance_charge (n := 12273) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (421669/200000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12273 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (91935641687/125000000000000000)
  k0 := (4054391783441211/1000000000000000000)
  k6 := (12360193477105993/1000000000000000000)
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
  norm_lower := (window_guards (n := 12273) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12273) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((10952499/100000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12273 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12273) internalParameters :=
  BstLean.Part227.worldPackage (n := 12273) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (10952499/100000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12273) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12273.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12273, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12273.frame := by
  exact frame.2.trans (by norm_num [Part259.world12273])

theorem moment_payment : internalParameters.moment ≤ Part259.world12273.moment := by
  exact moment.2.trans (by norm_num [Part259.world12273])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (238352081/200000000000) ∧
    internalParameters.frame ≤ (631733196513/1000000000000) ∧
    internalParameters.moment ≤ (10303263189/1000000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12273) (Part259.world12273) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12273]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12273])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12273]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12273]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12273).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12273).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12273
#eval (do IO.println s!"P260 END 12273 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12274 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12274
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
    exp (-((mW 12274 : ℝ)*24548)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12274 : ℝ)*24548)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12274 : ℝ)*24548)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12274 : ℝ)*24548)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24548 (mW 12274) i /
      (rowEps i * e1MeanBounds 24548 (mW 12274) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24548 (mW 12274) (1/10^6) (1/10^7) rowEps ≤ (2108171/1000000000000) := by
  have hr : 0 ≤ firstRatio 24548 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24548 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24548) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12274 (1/10^6) (1/10^7) ((2108171/1000000000000))
      (712/10000) rowEps ≤ (3422077/31250000000) := by
  have hs : statisticsPayment ≤ (1030611751443/250000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (1052840156929/10000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12274 (1/10^6) (1/10^7) ((2108171/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 12274 : ℝ)*24548)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12274 : ℝ)*24548)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12274) (mW 12274)).real
      (goodDist 12274 (712/10000))ᶜ ≤ (3422077/31250000000) := by
  apply le_trans (concrete_distance_charge (n := 12274) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (2108171/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12274 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (36769762601/50000000000000000)
  k0 := (4054144038221509/1000000000000000000)
  k6 := (12359689955627951/1000000000000000000)
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
  norm_lower := (window_guards (n := 12274) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12274) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((3422077/31250000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12274 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12274) internalParameters :=
  BstLean.Part227.worldPackage (n := 12274) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (3422077/31250000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12274) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12274.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12274, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12274.frame := by
  exact frame.2.trans (by norm_num [Part259.world12274])

theorem moment_payment : internalParameters.moment ≤ Part259.world12274.moment := by
  exact moment.2.trans (by norm_num [Part259.world12274])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1191711487/1000000000000) ∧
    internalParameters.frame ≤ (631718330843/1000000000000) ∧
    internalParameters.moment ≤ (5150533029/500000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12274) (Part259.world12274) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12274]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12274])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12274]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12274]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12274).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12274).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12274
#eval (do IO.println s!"P260 END 12274 6 {← IO.monoMsNow}" : IO Unit)
