import BstLean.Part260Shard3Step5
#eval (do IO.println s!"P260 START 12300 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12300
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
    exp (-((mW 12300 : ℝ)*24600)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12300 : ℝ)*24600)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12300 : ℝ)*24600)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12300 : ℝ)*24600)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24600 (mW 12300) i /
      (rowEps i * e1MeanBounds 24600 (mW 12300) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24600 (mW 12300) (1/10^6) (1/10^7) rowEps ≤ (1051833/500000000000) := by
  have hr : 0 ≤ firstRatio 24600 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24600 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24600) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12300 (1/10^6) (1/10^7) ((1051833/500000000000))
      (712/10000) rowEps ≤ (54514529/500000000000) := by
  have hs : statisticsPayment ≤ (4104668246967/1000000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (20964877591043/200000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12300 (1/10^6) (1/10^7) ((1051833/500000000000))
      (712/10000) rowEps =
      exp (-((mW 12300 : ℝ)*24600)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12300 : ℝ)*24600)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12300) (mW 12300)).real
      (goodDist 12300 (712/10000))ᶜ ≤ (54514529/500000000000) := by
  apply le_trans (concrete_distance_charge (n := 12300) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (1051833/500000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12300 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (733064743633/1000000000000000000)
  k0 := (1011928759232757/250000000000000000)
  k6 := (12346619958119871/1000000000000000000)
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
  norm_lower := (window_guards (n := 12300) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12300) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((54514529/500000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12300 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12300) internalParameters :=
  BstLean.Part227.worldPackage (n := 12300) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (54514529/500000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12300) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12300.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12300, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12300.frame := by
  exact frame.2.trans (by norm_num [Part259.world12300])

theorem moment_payment : internalParameters.moment ≤ Part259.world12300.moment := by
  exact moment.2.trans (by norm_num [Part259.world12300])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1190444319/1000000000000) ∧
    internalParameters.frame ≤ (631332694041/1000000000000) ∧
    internalParameters.moment ≤ (5122084823/500000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12300) (Part259.world12300) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12300]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12300])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12300]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12300]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12300).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12300).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12300
#eval (do IO.println s!"P260 END 12300 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12301 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12301
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
    exp (-((mW 12301 : ℝ)*24602)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12301 : ℝ)*24602)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12301 : ℝ)*24602)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12301 : ℝ)*24602)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24602 (mW 12301) i /
      (rowEps i * e1MeanBounds 24602 (mW 12301) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24602 (mW 12301) (1/10^6) (1/10^7) rowEps ≤ (2103493/1000000000000) := by
  have hr : 0 ≤ firstRatio 24602 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24602 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24602) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12301 (1/10^6) (1/10^7) ((2103493/1000000000000))
      (712/10000) rowEps ≤ (4360429/40000000000) := by
  have hs : statisticsPayment ≤ (4103987286153/1000000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (26201684168111/250000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12301 (1/10^6) (1/10^7) ((2103493/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 12301 : ℝ)*24602)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12301 : ℝ)*24602)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12301) (mW 12301)).real
      (goodDist 12301 (712/10000))ᶜ ≤ (4360429/40000000000) := by
  apply le_trans (concrete_distance_charge (n := 12301) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (2103493/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12301 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (732975354577/1000000000000000000)
  k0 := (6324169129051/1562500000000000)
  k6 := (1234611809360091/100000000000000000)
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
  norm_lower := (window_guards (n := 12301) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12301) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((4360429/40000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12301 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12301) internalParameters :=
  BstLean.Part227.worldPackage (n := 12301) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (4360429/40000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12301) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12301.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12301, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12301.frame := by
  exact frame.2.trans (by norm_num [Part259.world12301])

theorem moment_payment : internalParameters.moment ≤ Part259.world12301.moment := by
  exact moment.2.trans (by norm_num [Part259.world12301])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (595197881/500000000000) ∧
    internalParameters.frame ≤ (631317895259/1000000000000) ∧
    internalParameters.moment ≤ (10241990099/1000000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12301) (Part259.world12301) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12301]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12301])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12301]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12301]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12301).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12301).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12301
#eval (do IO.println s!"P260 END 12301 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12302 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12302
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
    exp (-((mW 12302 : ℝ)*24604)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12302 : ℝ)*24604)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12302 : ℝ)*24604)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12302 : ℝ)*24604)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24604 (mW 12302) i /
      (rowEps i * e1MeanBounds 24604 (mW 12302) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24604 (mW 12302) (1/10^6) (1/10^7) rowEps ≤ (52583/25000000000) := by
  have hr : 0 ≤ firstRatio 24604 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24604 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24604) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12302 (1/10^6) (1/10^7) ((52583/25000000000))
      (712/10000) rowEps ≤ (10899239/100000000000) := by
  have hs : statisticsPayment ≤ (820661306943/200000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (104789081595197/1000000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12302 (1/10^6) (1/10^7) ((52583/25000000000))
      (712/10000) rowEps =
      exp (-((mW 12302 : ℝ)*24604)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12302 : ℝ)*24604)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12302) (mW 12302)).real
      (goodDist 12302 (712/10000))ᶜ ≤ (10899239/100000000000) := by
  apply le_trans (concrete_distance_charge (n := 12302) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (52583/25000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12302 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (732885983687/1000000000000000000)
  k0 := (505902685420521/125000000000000000)
  k6 := (1543202036284529/125000000000000000)
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
  norm_lower := (window_guards (n := 12302) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12302) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((10899239/100000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12302 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12302) internalParameters :=
  BstLean.Part227.worldPackage (n := 12302) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (10899239/100000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12302) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12302.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12302, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12302.frame := by
  exact frame.2.trans (by norm_num [Part259.world12302])

theorem moment_payment : internalParameters.moment ≤ Part259.world12302.moment := by
  exact moment.2.trans (by norm_num [Part259.world12302])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (595173609/500000000000) ∧
    internalParameters.frame ≤ (9864110921/15625000000) ∧
    internalParameters.moment ≤ (10239811201/1000000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12302) (Part259.world12302) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12302]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12302])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12302]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12302]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12302).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12302).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12302
#eval (do IO.println s!"P260 END 12302 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12303 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12303
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
    exp (-((mW 12303 : ℝ)*24606)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12303 : ℝ)*24606)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12303 : ℝ)*24606)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12303 : ℝ)*24606)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24606 (mW 12303) i /
      (rowEps i * e1MeanBounds 24606 (mW 12303) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24606 (mW 12303) (1/10^6) (1/10^7) rowEps ≤ (2103147/1000000000000) := by
  have hr : 0 ≤ firstRatio 24606 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24606 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24606) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12303 (1/10^6) (1/10^7) ((2103147/1000000000000))
      (712/10000) rowEps ≤ (2179481/20000000000) := by
  have hs : statisticsPayment ≤ (820525198513/200000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (5238571136311/50000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12303 (1/10^6) (1/10^7) ((2103147/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 12303 : ℝ)*24606)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12303 : ℝ)*24606)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12303) (mW 12303)).real
      (goodDist 12303 (712/10000))ᶜ ≤ (2179481/20000000000) := by
  apply le_trans (concrete_distance_charge (n := 12303) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (2103147/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12303 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (732796630957/1000000000000000000)
  k0 := (2023487379617733/500000000000000000)
  k6 := (12345114548133403/1000000000000000000)
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
  norm_lower := (window_guards (n := 12303) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12303) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((2179481/20000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12303 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12303) internalParameters :=
  BstLean.Part227.worldPackage (n := 12303) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (2179481/20000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12303) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12303.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12303, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12303.frame := by
  exact frame.2.trans (by norm_num [Part259.world12303])

theorem moment_payment : internalParameters.moment ≤ Part259.world12303.moment := by
  exact moment.2.trans (by norm_num [Part259.world12303])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (18598417/15625000000) ∧
    internalParameters.frame ≤ (631288305097/1000000000000) ∧
    internalParameters.moment ≤ (10237632949/1000000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12303) (Part259.world12303) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12303]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12303])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12303]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12303]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12303).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12303).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12303
#eval (do IO.println s!"P260 END 12303 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12304 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12304
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
    exp (-((mW 12304 : ℝ)*24608)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12304 : ℝ)*24608)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12304 : ℝ)*24608)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12304 : ℝ)*24608)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24608 (mW 12304) i /
      (rowEps i * e1MeanBounds 24608 (mW 12304) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24608 (mW 12304) (1/10^6) (1/10^7) rowEps ≤ (1051487/500000000000) := by
  have hr : 0 ≤ firstRatio 24608 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24608 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24608) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12304 (1/10^6) (1/10^7) ((1051487/500000000000))
      (712/10000) rowEps ≤ (108955707/1000000000000) := by
  have hs : statisticsPayment ≤ (4101945659617/1000000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (104753760068263/1000000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12304 (1/10^6) (1/10^7) ((1051487/500000000000))
      (712/10000) rowEps =
      exp (-((mW 12304 : ℝ)*24608)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12304 : ℝ)*24608)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12304) (mW 12304)).real
      (goodDist 12304 (712/10000))ᶜ ≤ (108955707/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 12304) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (1051487/500000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12304 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (366353648191/500000000000000000)
  k0 := (2023364035099573/500000000000000000)
  k6 := (1543076608394999/125000000000000000)
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
  norm_lower := (window_guards (n := 12304) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12304) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((108955707/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12304 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12304) internalParameters :=
  BstLean.Part227.worldPackage (n := 12304) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (108955707/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12304) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12304.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12304, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12304.frame := by
  exact frame.2.trans (by norm_num [Part259.world12304])

theorem moment_payment : internalParameters.moment ≤ Part259.world12304.moment := by
  exact moment.2.trans (by norm_num [Part259.world12304])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (119025017/100000000000) ∧
    internalParameters.frame ≤ (631273513717/1000000000000) ∧
    internalParameters.moment ≤ (5117727673/500000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12304) (Part259.world12304) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12304]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12304])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12304]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12304]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12304).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12304).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12304
#eval (do IO.println s!"P260 END 12304 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12305 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12305
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
    exp (-((mW 12305 : ℝ)*24610)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12305 : ℝ)*24610)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12305 : ℝ)*24610)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12305 : ℝ)*24610)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24610 (mW 12305) i /
      (rowEps i * e1MeanBounds 24610 (mW 12305) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24610 (mW 12305) (1/10^6) (1/10^7) rowEps ≤ (2102801/1000000000000) := by
  have hr : 0 ≤ firstRatio 24610 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24610 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24610) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12305 (1/10^6) (1/10^7) ((2102801/1000000000000))
      (712/10000) rowEps ≤ (108937361/1000000000000) := by
  have hs : statisticsPayment ≤ (2050632767891/500000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (52368046812039/500000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12305 (1/10^6) (1/10^7) ((2102801/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 12305 : ℝ)*24610)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12305 : ℝ)*24610)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12305) (mW 12305)).real
      (goodDist 12305 (712/10000))ᶜ ≤ (108937361/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 12305) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (2102801/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12305 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (732617979957/1000000000000000000)
  k0 := (4046481416247819/1000000000000000000)
  k6 := (12344111247343569/1000000000000000000)
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
  norm_lower := (window_guards (n := 12305) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12305) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((108937361/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12305 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12305) internalParameters :=
  BstLean.Part227.worldPackage (n := 12305) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (108937361/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12305) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12305.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12305, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12305.frame := by
  exact frame.2.trans (by norm_num [Part259.world12305])

theorem moment_payment : internalParameters.moment ≤ Part259.world12305.moment := by
  exact moment.2.trans (by norm_num [Part259.world12305])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (595100833/500000000000) ∧
    internalParameters.frame ≤ (631258724803/1000000000000) ∧
    internalParameters.moment ≤ (10233278389/1000000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12305) (Part259.world12305) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12305]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12305])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12305]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12305]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12305).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12305).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12305
#eval (do IO.println s!"P260 END 12305 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12306 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12306
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
    exp (-((mW 12306 : ℝ)*24612)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12306 : ℝ)*24612)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12306 : ℝ)*24612)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12306 : ℝ)*24612)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24612 (mW 12306) i /
      (rowEps i * e1MeanBounds 24612 (mW 12306) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24612 (mW 12306) (1/10^6) (1/10^7) rowEps ≤ (2102629/1000000000000) := by
  have hr : 0 ≤ firstRatio 24612 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24612 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24612) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12306 (1/10^6) (1/10^7) ((2102629/1000000000000))
      (712/10000) rowEps ≤ (1089193/10000000000) := by
  have hs : statisticsPayment ≤ (164023424839/40000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (4188748532767/40000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12306 (1/10^6) (1/10^7) ((2102629/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 12306 : ℝ)*24612)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12306 : ℝ)*24612)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12306) (mW 12306)).real
      (goodDist 12306 (712/10000))ᶜ ≤ (1089193/10000000000) := by
  apply le_trans (concrete_distance_charge (n := 12306) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (2102629/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12306 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (183132170419/250000000000000000)
  k0 := (404623479737133/100000000000000000)
  k6 := (12343609688671711/1000000000000000000)
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
  norm_lower := (window_guards (n := 12306) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12306) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((1089193/10000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12306 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12306) internalParameters :=
  BstLean.Part227.worldPackage (n := 12306) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (1089193/10000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12306) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12306.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12306, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12306.frame := by
  exact frame.2.trans (by norm_num [Part259.world12306])

theorem moment_payment : internalParameters.moment ≤ Part259.world12306.moment := by
  exact moment.2.trans (by norm_num [Part259.world12306])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (47606127/40000000000) ∧
    internalParameters.frame ≤ (315621969177/500000000000) ∧
    internalParameters.moment ≤ (10231102079/1000000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12306) (Part259.world12306) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12306]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12306])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12306]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12306]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12306).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12306).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12306
#eval (do IO.println s!"P260 END 12306 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12307 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12307
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
    exp (-((mW 12307 : ℝ)*24614)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12307 : ℝ)*24614)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12307 : ℝ)*24614)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12307 : ℝ)*24614)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24614 (mW 12307) i /
      (rowEps i * e1MeanBounds 24614 (mW 12307) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24614 (mW 12307) (1/10^6) (1/10^7) rowEps ≤ (262807/125000000000) := by
  have hr : 0 ≤ firstRatio 24614 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24614 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24614) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12307 (1/10^6) (1/10^7) ((262807/125000000000))
      (712/10000) rowEps ≤ (108900947/1000000000000) := by
  have hs : statisticsPayment ≤ (1024976478777/250000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (52350519642357/500000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12307 (1/10^6) (1/10^7) ((262807/125000000000))
      (712/10000) rowEps =
      exp (-((mW 12307 : ℝ)*24614)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12307 : ℝ)*24614)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12307) (mW 12307)).real
      (goodDist 12307 (712/10000))ᶜ ≤ (108900947/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 12307) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (262807/125000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12307 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (146487880307/200000000000000000)
  k0 := (1011497053391261/250000000000000000)
  k6 := (3085777047782999/250000000000000000)
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
  norm_lower := (window_guards (n := 12307) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12307) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((108900947/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12307 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12307) internalParameters :=
  BstLean.Part227.worldPackage (n := 12307) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (108900947/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12307) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12307.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12307, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12307.frame := by
  exact frame.2.trans (by norm_num [Part259.world12307])

theorem moment_payment : internalParameters.moment ≤ Part259.world12307.moment := by
  exact moment.2.trans (by norm_num [Part259.world12307])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (595052349/500000000000) ∧
    internalParameters.frame ≤ (63122915437/100000000000) ∧
    internalParameters.moment ≤ (639307901/62500000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12307) (Part259.world12307) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12307]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12307])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12307]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12307]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12307).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12307).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12307
#eval (do IO.println s!"P260 END 12307 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12308 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12308
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
    exp (-((mW 12308 : ℝ)*24616)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12308 : ℝ)*24616)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12308 : ℝ)*24616)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12308 : ℝ)*24616)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24616 (mW 12308) i /
      (rowEps i * e1MeanBounds 24616 (mW 12308) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24616 (mW 12308) (1/10^6) (1/10^7) rowEps ≤ (2102283/1000000000000) := by
  have hr : 0 ≤ firstRatio 24616 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24616 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24616) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12308 (1/10^6) (1/10^7) ((2102283/1000000000000))
      (712/10000) rowEps ≤ (108882589/1000000000000) := by
  have hs : statisticsPayment ≤ (2049613209047/500000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (52341680736127/500000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12308 (1/10^6) (1/10^7) ((2102283/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 12308 : ℝ)*24616)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12308 : ℝ)*24616)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12308) (mW 12308)).real
      (goodDist 12308 (712/10000))ᶜ ≤ (108882589/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 12308) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (2102283/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12308 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (732350139527/1000000000000000000)
  k0 := (4045741664816039/1000000000000000000)
  k6 := (1542825844339001/125000000000000000)
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
  norm_lower := (window_guards (n := 12308) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12308) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((108882589/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12308 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12308) internalParameters :=
  BstLean.Part227.worldPackage (n := 12308) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (108882589/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12308) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12308.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12308, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12308.frame := by
  exact frame.2.trans (by norm_num [Part259.world12308])

theorem moment_payment : internalParameters.moment ≤ Part259.world12308.moment := by
  exact moment.2.trans (by norm_num [Part259.world12308])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1190056233/1000000000000) ∧
    internalParameters.frame ≤ (12624287457/20000000000) ∧
    internalParameters.moment ≤ (10226751399/1000000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12308) (Part259.world12308) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12308]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12308])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12308]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12308]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12308).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12308).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12308
#eval (do IO.println s!"P260 END 12308 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12309 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12309
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
    exp (-((mW 12309 : ℝ)*24618)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12309 : ℝ)*24618)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12309 : ℝ)*24618)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12309 : ℝ)*24618)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24618 (mW 12309) i /
      (rowEps i * e1MeanBounds 24618 (mW 12309) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24618 (mW 12309) (1/10^6) (1/10^7) rowEps ≤ (2102111/1000000000000) := by
  have hr : 0 ≤ firstRatio 24618 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24618 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24618) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12309 (1/10^6) (1/10^7) ((2102111/1000000000000))
      (712/10000) rowEps ≤ (54432259/500000000000) := by
  have hs : statisticsPayment ≤ (819709425969/200000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (52332984865069/500000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12309 (1/10^6) (1/10^7) ((2102111/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 12309 : ℝ)*24618)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12309 : ℝ)*24618)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12309) (mW 12309)).real
      (goodDist 12309 (712/10000))ᶜ ≤ (54432259/500000000000) := by
  apply le_trans (concrete_distance_charge (n := 12309) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (2102111/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12309 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (732260895649/1000000000000000000)
  k0 := (2022747575561219/500000000000000000)
  k6 := (12342105379399331/1000000000000000000)
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
  norm_lower := (window_guards (n := 12309) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12309) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((54432259/500000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12309 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12309) internalParameters :=
  BstLean.Part227.worldPackage (n := 12309) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (54432259/500000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12309) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12309.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12309, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12309.frame := by
  exact frame.2.trans (by norm_num [Part259.world12309])

theorem moment_payment : internalParameters.moment ≤ Part259.world12309.moment := by
  exact moment.2.trans (by norm_num [Part259.world12309])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (595003891/500000000000) ∧
    internalParameters.frame ≤ (315599796897/500000000000) ∧
    internalParameters.moment ≤ (2556144257/250000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12309) (Part259.world12309) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12309]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12309])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12309]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12309]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12309).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12309).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12309
#eval (do IO.println s!"P260 END 12309 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12310 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12310
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
    exp (-((mW 12310 : ℝ)*24620)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12310 : ℝ)*24620)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12310 : ℝ)*24620)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12310 : ℝ)*24620)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24620 (mW 12310) i /
      (rowEps i * e1MeanBounds 24620 (mW 12310) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24620 (mW 12310) (1/10^6) (1/10^7) rowEps ≤ (1050969/500000000000) := by
  have hr : 0 ≤ firstRatio 24620 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24620 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24620) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12310 (1/10^6) (1/10^7) ((1050969/500000000000))
      (712/10000) rowEps ≤ (54423077/500000000000) := by
  have hs : statisticsPayment ≤ (4097868050277/1000000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (52324142171897/500000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12310 (1/10^6) (1/10^7) ((1050969/500000000000))
      (712/10000) rowEps =
      exp (-((mW 12310 : ℝ)*24620)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12310 : ℝ)*24620)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12310) (mW 12310)).real
      (goodDist 12310 (712/10000))ᶜ ≤ (54423077/500000000000) := by
  apply le_trans (concrete_distance_charge (n := 12310) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (1050969/500000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12310 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (146434333979/200000000000000000)
  k0 := (2022624336237037/500000000000000000)
  k6 := (12341604065181557/1000000000000000000)
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
  norm_lower := (window_guards (n := 12310) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12310) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((54423077/500000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12310 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12310) internalParameters :=
  BstLean.Part227.worldPackage (n := 12310) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (54423077/500000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12310) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12310.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12310, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12310.frame := by
  exact frame.2.trans (by norm_num [Part259.world12310])

theorem moment_payment : internalParameters.moment ≤ Part259.world12310.moment := by
  exact moment.2.trans (by norm_num [Part259.world12310])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (74372459/62500000000) ∧
    internalParameters.frame ≤ (631184817201/1000000000000) ∧
    internalParameters.moment ≤ (10222403303/1000000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12310) (Part259.world12310) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12310]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12310])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12310]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12310]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12310).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12310).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12310
#eval (do IO.println s!"P260 END 12310 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12311 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12311
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
    exp (-((mW 12311 : ℝ)*24622)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12311 : ℝ)*24622)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12311 : ℝ)*24622)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12311 : ℝ)*24622)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24622 (mW 12311) i /
      (rowEps i * e1MeanBounds 24622 (mW 12311) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24622 (mW 12311) (1/10^6) (1/10^7) rowEps ≤ (420353/200000000000) := by
  have hr : 0 ≤ firstRatio 24622 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24622 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24622) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12311 (1/10^6) (1/10^7) ((420353/200000000000))
      (712/10000) rowEps ≤ (54413893/500000000000) := by
  have hs : statisticsPayment ≤ (40971891793/10000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (52315297593847/500000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12311 (1/10^6) (1/10^7) ((420353/200000000000))
      (712/10000) rowEps =
      exp (-((mW 12311 : ℝ)*24622)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12311 : ℝ)*24622)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12311) (mW 12311)).real
      (goodDist 12311 (712/10000))ᶜ ≤ (54413893/500000000000) := by
  apply le_trans (concrete_distance_charge (n := 12311) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (420353/200000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12311 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (732082462259/1000000000000000000)
  k0 := (4045002228860777/1000000000000000000)
  k6 := (6170551406023139/500000000000000000)
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
  norm_lower := (window_guards (n := 12311) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12311) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((54413893/500000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12311 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12311) internalParameters :=
  BstLean.Part227.worldPackage (n := 12311) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (54413893/500000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12311) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12311.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12311, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12311.frame := by
  exact frame.2.trans (by norm_num [Part259.world12311])

theorem moment_payment : internalParameters.moment ≤ Part259.world12311.moment := by
  exact moment.2.trans (by norm_num [Part259.world12311])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (29747773/25000000000) ∧
    internalParameters.frame ≤ (631170043069/1000000000000) ∧
    internalParameters.moment ≤ (638764389/62500000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12311) (Part259.world12311) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12311]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12311])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12311]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12311]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12311).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12311).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12311
#eval (do IO.println s!"P260 END 12311 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12312 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12312
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
    exp (-((mW 12312 : ℝ)*24624)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12312 : ℝ)*24624)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12312 : ℝ)*24624)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12312 : ℝ)*24624)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24624 (mW 12312) i /
      (rowEps i * e1MeanBounds 24624 (mW 12312) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24624 (mW 12312) (1/10^6) (1/10^7) rowEps ≤ (2101593/1000000000000) := by
  have hr : 0 ≤ firstRatio 24624 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24624 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24624) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12312 (1/10^6) (1/10^7) ((2101593/1000000000000))
      (712/10000) rowEps ≤ (13601213/125000000000) := by
  have hs : statisticsPayment ≤ (4096510516829/1000000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (104613192032761/1000000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12312 (1/10^6) (1/10^7) ((2101593/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 12312 : ℝ)*24624)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12312 : ℝ)*24624)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12312) (mW 12312)).real
      (goodDist 12312 (712/10000))ᶜ ≤ (13601213/125000000000) := by
  apply le_trans (concrete_distance_charge (n := 12312) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (2101593/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12312 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (731993272737/1000000000000000000)
  k0 := (4044755820277901/1000000000000000000)
  k6 := (12340601619981091/1000000000000000000)
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
  norm_lower := (window_guards (n := 12312) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12312) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((13601213/125000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12312 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12312) internalParameters :=
  BstLean.Part227.worldPackage (n := 12312) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (13601213/125000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12312) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12312.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12312, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12312.frame := by
  exact frame.2.trans (by norm_num [Part259.world12312])

theorem moment_payment : internalParameters.moment ≤ Part259.world12312.moment := by
  exact moment.2.trans (by norm_num [Part259.world12312])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (297465627/250000000000) ∧
    internalParameters.frame ≤ (3155776357/5000000000) ∧
    internalParameters.moment ≤ (1021805779/100000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12312) (Part259.world12312) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12312]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12312])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12312]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12312]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12312).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12312).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12312
#eval (do IO.println s!"P260 END 12312 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12313 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12313
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
    exp (-((mW 12313 : ℝ)*24626)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12313 : ℝ)*24626)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12313 : ℝ)*24626)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12313 : ℝ)*24626)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24626 (mW 12313) i /
      (rowEps i * e1MeanBounds 24626 (mW 12313) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24626 (mW 12313) (1/10^6) (1/10^7) rowEps ≤ (105071/50000000000) := by
  have hr : 0 ≤ firstRatio 24626 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24626 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24626) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12313 (1/10^6) (1/10^7) ((105071/50000000000))
      (712/10000) rowEps ≤ (108791329/1000000000000) := by
  have hs : statisticsPayment ≤ (4095832062777/1000000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (26148873829797/250000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12313 (1/10^6) (1/10^7) ((105071/50000000000))
      (712/10000) rowEps =
      exp (-((mW 12313 : ℝ)*24626)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12313 : ℝ)*24626)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12313) (mW 12313)).real
      (goodDist 12313 (712/10000))ᶜ ≤ (108791329/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 12313) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (105071/50000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12313 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (731904101323/1000000000000000000)
  k0 := (4044509446715269/1000000000000000000)
  k6 := (3085025122243399/250000000000000000)
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
  norm_lower := (window_guards (n := 12313) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12313) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((108791329/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12313 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12313) internalParameters :=
  BstLean.Part227.worldPackage (n := 12313) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (108791329/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12313) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12313.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12313, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12313.frame := by
  exact frame.2.trans (by norm_num [Part259.world12313])

theorem moment_payment : internalParameters.moment ≤ Part259.world12313.moment := by
  exact moment.2.trans (by norm_num [Part259.world12313])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (118981411/100000000000) ∧
    internalParameters.frame ≤ (631140502191/1000000000000) ∧
    internalParameters.moment ≤ (10215886001/1000000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12313) (Part259.world12313) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12313]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12313])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12313]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12313]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12313).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12313).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12313
#eval (do IO.println s!"P260 END 12313 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12314 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12314
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
    exp (-((mW 12314 : ℝ)*24628)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12314 : ℝ)*24628)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12314 : ℝ)*24628)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12314 : ℝ)*24628)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24628 (mW 12314) i /
      (rowEps i * e1MeanBounds 24628 (mW 12314) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24628 (mW 12314) (1/10^6) (1/10^7) rowEps ≤ (513/244140625) := by
  have hr : 0 ≤ firstRatio 24628 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24628 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24628) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12314 (1/10^6) (1/10^7) ((513/244140625))
      (712/10000) rowEps ≤ (2719331/25000000000) := by
  have hs : statisticsPayment ≤ (4095153817057/1000000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (104578084560901/1000000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12314 (1/10^6) (1/10^7) ((513/244140625))
      (712/10000) rowEps =
      exp (-((mW 12314 : ℝ)*24628)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12314 : ℝ)*24628)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12314) (mW 12314)).real
      (goodDist 12314 (712/10000))ᶜ ≤ (2719331/25000000000) := by
  apply le_trans (concrete_distance_charge (n := 12314) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (513/244140625)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12314 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (731814948013/1000000000000000000)
  k0 := (404426310816823/100000000000000000)
  k6 := (12339599419011397/1000000000000000000)
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
  norm_lower := (window_guards (n := 12314) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12314) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((2719331/25000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12314 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12314) internalParameters :=
  BstLean.Part227.worldPackage (n := 12314) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (2719331/25000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12314) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12314.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12314, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12314.frame := by
  exact frame.2.trans (by norm_num [Part259.world12314])

theorem moment_payment : internalParameters.moment ≤ Part259.world12314.moment := by
  exact moment.2.trans (by norm_num [Part259.world12314])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (47590629/40000000000) ∧
    internalParameters.frame ≤ (315562867721/500000000000) ∧
    internalParameters.moment ≤ (10213714857/1000000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12314) (Part259.world12314) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12314]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12314])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12314]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12314]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12314).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12314).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12314
#eval (do IO.println s!"P260 END 12314 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12315 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12315
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
    exp (-((mW 12315 : ℝ)*24630)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12315 : ℝ)*24630)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12315 : ℝ)*24630)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12315 : ℝ)*24630)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24630 (mW 12315) i /
      (rowEps i * e1MeanBounds 24630 (mW 12315) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24630 (mW 12315) (1/10^6) (1/10^7) rowEps ≤ (84043/40000000000) := by
  have hr : 0 ≤ firstRatio 24630 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24630 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24630) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12315 (1/10^6) (1/10^7) ((84043/40000000000))
      (712/10000) rowEps ≤ (54377429/500000000000) := by
  have hs : statisticsPayment ≤ (2047237889791/500000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (104560380300789/1000000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12315 (1/10^6) (1/10^7) ((84043/40000000000))
      (712/10000) rowEps =
      exp (-((mW 12315 : ℝ)*24630)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12315 : ℝ)*24630)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12315) (mW 12315)).real
      (goodDist 12315 (712/10000))ᶜ ≤ (54377429/500000000000) := by
  apply le_trans (concrete_distance_charge (n := 12315) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (84043/40000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12315 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (731725812801/1000000000000000000)
  k0 := (2022008402313301/500000000000000000)
  k6 := (12339098410082101/1000000000000000000)
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
  norm_lower := (window_guards (n := 12315) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12315) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((54377429/500000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12315 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12315) internalParameters :=
  BstLean.Part227.worldPackage (n := 12315) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (54377429/500000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12315) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12315.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12315, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12315.frame := by
  exact frame.2.trans (by norm_num [Part259.world12315])

theorem moment_payment : internalParameters.moment ≤ Part259.world12315.moment := by
  exact moment.2.trans (by norm_num [Part259.world12315])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (594858677/500000000000) ∧
    internalParameters.frame ≤ (631110971153/1000000000000) ∧
    internalParameters.moment ≤ (10211544357/1000000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12315) (Part259.world12315) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12315]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12315])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12315]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12315]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12315).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12315).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12315
#eval (do IO.println s!"P260 END 12315 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12316 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12316
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
    exp (-((mW 12316 : ℝ)*24632)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12316 : ℝ)*24632)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12316 : ℝ)*24632)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12316 : ℝ)*24632)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24632 (mW 12316) i /
      (rowEps i * e1MeanBounds 24632 (mW 12316) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24632 (mW 12316) (1/10^6) (1/10^7) rowEps ≤ (2100903/1000000000000) := by
  have hr : 0 ≤ firstRatio 24632 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24632 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24632) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12316 (1/10^6) (1/10^7) ((2100903/1000000000000))
      (712/10000) rowEps ≤ (108736761/1000000000000) := by
  have hs : statisticsPayment ≤ (2046898975133/500000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (52271480974989/500000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12316 (1/10^6) (1/10^7) ((2100903/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 12316 : ℝ)*24632)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12316 : ℝ)*24632)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12316) (mW 12316)).real
      (goodDist 12316 (712/10000))ᶜ ≤ (108736761/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 12316) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (2100903/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12316 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (365818347841/500000000000000000)
  k0 := (1010942634020741/250000000000000000)
  k6 := (12338597462173319/1000000000000000000)
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
  norm_lower := (window_guards (n := 12316) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12316) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((108736761/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12316 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12316) internalParameters :=
  BstLean.Part227.worldPackage (n := 12316) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (108736761/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12316) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12316.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12316, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12316.frame := by
  exact frame.2.trans (by norm_num [Part259.world12316])

theorem moment_payment : internalParameters.moment ≤ Part259.world12316.moment := by
  exact moment.2.trans (by norm_num [Part259.world12316])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (237933799/200000000000) ∧
    internalParameters.frame ≤ (631096209323/1000000000000) ∧
    internalParameters.moment ≤ (5104687251/500000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12316) (Part259.world12316) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12316]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12316])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12316]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12316]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12316).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12316).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12316
#eval (do IO.println s!"P260 END 12316 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12317 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12317
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
    exp (-((mW 12317 : ℝ)*24634)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12317 : ℝ)*24634)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12317 : ℝ)*24634)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12317 : ℝ)*24634)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24634 (mW 12317) i /
      (rowEps i * e1MeanBounds 24634 (mW 12317) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24634 (mW 12317) (1/10^6) (1/10^7) rowEps ≤ (210073/100000000000) := by
  have hr : 0 ≤ firstRatio 24634 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24634 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24634) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12317 (1/10^6) (1/10^7) ((210073/100000000000))
      (712/10000) rowEps ≤ (27179593/250000000000) := by
  have hs : statisticsPayment ≤ (2046560164511/500000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (104525250154273/1000000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12317 (1/10^6) (1/10^7) ((210073/100000000000))
      (712/10000) rowEps =
      exp (-((mW 12317 : ℝ)*24634)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12317 : ℝ)*24634)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12317) (mW 12317)).real
      (goodDist 12317 (712/10000))ᶜ ≤ (27179593/250000000000) := by
  apply le_trans (concrete_distance_charge (n := 12317) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (210073/100000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12317 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (731547596651/1000000000000000000)
  k0 := (4043524302529893/1000000000000000000)
  k6 := (2467619315054533/200000000000000000)
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
  norm_lower := (window_guards (n := 12317) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12317) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((27179593/250000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12317 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12317) internalParameters :=
  BstLean.Part227.worldPackage (n := 12317) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (27179593/250000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12317) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12317.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12317, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12317.frame := by
  exact frame.2.trans (by norm_num [Part259.world12317])

theorem moment_payment : internalParameters.moment ≤ Part259.world12317.moment := by
  exact moment.2.trans (by norm_num [Part259.world12317])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (23792413/20000000000) ∧
    internalParameters.frame ≤ (19721295311/31250000000) ∧
    internalParameters.moment ≤ (10207205291/1000000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12317) (Part259.world12317) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12317]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12317])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12317]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12317]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12317).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12317).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12317
#eval (do IO.println s!"P260 END 12317 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12318 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12318
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
    exp (-((mW 12318 : ℝ)*24636)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12318 : ℝ)*24636)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12318 : ℝ)*24636)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12318 : ℝ)*24636)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24636 (mW 12318) i /
      (rowEps i * e1MeanBounds 24636 (mW 12318) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24636 (mW 12318) (1/10^6) (1/10^7) rowEps ≤ (1050279/500000000000) := by
  have hr : 0 ≤ firstRatio 24636 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24636 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24636) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12318 (1/10^6) (1/10^7) ((1050279/500000000000))
      (712/10000) rowEps ≤ (108700269/1000000000000) := by
  have hs : statisticsPayment ≤ (4092442915763/1000000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (104507824221777/1000000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12318 (1/10^6) (1/10^7) ((1050279/500000000000))
      (712/10000) rowEps =
      exp (-((mW 12318 : ℝ)*24636)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12318 : ℝ)*24636)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12318) (mW 12318)).real
      (goodDist 12318 (712/10000))ᶜ ≤ (108700269/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 12318) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (1050279/500000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12318 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (365729257851/500000000000000000)
  k0 := (4043278103957197/1000000000000000000)
  k6 := (12337595749367757/1000000000000000000)
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
  norm_lower := (window_guards (n := 12318) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12318) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((108700269/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12318 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12318) internalParameters :=
  BstLean.Part227.worldPackage (n := 12318) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (108700269/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12318) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12318.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12318, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12318.frame := by
  exact frame.2.trans (by norm_num [Part259.world12318])

theorem moment_payment : internalParameters.moment ≤ Part259.world12318.moment := by
  exact moment.2.trans (by norm_num [Part259.world12318])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (594786159/500000000000) ∧
    internalParameters.frame ≤ (631066693037/1000000000000) ∧
    internalParameters.moment ≤ (408201469/40000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12318) (Part259.world12318) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12318]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12318])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12318]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12318]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12318).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12318).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12318
#eval (do IO.println s!"P260 END 12318 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12319 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12319
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
    exp (-((mW 12319 : ℝ)*24638)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12319 : ℝ)*24638)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12319 : ℝ)*24638)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12319 : ℝ)*24638)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24638 (mW 12319) i /
      (rowEps i * e1MeanBounds 24638 (mW 12319) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24638 (mW 12319) (1/10^6) (1/10^7) rowEps ≤ (1050193/500000000000) := by
  have hr : 0 ≤ firstRatio 24638 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24638 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24638) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12319 (1/10^6) (1/10^7) ((1050193/500000000000))
      (712/10000) rowEps ≤ (54341081/500000000000) := by
  have hs : statisticsPayment ≤ (1022941427601/250000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (104490394489869/1000000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12319 (1/10^6) (1/10^7) ((1050193/500000000000))
      (712/10000) rowEps =
      exp (-((mW 12319 : ℝ)*24638)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12319 : ℝ)*24638)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12319) (mW 12319)).real
      (goodDist 12319 (712/10000))ᶜ ≤ (54341081/500000000000) := by
  apply le_trans (concrete_distance_charge (n := 12319) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (1050193/500000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12319 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (731369452831/1000000000000000000)
  k0 := (4043031940360211/1000000000000000000)
  k6 := (12337094984446217/1000000000000000000)
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
  norm_lower := (window_guards (n := 12319) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12319) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((54341081/500000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12319 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12319) internalParameters :=
  BstLean.Part227.worldPackage (n := 12319) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (54341081/500000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12319) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12319.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12319, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12319.frame := by
  exact frame.2.trans (by norm_num [Part259.world12319])

theorem moment_payment : internalParameters.moment ≤ Part259.world12319.moment := by
  exact moment.2.trans (by norm_num [Part259.world12319])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1189523999/1000000000000) ∧
    internalParameters.frame ≤ (31552596929/50000000000) ∧
    internalParameters.moment ≤ (10202868801/1000000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12319) (Part259.world12319) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12319]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12319])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12319]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12319]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12319).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12319).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12319
#eval (do IO.println s!"P260 END 12319 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12320 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12320
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
    exp (-((mW 12320 : ℝ)*24640)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12320 : ℝ)*24640)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12320 : ℝ)*24640)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12320 : ℝ)*24640)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24640 (mW 12320) i /
      (rowEps i * e1MeanBounds 24640 (mW 12320) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24640 (mW 12320) (1/10^6) (1/10^7) rowEps ≤ (2100213/1000000000000) := by
  have hr : 0 ≤ firstRatio 24640 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24640 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24640) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12320 (1/10^6) (1/10^7) ((2100213/1000000000000))
      (712/10000) rowEps ≤ (54331881/500000000000) := by
  have hs : statisticsPayment ≤ (4091088712857/1000000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (1044726713981/10000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12320 (1/10^6) (1/10^7) ((2100213/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 12320 : ℝ)*24640)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12320 : ℝ)*24640)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12320) (mW 12320)).real
      (goodDist 12320 (712/10000))ᶜ ≤ (54331881/500000000000) := by
  apply le_trans (concrete_distance_charge (n := 12320) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (2100213/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12320 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (731280408033/1000000000000000000)
  k0 := (252674113233219/62500000000000000)
  k6 := (12336594280495669/1000000000000000000)
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
  norm_lower := (window_guards (n := 12320) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12320) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((54331881/500000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12320 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12320) internalParameters :=
  BstLean.Part227.worldPackage (n := 12320) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (54331881/500000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12320) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12320.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12320, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12320.frame := by
  exact frame.2.trans (by norm_num [Part259.world12320])

theorem moment_payment : internalParameters.moment ≤ Part259.world12320.moment := by
  exact moment.2.trans (by norm_num [Part259.world12320])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1189475693/1000000000000) ∧
    internalParameters.frame ≤ (631037186579/1000000000000) ∧
    internalParameters.moment ≤ (10200701521/1000000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12320) (Part259.world12320) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12320]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12320])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12320]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12320]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12320).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12320).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12320
#eval (do IO.println s!"P260 END 12320 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12321 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12321
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
    exp (-((mW 12321 : ℝ)*24642)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12321 : ℝ)*24642)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12321 : ℝ)*24642)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12321 : ℝ)*24642)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24642 (mW 12321) i /
      (rowEps i * e1MeanBounds 24642 (mW 12321) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24642 (mW 12321) (1/10^6) (1/10^7) rowEps ≤ (2100041/1000000000000) := by
  have hr : 0 ≤ firstRatio 24642 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24642 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24642) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12321 (1/10^6) (1/10^7) ((2100041/1000000000000))
      (712/10000) rowEps ≤ (6790353/62500000000) := by
  have hs : statisticsPayment ≤ (4090411923037/1000000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (104455234100757/1000000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12321 (1/10^6) (1/10^7) ((2100041/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 12321 : ℝ)*24642)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12321 : ℝ)*24642)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12321) (mW 12321)).real
      (goodDist 12321 (712/10000))ᶜ ≤ (6790353/62500000000) := by
  apply le_trans (concrete_distance_charge (n := 12321) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (2100041/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12321 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (731191381301/1000000000000000000)
  k0 := (4042539718058111/1000000000000000000)
  k6 := (6168046818751871/500000000000000000)
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
  norm_lower := (window_guards (n := 12321) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12321) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((6790353/62500000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12321 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12321) internalParameters :=
  BstLean.Part227.worldPackage (n := 12321) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (6790353/62500000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12321) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12321.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12321, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12321.frame := by
  exact frame.2.trans (by norm_num [Part259.world12321])

theorem moment_payment : internalParameters.moment ≤ Part259.world12321.moment := by
  exact moment.2.trans (by norm_num [Part259.world12321])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1189427401/1000000000000) ∧
    internalParameters.frame ≤ (315511218517/500000000000) ∧
    internalParameters.moment ≤ (2039706977/200000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12321) (Part259.world12321) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12321]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12321])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12321]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12321]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12321).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12321).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12321
#eval (do IO.println s!"P260 END 12321 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12322 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12322
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
    exp (-((mW 12322 : ℝ)*24644)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12322 : ℝ)*24644)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12322 : ℝ)*24644)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12322 : ℝ)*24644)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24644 (mW 12322) i /
      (rowEps i * e1MeanBounds 24644 (mW 12322) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24644 (mW 12322) (1/10^6) (1/10^7) rowEps ≤ (2099869/1000000000000) := by
  have hr : 0 ≤ firstRatio 24644 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24644 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24644) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12322 (1/10^6) (1/10^7) ((2099869/1000000000000))
      (712/10000) rowEps ≤ (10862753/100000000000) := by
  have hs : statisticsPayment ≤ (511216917607/125000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (104437793012091/1000000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12322 (1/10^6) (1/10^7) ((2099869/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 12322 : ℝ)*24644)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12322 : ℝ)*24644)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12322) (mW 12322)).real
      (goodDist 12322 (712/10000))ᶜ ≤ (10862753/100000000000) := by
  apply le_trans (concrete_distance_charge (n := 12322) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (2099869/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12322 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (91387796579/125000000000000000)
  k0 := (1010573414834531/250000000000000000)
  k6 := (12335593055458067/1000000000000000000)
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
  norm_lower := (window_guards (n := 12322) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12322) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((10862753/100000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12322 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12322) internalParameters :=
  BstLean.Part227.worldPackage (n := 12322) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (10862753/100000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12322) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12322.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12322, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12322.frame := by
  exact frame.2.trans (by norm_num [Part259.world12322])

theorem moment_payment : internalParameters.moment ≤ Part259.world12322.moment := by
  exact moment.2.trans (by norm_num [Part259.world12322])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (594689561/500000000000) ∧
    internalParameters.frame ≤ (78875961243/125000000000) ∧
    internalParameters.moment ≤ (10196368891/1000000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12322) (Part259.world12322) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12322]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12322])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12322]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12322]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12322).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12322).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12322
#eval (do IO.println s!"P260 END 12322 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12323 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12323
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
    exp (-((mW 12323 : ℝ)*24646)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12323 : ℝ)*24646)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12323 : ℝ)*24646)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12323 : ℝ)*24646)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24646 (mW 12323) i /
      (rowEps i * e1MeanBounds 24646 (mW 12323) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24646 (mW 12323) (1/10^6) (1/10^7) rowEps ≤ (131231/62500000000) := by
  have hr : 0 ≤ firstRatio 24646 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24646 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24646) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12323 (1/10^6) (1/10^7) ((131231/62500000000))
      (712/10000) rowEps ≤ (108609119/1000000000000) := by
  have hs : statisticsPayment ≤ (4089058966229/1000000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (26105014662213/250000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12323 (1/10^6) (1/10^7) ((131231/62500000000))
      (712/10000) rowEps =
      exp (-((mW 12323 : ℝ)*24646)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12323 : ℝ)*24646)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12323) (mW 12323)).real
      (goodDist 12323 (712/10000))ᶜ ≤ (108609119/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 12323) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (131231/62500000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12323 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (731013382021/1000000000000000000)
  k0 := (4042047635564103/1000000000000000000)
  k6 := (12335092534346281/1000000000000000000)
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
  norm_lower := (window_guards (n := 12323) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12323) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((108609119/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12323 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12323) internalParameters :=
  BstLean.Part227.worldPackage (n := 12323) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (108609119/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12323) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12323.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12323, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12323.frame := by
  exact frame.2.trans (by norm_num [Part259.world12323])

theorem moment_payment : internalParameters.moment ≤ Part259.world12323.moment := by
  exact moment.2.trans (by norm_num [Part259.world12323])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (148666357/125000000000) ∧
    internalParameters.frame ≤ (157748236327/250000000000) ∧
    internalParameters.moment ≤ (10194203539/1000000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12323) (Part259.world12323) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12323]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12323])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12323]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12323]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12323).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12323).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12323
#eval (do IO.println s!"P260 END 12323 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12324 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12324
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
    exp (-((mW 12324 : ℝ)*24648)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12324 : ℝ)*24648)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12324 : ℝ)*24648)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12324 : ℝ)*24648)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24648 (mW 12324) i /
      (rowEps i * e1MeanBounds 24648 (mW 12324) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24648 (mW 12324) (1/10^6) (1/10^7) rowEps ≤ (524881/250000000000) := by
  have hr : 0 ≤ firstRatio 24648 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24648 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24648) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12324 (1/10^6) (1/10^7) ((524881/250000000000))
      (712/10000) rowEps ≤ (54295497/500000000000) := by
  have hs : statisticsPayment ≤ (4088382799069/1000000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (52201305005511/500000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12324 (1/10^6) (1/10^7) ((524881/250000000000))
      (712/10000) rowEps =
      exp (-((mW 12324 : ℝ)*24648)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12324 : ℝ)*24648)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12324) (mW 12324)).real
      (goodDist 12324 (712/10000))ᶜ ≤ (54295497/500000000000) := by
  apply le_trans (concrete_distance_charge (n := 12324) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (524881/250000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12324 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (730924409461/1000000000000000000)
  k0 := (2020900823361537/500000000000000000)
  k6 := (12334592074156021/1000000000000000000)
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
  norm_lower := (window_guards (n := 12324) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12324) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((54295497/500000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12324 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12324) internalParameters :=
  BstLean.Part227.worldPackage (n := 12324) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (54295497/500000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12324) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12324.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12324, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12324.frame := by
  exact frame.2.trans (by norm_num [Part259.world12324])

theorem moment_payment : internalParameters.moment ≤ Part259.world12324.moment := by
  exact moment.2.trans (by norm_num [Part259.world12324])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1189282603/1000000000000) ∧
    internalParameters.frame ≤ (315489101563/500000000000) ∧
    internalParameters.moment ≤ (10192038831/1000000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12324) (Part259.world12324) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12324]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12324])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12324]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12324]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12324).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12324).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12324
#eval (do IO.println s!"P260 END 12324 6 {← IO.monoMsNow}" : IO Unit)
