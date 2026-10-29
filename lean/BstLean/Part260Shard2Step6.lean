import BstLean.Part260Shard2Step5
#eval (do IO.println s!"P260 START 12275 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12275
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
    exp (-((mW 12275 : ℝ)*24550)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12275 : ℝ)*24550)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12275 : ℝ)*24550)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12275 : ℝ)*24550)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24550 (mW 12275) i /
      (rowEps i * e1MeanBounds 24550 (mW 12275) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24550 (mW 12275) (1/10^6) (1/10^7) rowEps ≤ (2107997/1000000000000) := by
  have hr : 0 ≤ firstRatio 24550 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24550 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24550) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12275 (1/10^6) (1/10^7) ((2107997/1000000000000))
      (712/10000) rowEps ≤ (21897587/200000000000) := by
  have hs : statisticsPayment ≤ (4121760570431/1000000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (105266173126727/1000000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12275 (1/10^6) (1/10^7) ((2107997/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 12275 : ℝ)*24550)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12275 : ℝ)*24550)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12275) (mW 12275)).real
      (goodDist 12275 (712/10000))ᶜ ≤ (21897587/200000000000) := by
  apply le_trans (concrete_distance_charge (n := 12275) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (2107997/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12275 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (14706107777/20000000000000000)
  k0 := (4053896328323839/1000000000000000000)
  k6 := (6179593247840641/500000000000000000)
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
  norm_lower := (window_guards (n := 12275) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12275) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((21897587/200000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12275 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12275) internalParameters :=
  BstLean.Part227.worldPackage (n := 12275) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (21897587/200000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12275) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12275.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12275, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12275.frame := by
  exact frame.2.trans (by norm_num [Part259.world12275])

theorem moment_payment : internalParameters.moment ≤ Part259.world12275.moment := by
  exact moment.2.trans (by norm_num [Part259.world12275])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1191662583/1000000000000) ∧
    internalParameters.frame ≤ (631703467659/1000000000000) ∧
    internalParameters.moment ≤ (514943479/50000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12275) (Part259.world12275) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12275]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12275])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12275]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12275]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12275).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12275).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12275
#eval (do IO.println s!"P260 END 12275 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12276 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12276
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
    exp (-((mW 12276 : ℝ)*24552)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12276 : ℝ)*24552)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12276 : ℝ)*24552)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12276 : ℝ)*24552)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24552 (mW 12276) i /
      (rowEps i * e1MeanBounds 24552 (mW 12276) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24552 (mW 12276) (1/10^6) (1/10^7) rowEps ≤ (131739/62500000000) := by
  have hr : 0 ≤ firstRatio 24552 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24552 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24552) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12276 (1/10^6) (1/10^7) ((131739/62500000000))
      (712/10000) rowEps ≤ (109469693/1000000000000) := by
  have hs : statisticsPayment ≤ (4121074346749/1000000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (52624308722111/500000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12276 (1/10^6) (1/10^7) ((131739/62500000000))
      (712/10000) rowEps =
      exp (-((mW 12276 : ℝ)*24552)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12276 : ℝ)*24552)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12276) (mW 12276)).real
      (goodDist 12276 (712/10000))ᶜ ≤ (109469693/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 12276) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (131739/62500000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12276 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (36760777199/50000000000000000)
  k0 := (506706081717267/125000000000000000)
  k6 := (6179341548626727/500000000000000000)
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
  norm_lower := (window_guards (n := 12276) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12276) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((109469693/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12276 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12276) internalParameters :=
  BstLean.Part227.worldPackage (n := 12276) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (109469693/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12276) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12276.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12276, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12276.frame := by
  exact frame.2.trans (by norm_num [Part259.world12276])

theorem moment_payment : internalParameters.moment ≤ Part259.world12276.moment := by
  exact moment.2.trans (by norm_num [Part259.world12276])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (297903423/250000000000) ∧
    internalParameters.frame ≤ (7896107587/12500000000) ∧
    internalParameters.moment ≤ (10296673757/1000000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12276) (Part259.world12276) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12276]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12276])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12276]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12276]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12276).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12276).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12276
#eval (do IO.println s!"P260 END 12276 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12277 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12277
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
    exp (-((mW 12277 : ℝ)*24554)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12277 : ℝ)*24554)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12277 : ℝ)*24554)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12277 : ℝ)*24554)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24554 (mW 12277) i /
      (rowEps i * e1MeanBounds 24554 (mW 12277) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24554 (mW 12277) (1/10^6) (1/10^7) rowEps ≤ (42153/20000000000) := by
  have hr : 0 ≤ firstRatio 24554 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24554 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24554) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12277 (1/10^6) (1/10^7) ((42153/20000000000))
      (712/10000) rowEps ≤ (109451157/1000000000000) := by
  have hs : statisticsPayment ≤ (2060194167319/500000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (52615383613101/500000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12277 (1/10^6) (1/10^7) ((42153/20000000000))
      (712/10000) rowEps =
      exp (-((mW 12277 : ℝ)*24554)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12277 : ℝ)*24554)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12277) (mW 12277)).real
      (goodDist 12277 (712/10000))ᶜ ≤ (109451157/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 12277) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (42153/20000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12277 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (367562858703/500000000000000000)
  k0 := (810680202891969/200000000000000000)
  k6 := (12358179760331941/1000000000000000000)
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
  norm_lower := (window_guards (n := 12277) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12277) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((109451157/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12277 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12277) internalParameters :=
  BstLean.Part227.worldPackage (n := 12277) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (109451157/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12277) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12277.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12277, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12277.frame := by
  exact frame.2.trans (by norm_num [Part259.world12277])

theorem moment_payment : internalParameters.moment ≤ Part259.world12277.moment := by
  exact moment.2.trans (by norm_num [Part259.world12277])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (595782407/500000000000) ∧
    internalParameters.frame ≤ (315836874373/500000000000) ∧
    internalParameters.moment ≤ (2573619647/250000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12277) (Part259.world12277) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12277]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12277])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12277]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12277]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12277).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12277).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12277
#eval (do IO.println s!"P260 END 12277 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12278 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12278
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
    exp (-((mW 12278 : ℝ)*24556)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12278 : ℝ)*24556)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12278 : ℝ)*24556)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12278 : ℝ)*24556)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24556 (mW 12278) i /
      (rowEps i * e1MeanBounds 24556 (mW 12278) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24556 (mW 12278) (1/10^6) (1/10^7) rowEps ≤ (2107477/1000000000000) := by
  have hr : 0 ≤ firstRatio 24556 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24556 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24556) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12278 (1/10^6) (1/10^7) ((2107477/1000000000000))
      (712/10000) rowEps ≤ (27358227/250000000000) := by
  have hs : statisticsPayment ≤ (411970253401/100000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (6575825240361/62500000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12278 (1/10^6) (1/10^7) ((2107477/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 12278 : ℝ)*24556)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12278 : ℝ)*24556)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12278) (mW 12278)).real
      (goodDist 12278 (712/10000))ᶜ ≤ (27358227/250000000000) := by
  apply le_trans (concrete_distance_charge (n := 12278) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (2107477/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12278 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (735035909121/1000000000000000000)
  k0 := (4053153410476139/1000000000000000000)
  k6 := (6178838242452109/500000000000000000)
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
  norm_lower := (window_guards (n := 12278) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12278) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((27358227/250000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12278 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12278) internalParameters :=
  BstLean.Part227.worldPackage (n := 12278) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (27358227/250000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12278) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12278.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12278, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12278.frame := by
  exact frame.2.trans (by norm_num [Part259.world12278])

theorem moment_payment : internalParameters.moment ≤ Part259.world12278.moment := by
  exact moment.2.trans (by norm_num [Part259.world12278])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (23830319/20000000000) ∧
    internalParameters.frame ≤ (126331778603/200000000000) ∧
    internalParameters.moment ≤ (10292284073/1000000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12278) (Part259.world12278) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12278]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12278])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12278]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12278]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12278).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12278).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12278
#eval (do IO.println s!"P260 END 12278 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12279 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12279
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
    exp (-((mW 12279 : ℝ)*24558)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12279 : ℝ)*24558)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12279 : ℝ)*24558)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12279 : ℝ)*24558)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24558 (mW 12279) i /
      (rowEps i * e1MeanBounds 24558 (mW 12279) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24558 (mW 12279) (1/10^6) (1/10^7) rowEps ≤ (2107303/1000000000000) := by
  have hr : 0 ≤ firstRatio 24558 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24558 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24558) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12279 (1/10^6) (1/10^7) ((2107303/1000000000000))
      (712/10000) rowEps ≤ (27353591/250000000000) := by
  have hs : statisticsPayment ≤ (164760677791/40000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (105195345987003/1000000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12279 (1/10^6) (1/10^7) ((2107303/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 12279 : ℝ)*24558)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12279 : ℝ)*24558)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12279) (mW 12279)).real
      (goodDist 12279 (712/10000))ᶜ ≤ (27353591/250000000000) := by
  apply le_trans (concrete_distance_charge (n := 12279) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (2107303/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12279 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (9186826489/12500000000000000)
  k0 := (2026452920889849/500000000000000000)
  k6 := (3089293317739441/250000000000000000)
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
  norm_lower := (window_guards (n := 12279) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12279) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((27353591/250000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12279 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12279) internalParameters :=
  BstLean.Part227.worldPackage (n := 12279) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (27353591/250000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12279) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12279.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12279, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12279.frame := by
  exact frame.2.trans (by norm_num [Part259.world12279])

theorem moment_payment : internalParameters.moment ≤ Part259.world12279.moment := by
  exact moment.2.trans (by norm_num [Part259.world12279])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1191467099/1000000000000) ∧
    internalParameters.frame ≤ (78955504971/125000000000) ∧
    internalParameters.moment ≤ (2572522553/250000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12279) (Part259.world12279) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12279]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12279])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12279]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12279]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12279).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12279).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12279
#eval (do IO.println s!"P260 END 12279 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12280 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12280
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
    exp (-((mW 12280 : ℝ)*24560)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12280 : ℝ)*24560)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12280 : ℝ)*24560)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12280 : ℝ)*24560)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24560 (mW 12280) i /
      (rowEps i * e1MeanBounds 24560 (mW 12280) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24560 (mW 12280) (1/10^6) (1/10^7) rowEps ≤ (210713/100000000000) := by
  have hr : 0 ≤ firstRatio 24560 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24560 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24560) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12280 (1/10^6) (1/10^7) ((210713/100000000000))
      (712/10000) rowEps ≤ (27349027/250000000000) := by
  have hs : statisticsPayment ≤ (2059165783423/500000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (52588887459821/500000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12280 (1/10^6) (1/10^7) ((210713/100000000000))
      (712/10000) rowEps =
      exp (-((mW 12280 : ℝ)*24560)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12280 : ℝ)*24560)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12280) (mW 12280)).real
      (goodDist 12280 (712/10000))ᶜ ≤ (27349027/250000000000) := by
  apply le_trans (concrete_distance_charge (n := 12280) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (210713/100000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12280 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (734856347399/1000000000000000000)
  k0 := (4052658308365961/1000000000000000000)
  k6 := (193072970601251/15625000000000000)
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
  norm_lower := (window_guards (n := 12280) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12280) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((27349027/250000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12280 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12280) internalParameters :=
  BstLean.Part227.worldPackage (n := 12280) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (27349027/250000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12280) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12280.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12280, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12280.frame := by
  exact frame.2.trans (by norm_num [Part259.world12280])

theorem moment_payment : internalParameters.moment ≤ Part259.world12280.moment := by
  exact moment.2.trans (by norm_num [Part259.world12280])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (595709131/500000000000) ∧
    internalParameters.frame ≤ (157907297251/250000000000) ∧
    internalParameters.moment ≤ (10287897003/1000000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12280) (Part259.world12280) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12280]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12280])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12280]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12280]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12280).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12280).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12280
#eval (do IO.println s!"P260 END 12280 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12281 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12281
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
    exp (-((mW 12281 : ℝ)*24562)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12281 : ℝ)*24562)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12281 : ℝ)*24562)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12281 : ℝ)*24562)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24562 (mW 12281) i /
      (rowEps i * e1MeanBounds 24562 (mW 12281) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24562 (mW 12281) (1/10^6) (1/10^7) rowEps ≤ (526739/250000000000) := by
  have hr : 0 ≤ firstRatio 24562 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24562 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24562) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12281 (1/10^6) (1/10^7) ((526739/250000000000))
      (712/10000) rowEps ≤ (109377557/1000000000000) := by
  have hs : statisticsPayment ≤ (823529280027/200000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (5257995471561/50000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12281 (1/10^6) (1/10^7) ((526739/250000000000))
      (712/10000) rowEps =
      exp (-((mW 12281 : ℝ)*24562)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12281 : ℝ)*24562)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12281) (mW 12281)).real
      (goodDist 12281 (712/10000))ᶜ ≤ (109377557/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 12281) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (526739/250000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12281 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (22961456061/31250000000000000)
  k0 := (4052410810224847/1000000000000000000)
  k6 := (3089041756864651/250000000000000000)
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
  norm_lower := (window_guards (n := 12281) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12281) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((109377557/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12281 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12281) internalParameters :=
  BstLean.Part227.worldPackage (n := 12281) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (109377557/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12281) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12281.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12281, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12281.frame := by
  exact frame.2.trans (by norm_num [Part259.world12281])

theorem moment_payment : internalParameters.moment ≤ Part259.world12281.moment := by
  exact moment.2.trans (by norm_num [Part259.world12281])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (595684719/500000000000) ∧
    internalParameters.frame ≤ (631614340721/1000000000000) ∧
    internalParameters.moment ≤ (40178533/3906250000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12281) (Part259.world12281) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12281]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12281])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12281]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12281]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12281).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12281).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12281
#eval (do IO.println s!"P260 END 12281 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12282 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12282
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
    exp (-((mW 12282 : ℝ)*24564)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12282 : ℝ)*24564)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12282 : ℝ)*24564)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12282 : ℝ)*24564)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24564 (mW 12282) i /
      (rowEps i * e1MeanBounds 24564 (mW 12282) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24564 (mW 12282) (1/10^6) (1/10^7) rowEps ≤ (2106783/1000000000000) := by
  have hr : 0 ≤ firstRatio 24564 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24564 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24564) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12282 (1/10^6) (1/10^7) ((2106783/1000000000000))
      (712/10000) rowEps ≤ (54679647/500000000000) := by
  have hs : statisticsPayment ≤ (514620180569/125000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (52571165343961/500000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12282 (1/10^6) (1/10^7) ((2106783/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 12282 : ℝ)*24564)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12282 : ℝ)*24564)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12282) (mW 12282)).real
      (goodDist 12282 (712/10000))ᶜ ≤ (54679647/500000000000) := by
  apply le_trans (concrete_distance_charge (n := 12282) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (2106783/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12282 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (367338429387/500000000000000000)
  k0 := (4052163347349031/1000000000000000000)
  k6 := (12355663997880873/1000000000000000000)
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
  norm_lower := (window_guards (n := 12282) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12282) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((54679647/500000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12282 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12282) internalParameters :=
  BstLean.Part227.worldPackage (n := 12282) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (54679647/500000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12282) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12282.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12282, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12282.frame := by
  exact frame.2.trans (by norm_num [Part259.world12282])

theorem moment_payment : internalParameters.moment ≤ Part259.world12282.moment := by
  exact moment.2.trans (by norm_num [Part259.world12282])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1191320627/1000000000000) ∧
    internalParameters.frame ≤ (15789987373/25000000000) ∧
    internalParameters.moment ≤ (5141756273/500000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12282) (Part259.world12282) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12282]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12282])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12282]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12282]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12282).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12282).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12282
#eval (do IO.println s!"P260 END 12282 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12283 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12283
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
    exp (-((mW 12283 : ℝ)*24566)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12283 : ℝ)*24566)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12283 : ℝ)*24566)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12283 : ℝ)*24566)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24566 (mW 12283) i /
      (rowEps i * e1MeanBounds 24566 (mW 12283) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24566 (mW 12283) (1/10^6) (1/10^7) rowEps ≤ (2106609/1000000000000) := by
  have hr : 0 ≤ firstRatio 24566 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24566 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24566) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12283 (1/10^6) (1/10^7) ((2106609/1000000000000))
      (712/10000) rowEps ≤ (1708449/15625000000) := by
  have hs : statisticsPayment ≤ (1029069175003/250000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (105124457580963/1000000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12283 (1/10^6) (1/10^7) ((2106609/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 12283 : ℝ)*24566)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12283 : ℝ)*24566)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12283) (mW 12283)).real
      (goodDist 12283 (712/10000))ᶜ ≤ (1708449/15625000000) := by
  apply le_trans (concrete_distance_charge (n := 12283) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (2106609/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12283 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (36729357093/50000000000000000)
  k0 := (253244744983199/62500000000000000)
  k6 := (12355161029734367/1000000000000000000)
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
  norm_lower := (window_guards (n := 12283) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12283) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((1708449/15625000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12283 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12283) internalParameters :=
  BstLean.Part227.worldPackage (n := 12283) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (1708449/15625000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12283) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12283.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12283, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12283.frame := by
  exact frame.2.trans (by norm_num [Part259.world12283])

theorem moment_payment : internalParameters.moment ≤ Part259.world12283.moment := by
  exact moment.2.trans (by norm_num [Part259.world12283])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (119127183/100000000000) ∧
    internalParameters.frame ≤ (1578961629/2500000000) ∧
    internalParameters.moment ≤ (642582581/62500000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12283) (Part259.world12283) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12283]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12283])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12283]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12283]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12283).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12283).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12283
#eval (do IO.println s!"P260 END 12283 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12284 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12284
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
    exp (-((mW 12284 : ℝ)*24568)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12284 : ℝ)*24568)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12284 : ℝ)*24568)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12284 : ℝ)*24568)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24568 (mW 12284) i /
      (rowEps i * e1MeanBounds 24568 (mW 12284) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24568 (mW 12284) (1/10^6) (1/10^7) rowEps ≤ (526609/250000000000) := by
  have hr : 0 ≤ firstRatio 24568 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24568 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24568) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12284 (1/10^6) (1/10^7) ((526609/250000000000))
      (712/10000) rowEps ≤ (21864493/200000000000) := by
  have hs : statisticsPayment ≤ (514449020803/125000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (821147431037/7812500000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12284 (1/10^6) (1/10^7) ((526609/250000000000))
      (712/10000) rowEps =
      exp (-((mW 12284 : ℝ)*24568)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12284 : ℝ)*24568)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12284) (mW 12284)).real
      (goodDist 12284 (712/10000))ᶜ ≤ (21864493/200000000000) := by
  apply le_trans (concrete_distance_charge (n := 12284) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (526609/250000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12284 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (183624360801/250000000000000000)
  k0 := (63307320740019/15625000000000000)
  k6 := (6177329061503291/500000000000000000)
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
  norm_lower := (window_guards (n := 12284) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12284) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((21864493/200000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12284 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12284) internalParameters :=
  BstLean.Part227.worldPackage (n := 12284) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (21864493/200000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12284) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12284.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12284, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12284.frame := by
  exact frame.2.trans (by norm_num [Part259.world12284])

theorem moment_payment : internalParameters.moment ≤ Part259.world12284.moment := by
  exact moment.2.trans (by norm_num [Part259.world12284])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (595611523/500000000000) ∧
    internalParameters.frame ≤ (631569810759/1000000000000) ∧
    internalParameters.moment ≤ (5139565349/500000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12284) (Part259.world12284) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12284]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12284])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12284]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12284]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12284).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12284).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12284
#eval (do IO.println s!"P260 END 12284 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12285 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12285
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
    exp (-((mW 12285 : ℝ)*24570)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12285 : ℝ)*24570)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12285 : ℝ)*24570)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12285 : ℝ)*24570)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24570 (mW 12285) i /
      (rowEps i * e1MeanBounds 24570 (mW 12285) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24570 (mW 12285) (1/10^6) (1/10^7) rowEps ≤ (1053131/500000000000) := by
  have hr : 0 ≤ firstRatio 24570 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24570 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24570) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12285 (1/10^6) (1/10^7) ((1053131/500000000000))
      (712/10000) rowEps ≤ (1093039/10000000000) := by
  have hs : statisticsPayment ≤ (4114907843701/1000000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (105088990458363/1000000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12285 (1/10^6) (1/10^7) ((1053131/500000000000))
      (712/10000) rowEps =
      exp (-((mW 12285 : ℝ)*24570)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12285 : ℝ)*24570)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12285) (mW 12285)).real
      (goodDist 12285 (712/10000))ᶜ ≤ (1093039/10000000000) := by
  apply le_trans (concrete_distance_charge (n := 12285) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (1053131/500000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12285 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (367203881401/500000000000000000)
  k0 := (506427646279319/125000000000000000)
  k6 := (617707763884251/50000000000000000)
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
  norm_lower := (window_guards (n := 12285) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12285) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((1093039/10000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12285 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12285) internalParameters :=
  BstLean.Part227.worldPackage (n := 12285) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (1093039/10000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12285) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12285.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12285, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12285.frame := by
  exact frame.2.trans (by norm_num [Part259.world12285])

theorem moment_payment : internalParameters.moment ≤ Part259.world12285.moment := by
  exact moment.2.trans (by norm_num [Part259.world12285])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (297793569/250000000000) ∧
    internalParameters.frame ≤ (631554972397/1000000000000) ∧
    internalParameters.moment ≤ (642308797/62500000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12285) (Part259.world12285) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12285]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12285])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12285]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12285]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12285).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12285).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12285
#eval (do IO.println s!"P260 END 12285 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12286 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12286
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
    exp (-((mW 12286 : ℝ)*24572)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12286 : ℝ)*24572)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12286 : ℝ)*24572)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12286 : ℝ)*24572)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24572 (mW 12286) i /
      (rowEps i * e1MeanBounds 24572 (mW 12286) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24572 (mW 12286) (1/10^6) (1/10^7) rowEps ≤ (2106089/1000000000000) := by
  have hr : 0 ≤ firstRatio 24572 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24572 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24572) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12286 (1/10^6) (1/10^7) ((2106089/1000000000000))
      (712/10000) rowEps ≤ (54642811/500000000000) := by
  have hs : statisticsPayment ≤ (1028555932939/250000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (52535698198111/500000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12286 (1/10^6) (1/10^7) ((2106089/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 12286 : ℝ)*24572)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12286 : ℝ)*24572)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12286) (mW 12286)).real
      (goodDist 12286 (712/10000))ᶜ ≤ (54642811/500000000000) := by
  apply le_trans (concrete_distance_charge (n := 12286) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (2106089/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12286 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (734318100647/1000000000000000000)
  k0 := (4051173848338337/1000000000000000000)
  k6 := (2470730498751437/200000000000000000)
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
  norm_lower := (window_guards (n := 12286) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12286) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((54642811/500000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12286 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12286) internalParameters :=
  BstLean.Part227.worldPackage (n := 12286) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (54642811/500000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12286) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12286.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12286, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12286.frame := by
  exact frame.2.trans (by norm_num [Part259.world12286])

theorem moment_payment : internalParameters.moment ≤ Part259.world12286.moment := by
  exact moment.2.trans (by norm_num [Part259.world12286])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1191125519/1000000000000) ∧
    internalParameters.frame ≤ (126308027303/200000000000) ∧
    internalParameters.moment ≤ (10274751459/1000000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12286) (Part259.world12286) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12286]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12286])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12286]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12286]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12286).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12286).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12286
#eval (do IO.println s!"P260 END 12286 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12287 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12287
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
    exp (-((mW 12287 : ℝ)*24574)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12287 : ℝ)*24574)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12287 : ℝ)*24574)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12287 : ℝ)*24574)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24574 (mW 12287) i /
      (rowEps i * e1MeanBounds 24574 (mW 12287) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24574 (mW 12287) (1/10^6) (1/10^7) rowEps ≤ (526479/250000000000) := by
  have hr : 0 ≤ firstRatio 24574 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24574 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24574) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12287 (1/10^6) (1/10^7) ((526479/250000000000))
      (712/10000) rowEps ≤ (5463367/50000000000) := by
  have hs : statisticsPayment ≤ (8227079661/2000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (105053798498497/1000000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12287 (1/10^6) (1/10^7) ((526479/250000000000))
      (712/10000) rowEps =
      exp (-((mW 12287 : ℝ)*24574)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12287 : ℝ)*24574)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12287) (mW 12287)).real
      (goodDist 12287 (712/10000))ᶜ ≤ (5463367/50000000000) := by
  apply le_trans (concrete_distance_charge (n := 12287) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (526479/250000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12287 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (22944639273/31250000000000000)
  k0 := (16203706246683/4000000000000000)
  k6 := (2470629954242117/200000000000000000)
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
  norm_lower := (window_guards (n := 12287) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12287) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((5463367/50000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12287 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12287) internalParameters :=
  BstLean.Part227.worldPackage (n := 12287) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (5463367/50000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12287) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12287.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12287, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12287.frame := by
  exact frame.2.trans (by norm_num [Part259.world12287])

theorem moment_payment : internalParameters.moment ≤ Part259.world12287.moment := by
  exact moment.2.trans (by norm_num [Part259.world12287])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (47643071/40000000000) ∧
    internalParameters.frame ≤ (63152530311/100000000000) ∧
    internalParameters.moment ≤ (10272562817/1000000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12287) (Part259.world12287) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12287]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12287])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12287]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12287]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12287).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12287).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12287
#eval (do IO.println s!"P260 END 12287 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12288 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12288
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
    exp (-((mW 12288 : ℝ)*24576)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12288 : ℝ)*24576)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12288 : ℝ)*24576)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12288 : ℝ)*24576)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24576 (mW 12288) i /
      (rowEps i * e1MeanBounds 24576 (mW 12288) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24576 (mW 12288) (1/10^6) (1/10^7) rowEps ≤ (2105743/1000000000000) := by
  have hr : 0 ≤ firstRatio 24576 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24576 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24576) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12288 (1/10^6) (1/10^7) ((2105743/1000000000000))
      (712/10000) rowEps ≤ (54624527/500000000000) := by
  have hs : statisticsPayment ≤ (822571227969/200000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (52518098383959/500000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12288 (1/10^6) (1/10^7) ((2105743/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 12288 : ℝ)*24576)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12288 : ℝ)*24576)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12288) (mW 12288)).real
      (goodDist 12288 (712/10000))ᶜ ≤ (54624527/500000000000) := by
  apply le_trans (concrete_distance_charge (n := 12288) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (2105743/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12288 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (367069415531/500000000000000000)
  k0 := (405067931021893/100000000000000000)
  k6 := (3088161777508183/250000000000000000)
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
  norm_lower := (window_guards (n := 12288) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12288) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((54624527/500000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12288 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12288) internalParameters :=
  BstLean.Part227.worldPackage (n := 12288) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (54624527/500000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12288) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12288.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12288, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12288.frame := by
  exact frame.2.trans (by norm_num [Part259.world12288])

theorem moment_payment : internalParameters.moment ≤ Part259.world12288.moment := by
  exact moment.2.trans (by norm_num [Part259.world12288])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (238205609/200000000000) ∧
    internalParameters.frame ≤ (315755236091/500000000000) ∧
    internalParameters.moment ≤ (5135187413/500000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12288) (Part259.world12288) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12288]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12288])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12288]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12288]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12288).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12288).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12288
#eval (do IO.println s!"P260 END 12288 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12289 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12289
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
    exp (-((mW 12289 : ℝ)*24578)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12289 : ℝ)*24578)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12289 : ℝ)*24578)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12289 : ℝ)*24578)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24578 (mW 12289) i /
      (rowEps i * e1MeanBounds 24578 (mW 12289) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24578 (mW 12289) (1/10^6) (1/10^7) rowEps ≤ (2105569/1000000000000) := by
  have hr : 0 ≤ firstRatio 24578 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24578 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24578) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12289 (1/10^6) (1/10^7) ((2105569/1000000000000))
      (712/10000) rowEps ≤ (4369219/40000000000) := by
  have hs : statisticsPayment ≤ (514021582463/125000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (105018300845417/1000000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12289 (1/10^6) (1/10^7) ((2105569/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 12289 : ℝ)*24578)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12289 : ℝ)*24578)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12289) (mW 12289)).real
      (goodDist 12289 (712/10000))ᶜ ≤ (4369219/40000000000) := by
  apply le_trans (concrete_distance_charge (n := 12289) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (2105569/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12289 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (734049223621/1000000000000000000)
  k0 := (405043209397829/100000000000000000)
  k6 := (6176072255105571/500000000000000000)
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
  norm_lower := (window_guards (n := 12289) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12289) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((4369219/40000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12289 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12289) internalParameters :=
  BstLean.Part227.worldPackage (n := 12289) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (4369219/40000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12289) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12289.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12289, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12289.frame := by
  exact frame.2.trans (by norm_num [Part259.world12289])

theorem moment_payment : internalParameters.moment ≤ Part259.world12289.moment := by
  exact moment.2.trans (by norm_num [Part259.world12289])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (4652263/3906250000) ∧
    internalParameters.frame ≤ (631495643731/1000000000000) ∧
    internalParameters.moment ≤ (5134093743/500000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12289) (Part259.world12289) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12289]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12289])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12289]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12289]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12289).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12289).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12289
#eval (do IO.println s!"P260 END 12289 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12290 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12290
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
    exp (-((mW 12290 : ℝ)*24580)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12290 : ℝ)*24580)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12290 : ℝ)*24580)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12290 : ℝ)*24580)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24580 (mW 12290) i /
      (rowEps i * e1MeanBounds 24580 (mW 12290) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24580 (mW 12290) (1/10^6) (1/10^7) rowEps ≤ (526349/250000000000) := by
  have hr : 0 ≤ firstRatio 24580 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24580 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24580) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12290 (1/10^6) (1/10^7) ((526349/250000000000))
      (712/10000) rowEps ≤ (54606091/500000000000) := by
  have hs : statisticsPayment ≤ (4111489389989/1000000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (105000691482933/1000000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12290 (1/10^6) (1/10^7) ((526349/250000000000))
      (712/10000) rowEps =
      exp (-((mW 12290 : ℝ)*24580)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12290 : ℝ)*24580)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12290) (mW 12290)).real
      (goodDist 12290 (712/10000))ᶜ ≤ (54606091/500000000000) := by
  apply le_trans (concrete_distance_charge (n := 12290) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (526349/250000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12290 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (733959634407/1000000000000000000)
  k0 := (4050184912938723/1000000000000000000)
  k6 := (3087910492933333/250000000000000000)
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
  norm_lower := (window_guards (n := 12290) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12290) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((54606091/500000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12290 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12290) internalParameters :=
  BstLean.Part227.worldPackage (n := 12290) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (54606091/500000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12290) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12290.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12290, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12290.frame := by
  exact frame.2.trans (by norm_num [Part259.world12290])

theorem moment_payment : internalParameters.moment ≤ Part259.world12290.moment := by
  exact moment.2.trans (by norm_num [Part259.world12290])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (18608291/15625000000) ∧
    internalParameters.frame ≤ (157870204439/250000000000) ∧
    internalParameters.moment ≤ (10266000797/1000000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12290) (Part259.world12290) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12290]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12290])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12290]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12290]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12290).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12290).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12290
#eval (do IO.println s!"P260 END 12290 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12291 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12291
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
    exp (-((mW 12291 : ℝ)*24582)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12291 : ℝ)*24582)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12291 : ℝ)*24582)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12291 : ℝ)*24582)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24582 (mW 12291) i /
      (rowEps i * e1MeanBounds 24582 (mW 12291) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24582 (mW 12291) (1/10^6) (1/10^7) rowEps ≤ (2105223/1000000000000) := by
  have hr : 0 ≤ firstRatio 24582 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24582 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24582) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12291 (1/10^6) (1/10^7) ((2105223/1000000000000))
      (712/10000) rowEps ≤ (54596943/500000000000) := by
  have hs : statisticsPayment ≤ (1027701582653/250000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (104983078295821/1000000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12291 (1/10^6) (1/10^7) ((2105223/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 12291 : ℝ)*24582)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12291 : ℝ)*24582)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12291) (mW 12291)).real
      (goodDist 12291 (712/10000))ᶜ ≤ (54596943/500000000000) := by
  apply le_trans (concrete_distance_charge (n := 12291) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (2105223/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12291 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (91733757927/125000000000000000)
  k0 := (2024968883547819/500000000000000000)
  k6 := (6175569747293413/500000000000000000)
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
  norm_lower := (window_guards (n := 12291) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12291) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((54596943/500000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12291 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12291) internalParameters :=
  BstLean.Part227.worldPackage (n := 12291) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (54596943/500000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12291) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12291.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12291, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12291.frame := by
  exact frame.2.trans (by norm_num [Part259.world12291])

theorem moment_payment : internalParameters.moment ≤ Part259.world12291.moment := by
  exact moment.2.trans (by norm_num [Part259.world12291])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1190881933/1000000000000) ∧
    internalParameters.frame ≤ (631465994257/1000000000000) ∧
    internalParameters.moment ≤ (5131907379/500000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12291) (Part259.world12291) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12291]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12291])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12291]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12291]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12291).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12291).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12291
#eval (do IO.println s!"P260 END 12291 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12292 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12292
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
    exp (-((mW 12292 : ℝ)*24584)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12292 : ℝ)*24584)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12292 : ℝ)*24584)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12292 : ℝ)*24584)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24584 (mW 12292) i /
      (rowEps i * e1MeanBounds 24584 (mW 12292) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24584 (mW 12292) (1/10^6) (1/10^7) rowEps ≤ (42101/20000000000) := by
  have hr : 0 ≤ firstRatio 24584 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24584 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24584) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12292 (1/10^6) (1/10^7) ((42101/20000000000))
      (712/10000) rowEps ≤ (54587793/500000000000) := by
  have hs : statisticsPayment ≤ (1027530870371/250000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (20993092257363/200000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12292 (1/10^6) (1/10^7) ((42101/20000000000))
      (712/10000) rowEps =
      exp (-((mW 12292 : ℝ)*24584)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12292 : ℝ)*24584)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12292) (mW 12292)).real
      (goodDist 12292 (712/10000))ᶜ ≤ (54587793/500000000000) := by
  apply le_trans (concrete_distance_charge (n := 12292) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (42101/20000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12292 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (733780510641/1000000000000000000)
  k0 := (2024845328218081/500000000000000000)
  k6 := (12350637078759149/1000000000000000000)
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
  norm_lower := (window_guards (n := 12292) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12292) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((54587793/500000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12292 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12292) internalParameters :=
  BstLean.Part227.worldPackage (n := 12292) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (54587793/500000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12292) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12292.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12292, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12292.frame := by
  exact frame.2.trans (by norm_num [Part259.world12292])

theorem moment_payment : internalParameters.moment ≤ Part259.world12292.moment := by
  exact moment.2.trans (by norm_num [Part259.world12292])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (148854157/125000000000) ∧
    internalParameters.frame ≤ (39465698327/62500000000) ∧
    internalParameters.moment ≤ (1026162937/100000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12292) (Part259.world12292) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12292]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12292])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12292]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12292]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12292).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12292).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12292
#eval (do IO.println s!"P260 END 12292 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12293 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12293
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
    exp (-((mW 12293 : ℝ)*24586)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12293 : ℝ)*24586)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12293 : ℝ)*24586)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12293 : ℝ)*24586)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24586 (mW 12293) i /
      (rowEps i * e1MeanBounds 24586 (mW 12293) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24586 (mW 12293) (1/10^6) (1/10^7) rowEps ≤ (2104877/1000000000000) := by
  have hr : 0 ≤ firstRatio 24586 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24586 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24586) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12293 (1/10^6) (1/10^7) ((2104877/1000000000000))
      (712/10000) rowEps ≤ (109157283/1000000000000) := by
  have hs : statisticsPayment ≤ (102736021063/25000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (26236960114663/250000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12293 (1/10^6) (1/10^7) ((2104877/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 12293 : ℝ)*24586)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12293 : ℝ)*24586)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12293) (mW 12293)).real
      (goodDist 12293 (712/10000))ᶜ ≤ (109157283/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 12293) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (2104877/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12293 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (366845488039/500000000000000000)
  k0 := (2024721790477849/500000000000000000)
  k6 := (12350134724237831/1000000000000000000)
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
  norm_lower := (window_guards (n := 12293) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12293) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((109157283/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12293 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12293) internalParameters :=
  BstLean.Part227.worldPackage (n := 12293) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (109157283/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12293) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12293.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12293, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12293.frame := by
  exact frame.2.trans (by norm_num [Part259.world12293])

theorem moment_payment : internalParameters.moment ≤ Part259.world12293.moment := by
  exact moment.2.trans (by norm_num [Part259.world12293])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1190784593/1000000000000) ∧
    internalParameters.frame ≤ (631436354681/1000000000000) ∧
    internalParameters.moment ≤ (1282430579/125000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12293) (Part259.world12293) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12293]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12293])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12293]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12293]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12293).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12293).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12293
#eval (do IO.println s!"P260 END 12293 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12294 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12294
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
    exp (-((mW 12294 : ℝ)*24588)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12294 : ℝ)*24588)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12294 : ℝ)*24588)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12294 : ℝ)*24588)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24588 (mW 12294) i /
      (rowEps i * e1MeanBounds 24588 (mW 12294) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24588 (mW 12294) (1/10^6) (1/10^7) rowEps ≤ (16443/7812500000) := by
  have hr : 0 ≤ firstRatio 24588 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24588 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24588) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12294 (1/10^6) (1/10^7) ((16443/7812500000))
      (712/10000) rowEps ≤ (3410593/31250000000) := by
  have hs : statisticsPayment ≤ (410875841363/100000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (10493021581407/100000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12294 (1/10^6) (1/10^7) ((16443/7812500000))
      (712/10000) rowEps =
      exp (-((mW 12294 : ℝ)*24588)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12294 : ℝ)*24588)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12294) (mW 12294)).real
      (goodDist 12294 (712/10000))ᶜ ≤ (3410593/31250000000) := by
  apply le_trans (concrete_distance_charge (n := 12294) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (16443/7812500000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12294 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (366800729861/500000000000000000)
  k0 := (809839308129377/200000000000000000)
  k6 := (3087408107752601/250000000000000000)
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
  norm_lower := (window_guards (n := 12294) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12294) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((3410593/31250000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12294 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12294) internalParameters :=
  BstLean.Part227.worldPackage (n := 12294) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (3410593/31250000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12294) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12294.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12294, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12294.frame := by
  exact frame.2.trans (by norm_num [Part259.world12294])

theorem moment_payment : internalParameters.moment ≤ Part259.world12294.moment := by
  exact moment.2.trans (by norm_num [Part259.world12294])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (595367971/500000000000) ∧
    internalParameters.frame ≤ (631421538603/1000000000000) ∧
    internalParameters.moment ≤ (1252107/122070312500000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12294) (Part259.world12294) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12294]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12294])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12294]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12294]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12294).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12294).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12294
#eval (do IO.println s!"P260 END 12294 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12295 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12295
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
    exp (-((mW 12295 : ℝ)*24590)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12295 : ℝ)*24590)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12295 : ℝ)*24590)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12295 : ℝ)*24590)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24590 (mW 12295) i /
      (rowEps i * e1MeanBounds 24590 (mW 12295) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24590 (mW 12295) (1/10^6) (1/10^7) rowEps ≤ (2104531/1000000000000) := by
  have hr : 0 ≤ firstRatio 24590 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24590 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24590) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12295 (1/10^6) (1/10^7) ((2104531/1000000000000))
      (712/10000) rowEps ≤ (21824133/200000000000) := by
  have hs : statisticsPayment ≤ (513509524341/125000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (3278518354869/31250000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12295 (1/10^6) (1/10^7) ((2104531/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 12295 : ℝ)*24590)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12295 : ℝ)*24590)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12295) (mW 12295)).real
      (goodDist 12295 (712/10000))ᶜ ≤ (21824133/200000000000) := by
  apply le_trans (concrete_distance_charge (n := 12295) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (2104531/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12295 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (733511961567/1000000000000000000)
  k0 := (4048949535499603/1000000000000000000)
  k6 := (6174565099532203/500000000000000000)
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
  norm_lower := (window_guards (n := 12295) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12295) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((21824133/200000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12295 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12295) internalParameters :=
  BstLean.Part227.worldPackage (n := 12295) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (21824133/200000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12295) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12295.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12295, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12295.frame := by
  exact frame.2.trans (by norm_num [Part259.world12295])

theorem moment_payment : internalParameters.moment ≤ Part259.world12295.moment := by
  exact moment.2.trans (by norm_num [Part259.world12295])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (238137461/200000000000) ∧
    internalParameters.frame ≤ (315703362499/500000000000) ∧
    internalParameters.moment ≤ (2051015421/200000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12295) (Part259.world12295) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12295]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12295])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12295]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12295]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12295).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12295).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12295
#eval (do IO.println s!"P260 END 12295 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12296 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12296
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
    exp (-((mW 12296 : ℝ)*24592)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12296 : ℝ)*24592)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12296 : ℝ)*24592)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12296 : ℝ)*24592)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24592 (mW 12296) i /
      (rowEps i * e1MeanBounds 24592 (mW 12296) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24592 (mW 12296) (1/10^6) (1/10^7) rowEps ≤ (1052179/500000000000) := by
  have hr : 0 ≤ firstRatio 24592 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24592 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24592) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12296 (1/10^6) (1/10^7) ((1052179/500000000000))
      (712/10000) rowEps ≤ (109102351/1000000000000) := by
  have hs : statisticsPayment ≤ (2053697092863/500000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (104894955086603/1000000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12296 (1/10^6) (1/10^7) ((1052179/500000000000))
      (712/10000) rowEps =
      exp (-((mW 12296 : ℝ)*24592)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12296 : ℝ)*24592)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12296) (mW 12296)).real
      (goodDist 12296 (712/10000))ᶜ ≤ (109102351/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 12296) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (1052179/500000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12296 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (91677810201/125000000000000000)
  k0 := (2024351282753243/500000000000000000)
  k6 := (12348628028387377/1000000000000000000)
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
  norm_lower := (window_guards (n := 12296) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12296) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((109102351/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12296 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12296) internalParameters :=
  BstLean.Part227.worldPackage (n := 12296) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (109102351/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12296) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12296.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12296, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12296.frame := by
  exact frame.2.trans (by norm_num [Part259.world12296])

theorem moment_payment : internalParameters.moment ≤ Part259.world12296.moment := by
  exact moment.2.trans (by norm_num [Part259.world12296])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1190638681/1000000000000) ∧
    internalParameters.frame ≤ (126278382773/200000000000) ∧
    internalParameters.moment ≤ (2050578863/200000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12296) (Part259.world12296) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12296]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12296])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12296]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12296]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12296).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12296).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12296
#eval (do IO.println s!"P260 END 12296 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12297 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12297
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
    exp (-((mW 12297 : ℝ)*24594)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12297 : ℝ)*24594)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12297 : ℝ)*24594)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12297 : ℝ)*24594)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24594 (mW 12297) i /
      (rowEps i * e1MeanBounds 24594 (mW 12297) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24594 (mW 12297) (1/10^6) (1/10^7) rowEps ≤ (420837/200000000000) := by
  have hr : 0 ≤ firstRatio 24594 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24594 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24594) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12297 (1/10^6) (1/10^7) ((420837/200000000000))
      (712/10000) rowEps ≤ (109084033/1000000000000) := by
  have hs : statisticsPayment ≤ (513339048317/125000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (104877319009199/1000000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12297 (1/10^6) (1/10^7) ((420837/200000000000))
      (712/10000) rowEps =
      exp (-((mW 12297 : ℝ)*24594)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12297 : ℝ)*24594)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12297) (mW 12297)).real
      (goodDist 12297 (712/10000))ᶜ ≤ (109084033/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 12297) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (420837/200000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12297 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (733333019841/1000000000000000000)
  k0 := (4048455630662927/1000000000000000000)
  k6 := (617406295948343/50000000000000000)
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
  norm_lower := (window_guards (n := 12297) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12297) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((109084033/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12297 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12297) internalParameters :=
  BstLean.Part227.worldPackage (n := 12297) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (109084033/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12297) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12297.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12297, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12297.frame := by
  exact frame.2.trans (by norm_num [Part259.world12297])

theorem moment_payment : internalParameters.moment ≤ Part259.world12297.moment := by
  exact moment.2.trans (by norm_num [Part259.world12297])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (1190590071/1000000000000) ∧
    internalParameters.frame ≤ (157844276301/250000000000) ∧
    internalParameters.moment ≤ (410028487/40000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12297) (Part259.world12297) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12297]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12297])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12297]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12297]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12297).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12297).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12297
#eval (do IO.println s!"P260 END 12297 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12298 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12298
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
    exp (-((mW 12298 : ℝ)*24596)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12298 : ℝ)*24596)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12298 : ℝ)*24596)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12298 : ℝ)*24596)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24596 (mW 12298) i /
      (rowEps i * e1MeanBounds 24596 (mW 12298) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24596 (mW 12298) (1/10^6) (1/10^7) rowEps ≤ (526003/250000000000) := by
  have hr : 0 ≤ firstRatio 24596 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24596 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24596) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12298 (1/10^6) (1/10^7) ((526003/250000000000))
      (712/10000) rowEps ≤ (109065711/1000000000000) := by
  have hs : statisticsPayment ≤ (256626924817/62500000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (52429839563169/500000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12298 (1/10^6) (1/10^7) ((526003/250000000000))
      (712/10000) rowEps =
      exp (-((mW 12298 : ℝ)*24596)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12298 : ℝ)*24596)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12298) (mW 12298)).real
      (goodDist 12298 (712/10000))ᶜ ≤ (109065711/1000000000000) := by
  apply le_trans (concrete_distance_charge (n := 12298) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (526003/250000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12298 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (733243576259/1000000000000000000)
  k0 := (4048208730956033/1000000000000000000)
  k6 := (6173811935395201/500000000000000000)
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
  norm_lower := (window_guards (n := 12298) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12298) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((109065711/1000000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12298 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12298) internalParameters :=
  BstLean.Part227.worldPackage (n := 12298) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (109065711/1000000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12298) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12298.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12298, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12298.frame := by
  exact frame.2.trans (by norm_num [Part259.world12298])

theorem moment_payment : internalParameters.moment ≤ Part259.world12298.moment := by
  exact moment.2.trans (by norm_num [Part259.world12298])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (595270737/500000000000) ∧
    internalParameters.frame ≤ (631362299013/1000000000000) ∧
    internalParameters.moment ≤ (10248530683/1000000000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12298) (Part259.world12298) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12298]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12298])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12298]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12298]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12298).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12298).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12298
#eval (do IO.println s!"P260 END 12298 6 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12299 6 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12299
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
    exp (-((mW 12299 : ℝ)*24598)/2 * ((1/10^6)-log (1+1/10^6))) +
    exp (-((mW 12299 : ℝ)*24598)/2 * (-(1/10^6)-log (1-1/10^6))) ≤ 1/10^12 := by
  have hp : -((mW 12299 : ℝ)*24598)/2 * ((1/10^6)-log (1+1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_plus]
  have hm : -((mW 12299 : ℝ)*24598)/2 * (-(1/10^6)-log (1-1/10^6)) ≤ -100 := by
    rw [width]
    nlinarith only [logarithm_minus]
  calc
    _ ≤ exp (-100) + exp (-100) := add_le_add (exp_le_exp.mpr hp) (exp_le_exp.mpr hm)
    _ ≤ 1/10^12 := by
      have h := BstLean.Part243.row_sampling
      unfold BstLean.Part243.rowSamplingAllowance at h
      linarith

theorem statistics_identity :
    (∑ i : Fin 4, e1Variances 24598 (mW 12299) i /
      (rowEps i * e1MeanBounds 24598 (mW 12299) i)^2) = statisticsPayment := by
  simp [Fin.sum_univ_succ, e1Variances, e1MeanBounds, rowEps, statisticsPayment]
  <;> ring

theorem mean_certificate :
    e1MeanBound 24598 (mW 12299) (1/10^6) (1/10^7) rowEps ≤ (2103839/1000000000000) := by
  have hr : 0 ≤ firstRatio 24598 := le_trans (by norm_num) ratio.1
  have hr' : firstRatio 24598 ≤ 3/4 := ratio.2.trans (by norm_num)
  have hK : endpointPolynomial (firstRatio 24598) ≤ 20474/100000 :=
    endpoint.2.trans (by norm_num)
  exact (mean_majorant hr hr' hK).trans (meanvalue.2.trans (by norm_num))

theorem direct_payment :
    directDistancePayment 12299 (1/10^6) (1/10^7) ((2103839/1000000000000))
      (712/10000) rowEps ≤ (54523693/500000000000) := by
  have hs : statisticsPayment ≤ (1026337354311/250000000000000000) := statpay.2.trans (by norm_num)
  have hc : conditionalValue ≤ (104842035440761/1000000000000000000) := conditional.2.trans (by norm_num)
  have hi : directDistancePayment 12299 (1/10^6) (1/10^7) ((2103839/1000000000000))
      (712/10000) rowEps =
      exp (-((mW 12299 : ℝ)*24598)/2 * ((1/10^6)-log (1+1/10^6))) +
      exp (-((mW 12299 : ℝ)*24598)/2 * (-(1/10^6)-log (1-1/10^6))) +
      statisticsPayment + 1/10^7 + conditionalValue := by
    unfold directDistancePayment e1Charge conditionalValue
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    rw [statistics_identity]
  rw [hi]
  linarith only [norm_charge, hs, hc]

theorem distance_charge :
    (BstLean.Part136.hidGauss (2*12299) (mW 12299)).real
      (goodDist 12299 (712/10000))ᶜ ≤ (54523693/500000000000) := by
  apply le_trans (concrete_distance_charge (n := 12299) (by norm_num)
    (εω := 1/10^6) (ph := 1/10^7) (Δ := (2103839/1000000000000)) (ε := rowEps)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [rowEps]) (by norm_num)
    mean_certificate (by norm_num))
  exact direct_payment

noncomputable def frameCertificate :
    FrameCertificate 12299 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := (366577075429/500000000000000000)
  k0 := (505995233297649/125000000000000000)
  k6 := (6173560941922777/500000000000000000)
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
  norm_lower := (window_guards (n := 12299) (by norm_num) (by norm_num)).1
  norm_separation := (window_guards (n := 12299) (by norm_num) (by norm_num)).2.1
  denominator := le_trans (by norm_num) denominator.1

noncomputable def internalParameters : WorldParameters :=
  worldParameters frameCertificate ((54523693/500000000000)) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12299 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12299) internalParameters :=
  BstLean.Part227.worldPackage (n := 12299) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := (54523693/500000000000)) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12299) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part259.world12299.hiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part259.world12299, width]

theorem frame_payment : internalParameters.frame ≤ Part259.world12299.frame := by
  exact frame.2.trans (by norm_num [Part259.world12299])

theorem moment_payment : internalParameters.moment ≤ Part259.world12299.moment := by
  exact moment.2.trans (by norm_num [Part259.world12299])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ (119049289/100000000000) ∧
    internalParameters.frame ≤ (631347495293/1000000000000) ∧
    internalParameters.moment ≤ (128079373/12500000000000000) := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12299) (Part259.world12299) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part259.world12299]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part259.world12299])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part259.world12299]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part259.world12299]))⟩
  frame_bound := by
    intro c hc w
    apply (internalWorld.frame_bound c hc w).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact div_le_div_of_nonneg_right frame_payment (by norm_num)
  moment_integrable := internalWorld.moment_integrable
  restricted_moment := internalWorld.restricted_moment.trans moment_payment

/-- The package uses the original angle events, with their existing payments. -/
theorem angle_events : worldPackage.lowerEvent = Ethm (paperProgram 12299).design.toCentres ∧
    worldPackage.upperEvent = Ethp (paperProgram 12299).design.toCentres := ⟨rfl, rfl⟩

end BstLean.Part260.Row12299
#eval (do IO.println s!"P260 END 12299 6 {← IO.monoMsNow}" : IO Unit)
