import BstLean.Part250Charge
import BstLean.Part250Denominator
import BstLean.Part250Frame
import BstLean.Part250Productlo
import BstLean.Part250Producthi
import BstLean.Part250Noiselo
import BstLean.Part250Noisehi
import BstLean.Part250Moment

/-! The complete World package for the unchanged 12225 scalar row. -/
namespace BstLean.Part250
open Real MeasureTheory Set BstLean.Part130 BstLean.Part137 BstLean.Part140
open BstLean.Part157 BstLean.Part159 BstLean.Part192 BstLean.Part227

noncomputable def frameCertificate :
    FrameCertificate 12225 (44945/10^6) (4/10000) (712/10000) (178/10^8) (1232/10^7) where
  r0 := 739821074269/10^18
  k0 := 4066325247/10^12
  k6 := 12384435116/10^12
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
  worldParameters frameCertificate (110415/10^9) (202225/100000) (202831/100000) (1/50)

theorem product_lower : (202225/100000 : ℝ) ≤ productLower 12225 (1232/10^7) := by
  apply le_trans _ productlo.1
  norm_num

noncomputable def internalWorld : WorldPackage (paperProgram 12225) internalParameters :=
  BstLean.Part227.worldPackage (n := 12225) (sp := 44945/10^6) (p₂ := 4/10000)
    (Xc := 712/10000) (dT := 178/10^8) (eB := 1232/10^7)
    (distancePayment := 110415/10^9) (Alo := 202225/100000) (Ahi := 202831/100000)
    (ζ := 1/50) (by norm_num) (by norm_num) (by norm_num)
    distance_charge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    frameCertificate
    (window_guards (n := 12225) (eB := 1232/10^7) (by norm_num) (by norm_num)).2.2
    (by norm_num) product_lower
    (producthi.2.trans (by norm_num)) (by norm_num) (by norm_num)

theorem hidden_payment : internalParameters.hiddenCharge ≤ Part243.proposedHiddenCharge := by
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance,
    Part243.proposedHiddenCharge, width]

theorem frame_payment : internalParameters.frame ≤ Part243.rowWorldFrame := by
  exact frame.2.trans (by norm_num [Part243.rowWorldFrame])

theorem moment_payment : internalParameters.moment ≤ Part243.rowMoment := by
  exact moment.2.trans (by norm_num [Part243.rowMoment])

theorem internal_numeric_bounds : internalParameters.hiddenCharge ≤ 1193927732/10^12 ∧
    internalParameters.frame ≤ 632449686/10^9 ∧
    internalParameters.moment ≤ 104095002/10^16 := by
  refine ⟨?_, frame.2.trans (by norm_num), moment.2.trans (by norm_num)⟩
  norm_num [internalParameters, worldParameters, hiddenChargeWithDistance, width]

/-- This structure supplies every World field without a numerical or analytic premise. -/
noncomputable def worldPackage :
    WorldPackage (paperProgram 12225) (Part243.rowWorldParameters Part243.proposedHiddenCharge) where
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
    exact ⟨le_trans (by norm_num [internalParameters, worldParameters, Part243.rowWorldParameters]) hl,
      hu.trans (by norm_num [internalParameters, worldParameters, Part243.rowWorldParameters])⟩
  scale_identity := internalWorld.scale_identity
  lowerEvent := internalWorld.lowerEvent
  upperEvent := internalWorld.upperEvent
  lower_measurable := internalWorld.lower_measurable
  upper_measurable := internalWorld.upper_measurable
  noise_window := by
    intro c hc
    obtain ⟨hl, hu⟩ := internalWorld.noise_window c hc
    exact ⟨(le_trans (by norm_num [Part243.rowWorldParameters]) noiselo.1).trans hl,
      hu.trans (noisehi.2.trans (by norm_num [Part243.rowWorldParameters]))⟩
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

/-- The radius remains the scalar master's cutoff, distinct from the product window. -/
theorem radius_payment : Part243.rowMoment / Part243.rowRadius^2 ≤ 2483506131/10^12 := by
  norm_num [Part243.rowMoment, Part243.rowRadius]

end BstLean.Part250
#print BstLean.Part250.worldPackage
#print axioms BstLean.Part250.worldPackage
#print axioms BstLean.Part250.radius_payment
