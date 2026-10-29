import BstLean.Part271AngularScale

/-! Keep the dimension powers in the first-layer and distance formulas explicit. -/
namespace BstLean.Part271.R3
open Real BstLean.Part130 BstLean.Part137 BstLean.Part218 BstLean.Part227
open BstLean.Part250 (rowEps meanMajorantValue)

noncomputable def scaleFactor (N m : ℕ) : ℝ := (m : ℝ)/((N : ℝ)*√(N : ℝ))

noncomputable def frobCore (N m : ℕ) : ℝ :=
  √((1+1/10^5)*(1+(N : ℝ)/(m : ℝ)+1/(m : ℝ))/4) +
  √((1/4-firstRatio N/2)^2*4*(1+1/1000)*(1+2/(N : ℝ))*((N : ℝ)/(m : ℝ)) +
    (1+1/1000)*4*(1-1/(m : ℝ))*j2Core N/(N : ℝ))

noncomputable def nuCore (N m : ℕ) : ℝ :=
  √((1+1/1000+3)*(5-2/(N : ℝ))*((N : ℝ)/(m : ℝ)))/(1-1/10^6)

noncomputable def tCore (N m : ℕ) : ℝ :=
  (frobCore N m^2 + 2*firstRatio N*(1+2/(N : ℝ))*(1-firstRatio N)*
    ((N : ℝ)/(m : ℝ))/(1/10^7))/(1-1/10^6)^2

noncomputable def meanCore (N m : ℕ) : ℝ :=
  (20474/100000)*(√(tCore N m)+√2*nuCore N m)^2 +
    6*nuCore N m^2+(√2+2)*nuCore N m*√(tCore N m)

noncomputable def covarianceCore (N m : ℕ) : ℝ :=
  frobCore N m/((1-1/10^6)*√(N : ℝ)*(1-firstRatio N))

noncomputable def conditionalCore (N m : ℕ) (C : ℝ) : ℝ :=
  (4*(1+1/10^6)^2*√(C/2)*((1-firstRatio N)*√(1-firstRatio N)*
    sixthConstant (covarianceCore N m)))/(712/10000-(1+1/10^6)*C)^2

theorem scaleFactor_sq {N m : ℕ} (hN : 0 < (N : ℝ)) :
    scaleFactor N m^2 = (m : ℝ)^2/(N : ℝ)^3 := by
  unfold scaleFactor
  rw [div_pow, mul_pow, Real.sq_sqrt hN.le]
  ring

theorem sqrt_scaleFactor (N m : ℕ) (x : ℝ) :
    √(scaleFactor N m^2*x) = scaleFactor N m*√x := by
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq
    (show 0 ≤ scaleFactor N m by unfold scaleFactor; positivity)]

theorem frob_scale {N m : ℕ} (hN : 0 < (N : ℝ)) (hm : 0 < (m : ℝ)) :
    e1FrobBound N m rowEps = scaleFactor N m*frobCore N m := by
  have h1 : (1+1/10^5)*((m : ℝ)*N*(m+N+1))/(4*(N : ℝ)^4) =
      scaleFactor N m^2*((1+1/10^5)*(1+(N : ℝ)/(m : ℝ)+1/(m : ℝ))/4) := by
    rw [scaleFactor_sq hN]
    field_simp [ne_of_gt hN, ne_of_gt hm]
    <;> ring
  have h2 : (1/(4*(N : ℝ))-cN N^2)^2*(4/(N : ℝ)^2)*
      ((1+1/1000)*((m : ℝ)*N*(N+2)))+(1+1/1000)*covarianceMeanBound N m =
      scaleFactor N m^2*((1/4-firstRatio N/2)^2*4*(1+1/1000)*(1+2/(N : ℝ))*
        ((N : ℝ)/(m : ℝ))+(1+1/1000)*4*(1-1/(m : ℝ))*j2Core N/(N : ℝ)) := by
    rw [scaleFactor_sq hN, cN_firstRatio hN]
    unfold covarianceMeanBound
    rw [angularJ2_scale hN]
    field_simp [ne_of_gt hN, ne_of_gt hm]
    <;> ring
  change √((1+1/10^5)*((m : ℝ)*N*(m+N+1))/(4*(N : ℝ)^4)) +
    √((1/(4*(N : ℝ))-cN N^2)^2*(4/(N : ℝ)^2)*
      ((1+1/1000)*((m : ℝ)*N*(N+2)))+(1+1/1000)*covarianceMeanBound N m) = _
  rw [h1, h2, sqrt_scaleFactor, sqrt_scaleFactor]
  unfold frobCore
  ring

theorem direction_scale {N m : ℕ} (hN : 0 < (N : ℝ)) :
    directionMean N m = (m : ℝ)*firstRatio N*(1+2/(N : ℝ))*
      (1-firstRatio N)/(N : ℝ)^2 := by
  unfold directionMean
  rw [← firstRatio, cN_firstRatio hN]
  field_simp [ne_of_gt hN]
  <;> ring

theorem nu_scale {N m : ℕ} (hN : 0 < (N : ℝ)) (hm : 0 < (m : ℝ)) :
    √(e1InputVarianceBound N m rowEps)/e1EnergyLower N m (1/10^6) =
      nuCore N m/√(N : ℝ) := by
  have hi : e1InputVarianceBound N m rowEps = scaleFactor N m^2*
      ((1+1/1000+3)*(5-2/(N : ℝ))*((N : ℝ)/(m : ℝ))) := by
    rw [scaleFactor_sq hN]
    change (1+1/1000+3)*(5*(m : ℝ)/(N : ℝ)^2-2*(m : ℝ)/(N : ℝ)^3) = _
    field_simp [ne_of_gt hN, ne_of_gt hm]
    <;> ring
  rw [hi, sqrt_scaleFactor]
  unfold nuCore e1EnergyLower scaleFactor
  field_simp [ne_of_gt hN, ne_of_gt hm]
  <;> ring

theorem t_scale {N m : ℕ} (hN : 0 < (N : ℝ)) (hm : 0 < (m : ℝ)) :
    (e1FrobBound N m rowEps^2+2*(directionMean N m/(1/10^7)))/
      e1EnergyLower N m (1/10^6)^2 = tCore N m/(N : ℝ) := by
  rw [frob_scale hN hm, mul_pow, scaleFactor_sq hN, direction_scale hN]
  unfold e1EnergyLower tCore
  field_simp [ne_of_gt hN, ne_of_gt hm]
  <;> ring

theorem mean_scale {N m : ℕ} (hN : 0 < (N : ℝ)) (hm : 0 < (m : ℝ)) :
    meanMajorantValue N m (1/10^6) (1/10^7) rowEps = meanCore N m/(N : ℝ) := by
  unfold meanMajorantValue
  dsimp only
  rw [t_scale hN hm, nu_scale hN hm, Real.sqrt_div' _ hN.le]
  calc
    _ = meanCore N m/(√(N : ℝ))^2 := by unfold meanCore; ring
    _ = _ := by rw [Real.sq_sqrt hN.le]

theorem covariance_scale {N m : ℕ} (hN : 0 < (N : ℝ)) (hm : 0 < (m : ℝ)) :
    e1CovarianceRatio N m (1/10^6) rowEps = covarianceCore N m := by
  unfold e1CovarianceRatio
  rw [frob_scale hN hm]
  unfold e1EnergyLower covarianceCore scaleFactor
  field_simp [ne_of_gt hN, ne_of_gt hm]
  <;> ring

theorem conditional_scale {N m : ℕ} (hN : 0 < (N : ℝ)) (hm : 0 < (m : ℝ)) (C : ℝ) :
    ((4*(N : ℝ)^2/(m : ℝ))*(1+1/10^6)^2*√((C/(N : ℝ))/2)*
      ((1-firstRatio N)*√(1-firstRatio N)*
        sixthConstant (e1CovarianceRatio N m (1/10^6) rowEps)))/
      (712/10000-(N : ℝ)*(1+1/10^6)*(C/(N : ℝ)))^2 =
        conditionalCore N m C*((N : ℝ)*√(N : ℝ)/(m : ℝ)) := by
  rw [covariance_scale hN hm]
  rw [show (C/(N : ℝ))/2 = (C/2)/(N : ℝ) by ring,
    Real.sqrt_div' _ hN.le]
  have hs := Real.sq_sqrt hN.le
  have hsp := (Real.sqrt_pos.mpr hN).ne'
  have hc : (N : ℝ)*(1+1/10^6)*(C/(N : ℝ)) = (1+1/10^6)*C := by
    field_simp [ne_of_gt hN]
    <;> ring
  rw [hc]
  unfold conditionalCore
  have hi : (N : ℝ)^2/√(N : ℝ) = (N : ℝ)*√(N : ℝ) := by
    apply (div_eq_iff hsp).mpr
    nlinarith [hs]
  calc
    _ = (4*(1+1/10^6)^2*√(C/2)*((1-firstRatio N)*√(1-firstRatio N)*
        sixthConstant (covarianceCore N m)))/(712/10000-(1+1/10^6)*C)^2 *
        (((N : ℝ)^2/√(N : ℝ))/(m : ℝ)) := by ring
    _ = _ := by rw [hi]

end BstLean.Part271.R3
