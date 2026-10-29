import BstLean.Part271DistanceScale
import BstLean.Part271StatisticsScale

/-! Normalized first-layer formulas for the selected low-band event. -/
namespace BstLean.Part290
open Real BstLean.Part130 BstLean.Part137 BstLean.Part218
open BstLean.Part271.R3
open BstLean.Part250 (meanMajorantValue)

noncomputable def worldEps : Fin 4 → ℝ := ![1/10^5, 1/1000, 4/1000, 10]

noncomputable def frobCore (N m : ℕ) : ℝ :=
  √((1+1/10^5)*(1+(N : ℝ)/(m : ℝ)+1/(m : ℝ))/4) +
  √((1/4-firstRatio N/2)^2*4*(1+1/1000)*(1+2/(N : ℝ))*((N : ℝ)/(m : ℝ)) +
    (1+4/1000)*4*(1-1/(m : ℝ))*j2Core N/(N : ℝ))

noncomputable def nuCore (N m : ℕ) : ℝ :=
  √((1+1/1000+10)*(5-2/(N : ℝ))*((N : ℝ)/(m : ℝ)))/(1-1/10^6)

noncomputable def tCore (N m : ℕ) : ℝ :=
  (frobCore N m^2 + 2*firstRatio N*(1+2/(N : ℝ))*(1-firstRatio N)*
    ((N : ℝ)/(m : ℝ))/(1/10^7))/(1-1/10^6)^2

noncomputable def meanCore (N m : ℕ) : ℝ :=
  (20474/100000)*(√(tCore N m)+√2*nuCore N m)^2 +
    6*nuCore N m^2+(√2+2)*nuCore N m*√(tCore N m)

theorem frob_scale {N m : ℕ} (hN : 0 < (N : ℝ)) (hm : 0 < (m : ℝ)) :
    e1FrobBound N m worldEps = scaleFactor N m*frobCore N m := by
  have h1 : (1+1/10^5)*((m : ℝ)*N*(m+N+1))/(4*(N : ℝ)^4) =
      scaleFactor N m^2*((1+1/10^5)*(1+(N : ℝ)/(m : ℝ)+1/(m : ℝ))/4) := by
    rw [scaleFactor_sq hN]
    field_simp [ne_of_gt hN, ne_of_gt hm]
    <;> ring
  have h2 : (1/(4*(N : ℝ))-cN N^2)^2*(4/(N : ℝ)^2)*
      ((1+1/1000)*((m : ℝ)*N*(N+2)))+(1+4/1000)*covarianceMeanBound N m =
      scaleFactor N m^2*((1/4-firstRatio N/2)^2*4*(1+1/1000)*(1+2/(N : ℝ))*
        ((N : ℝ)/(m : ℝ))+(1+4/1000)*4*(1-1/(m : ℝ))*j2Core N/(N : ℝ)) := by
    rw [scaleFactor_sq hN, cN_firstRatio hN]
    unfold covarianceMeanBound
    rw [angularJ2_scale hN]
    field_simp [ne_of_gt hN, ne_of_gt hm]
    <;> ring
  change √((1+1/10^5)*((m : ℝ)*N*(m+N+1))/(4*(N : ℝ)^4)) +
    √((1/(4*(N : ℝ))-cN N^2)^2*(4/(N : ℝ)^2)*
      ((1+1/1000)*((m : ℝ)*N*(N+2)))+(1+4/1000)*covarianceMeanBound N m) = _
  rw [h1, h2, sqrt_scaleFactor, sqrt_scaleFactor]
  unfold frobCore
  ring

theorem nu_scale {N m : ℕ} (hN : 0 < (N : ℝ)) (hm : 0 < (m : ℝ)) :
    √(e1InputVarianceBound N m worldEps)/e1EnergyLower N m (1/10^6) =
      nuCore N m/√(N : ℝ) := by
  have hi : e1InputVarianceBound N m worldEps = scaleFactor N m^2*
      ((1+1/1000+10)*(5-2/(N : ℝ))*((N : ℝ)/(m : ℝ))) := by
    rw [scaleFactor_sq hN]
    change (1+1/1000+10)*(5*(m : ℝ)/(N : ℝ)^2-2*(m : ℝ)/(N : ℝ)^3) = _
    field_simp [ne_of_gt hN, ne_of_gt hm]
    <;> ring
  rw [hi, sqrt_scaleFactor]
  unfold nuCore e1EnergyLower scaleFactor
  field_simp [ne_of_gt hN, ne_of_gt hm]
  <;> ring

theorem t_scale {N m : ℕ} (hN : 0 < (N : ℝ)) (hm : 0 < (m : ℝ)) :
    (e1FrobBound N m worldEps^2+2*(directionMean N m/(1/10^7)))/
      e1EnergyLower N m (1/10^6)^2 = tCore N m/(N : ℝ) := by
  rw [frob_scale hN hm, mul_pow, scaleFactor_sq hN, direction_scale hN]
  unfold e1EnergyLower tCore
  field_simp [ne_of_gt hN, ne_of_gt hm]
  <;> ring

theorem mean_scale {N m : ℕ} (hN : 0 < (N : ℝ)) (hm : 0 < (m : ℝ)) :
    meanMajorantValue N m (1/10^6) (1/10^7) worldEps = meanCore N m/(N : ℝ) := by
  unfold meanMajorantValue
  dsimp only
  rw [t_scale hN hm, nu_scale hN hm, Real.sqrt_div' _ hN.le]
  calc
    _ = meanCore N m/(√(N : ℝ))^2 := by unfold meanCore; ring
    _ = _ := by rw [Real.sq_sqrt hN.le]

theorem covariance_payment_scale {N m : ℕ} (hN : 0 < (N : ℝ))
    (hm : 1 < (m : ℝ)) (hJ : 0 < j2Core N) :
    covarianceVarianceBound N m/((4/1000)*covarianceMeanBound N m)^2 =
      covariancePaymentCore N m/(16*(m : ℝ)) := by
  have he : covarianceVarianceBound N m/((4/1000)*covarianceMeanBound N m)^2 =
      (covarianceVarianceBound N m/((1/1000)*covarianceMeanBound N m)^2)/16 := by ring
  rw [he, BstLean.Part271.R3.covariance_payment_scale hN hm hJ]
  ring

theorem norm_payment_scale {N m : ℕ} (hN : 1 ≤ (N : ℝ)) (hm : 0 < (m : ℝ)) :
    normVarianceBound N m/(10*inputVarianceMean N m)^2 =
      (9/100)*normCore N/(N : ℝ) := by
  have he : normVarianceBound N m/(10*inputVarianceMean N m)^2 =
      (9/100)*(normVarianceBound N m/(3*inputVarianceMean N m)^2) := by ring
  rw [he, BstLean.Part271.R3.norm_payment_scale hN hm]
  ring

end BstLean.Part290
