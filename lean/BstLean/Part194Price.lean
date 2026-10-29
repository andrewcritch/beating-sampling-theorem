import BstLean.Part152LM

/-! Scalar and Gaussian integral reductions for the exponential Price remainder. -/
namespace BstLean.Part194
open MeasureTheory ProbabilityTheory Real Set

/-- The quadratic form in the bivariate Gaussian density dominates the radial form. -/
theorem price_quadratic {u v w : ℝ} (hu : |u| < 1) :
    (v ^ 2 - 2 * u * v * w + w ^ 2) / (2 * (1 - u ^ 2)) ≥
      (v ^ 2 + w ^ 2) / 4 := by
  have hu0 : 0 < 1 - u ^ 2 := by
    have h := abs_lt.mp hu
    nlinarith
  apply (le_div_iff₀ (by positivity : 0 < 2 * (1 - u ^ 2))).mpr
  have hs := sq_nonneg (v - u * w)
  have ht := sq_nonneg (w - u * v)
  nlinarith

noncomputable def priceDensity (u v w : ℝ) : ℝ :=
  exp (-(v ^ 2 - 2 * u * v * w + w ^ 2) / (2 * (1 - u ^ 2))) /
    (2 * π * √(1 - u ^ 2))

/-- Density domination on the open correlation interval. -/
theorem price_density_bound {u v w : ℝ} (hu : |u| < 1) :
    priceDensity u v w ≤ exp (-(v ^ 2 + w ^ 2) / 4) /
      (2 * π * √(1 - u ^ 2)) := by
  unfold priceDensity
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply exp_le_exp.mpr
  simpa only [neg_div] using neg_le_neg (price_quadratic hu)

/-- Exact integration over the scalar regression coordinate. -/
theorem gaussian_exp_pair {T T' : ℝ} (hT : 0 ≤ T) (hT' : 0 ≤ T') :
    Integrable (fun z : ℝ => exp (-z ^ 2 * (T + T') / 4)) (gaussianReal 0 1) ∧
    (∫ z : ℝ, exp (-z ^ 2 * (T + T') / 4) ∂gaussianReal 0 1) =
      1 / √(1 + (T + T') / 2) := by
  have ht : -(T + T') / 4 < (1 : ℝ) / 2 := by linarith
  have h := BstLean.Part152.gauss_mgf_sq ht
  have hf : (fun z : ℝ => exp (-z ^ 2 * (T + T') / 4)) =
      fun z => exp ((-(T + T') / 4) * z ^ 2) := by
    funext z; congr 1; ring
  have he : 1 - 2 * (-(T + T') / 4) = 1 + (T + T') / 2 := by ring
  simpa only [hf, he, one_div] using h

/-- The arithmetic mean supplies the product fourth-root denominator. -/
theorem regression_denominator {T T' : ℝ} (hT : 0 ≤ T) (hT' : 0 ≤ T') :
    1 / √(1 + (T + T') / 2) ≤ 1 / √(√((1 + T) * (1 + T'))) := by
  have hp : 0 < (1 + T) * (1 + T') := by positivity
  have hs : √((1 + T) * (1 + T')) ^ 2 = (1 + T) * (1 + T') := sq_sqrt hp.le
  have hA : √((1 + T) * (1 + T')) ≤ 1 + (T + T') / 2 := by
    have h0 := sqrt_nonneg ((1 + T) * (1 + T'))
    have h1 : 0 ≤ 1 + (T + T') / 2 := by positivity
    have h2 : (1 + T) * (1 + T') ≤ (1 + (T + T') / 2) ^ 2 := by
      nlinarith [sq_nonneg (T - T')]
    nlinarith
  exact one_div_le_one_div_of_le (sqrt_pos.mpr (sqrt_pos.mpr hp)) (sqrt_le_sqrt hA)

/-- Integrate an explicitly supplied exponential remainder envelope.
The envelope is a hypothesis; this theorem does not supply the Price identity. -/
theorem integrated_price_of_envelope {R : ℝ → ℝ} {K c σ σ' T T' : ℝ}
    (hK : 0 ≤ K) (hσ : 0 < σ) (hσ' : 0 < σ') (hT : 0 ≤ T) (hT' : 0 ≤ T')
    (hRm : AEStronglyMeasurable R (gaussianReal 0 1)) (hR0 : ∀ z, 0 ≤ R z)
    (hR : ∀ z, R z ≤ K * c ^ 2 / (σ * σ') * exp (-z ^ 2 * (T + T') / 4)) :
    Integrable R (gaussianReal 0 1) ∧
    (∫ z, R z ∂gaussianReal 0 1) ≤
      K * c ^ 2 / (σ * σ') / √(√((1 + T) * (1 + T'))) := by
  have hC : 0 ≤ K * c ^ 2 / (σ * σ') := by positivity
  have hi := (gaussian_exp_pair hT hT').1.const_mul (K * c ^ 2 / (σ * σ'))
  have hRi : Integrable R (gaussianReal 0 1) := hi.mono' hRm (ae_of_all _ fun z => by
    rw [Real.norm_of_nonneg (hR0 z)]; exact hR z)
  refine ⟨hRi, ?_⟩
  calc (∫ z, R z ∂gaussianReal 0 1)
      ≤ ∫ z, K * c ^ 2 / (σ * σ') * exp (-z ^ 2 * (T + T') / 4)
          ∂gaussianReal 0 1 := integral_mono hRi hi hR
    _ = K * c ^ 2 / (σ * σ') * (1 / √(1 + (T + T') / 2)) := by
      rw [integral_const_mul, (gaussian_exp_pair hT hT').2]
    _ ≤ K * c ^ 2 / (σ * σ') * (1 / √(√((1 + T) * (1 + T')))) :=
      mul_le_mul_of_nonneg_left (regression_denominator hT hT') hC
    _ = _ := by ring

/-- Convert the regression fourth root to the norm denominator. -/
theorem scaled_fourth_denominator {D E P : ℝ} (hD : 0 < D) (hE : 0 ≤ E)
    (hP : 0 ≤ P) (hEq : D ^ 2 * P = E ^ 2) :
    D * √(√P) = √(D * E) := by
  have hFirst : D * √P = E := by
    have hsq : (D * √P) ^ 2 = E ^ 2 := by rw [mul_pow, sq_sqrt hP, hEq]
    exact (sq_eq_sq₀ (mul_nonneg hD.le (sqrt_nonneg _)) hE).mp hsq
  have hsq : (D * √(√P)) ^ 2 = D * E := by
    rw [mul_pow, sq_sqrt (sqrt_nonneg _), sq, mul_assoc, hFirst]
  rw [← hsq, sqrt_sq (mul_nonneg hD.le (sqrt_nonneg _))]

/-- Exact scalar norm relations give the paper's integrated denominator.
The pointwise exponential remainder envelope remains an explicit hypothesis. -/
theorem integrated_price_norm {R : ℝ → ℝ} {K c σ σ' T T' N N' : ℝ}
    (hK : 0 ≤ K) (hσ : 0 < σ) (hσ' : 0 < σ') (hT : 0 ≤ T) (hT' : 0 ≤ T')
    (hN : 0 ≤ N) (hN' : 0 ≤ N')
    (hNorm : N ^ 2 = σ ^ 2 * (1 + T)) (hNorm' : N' ^ 2 = σ' ^ 2 * (1 + T'))
    (hRm : AEStronglyMeasurable R (gaussianReal 0 1)) (hR0 : ∀ z, 0 ≤ R z)
    (hR : ∀ z, R z ≤ K * c ^ 2 / (σ * σ') * exp (-z ^ 2 * (T + T') / 4)) :
    Integrable R (gaussianReal 0 1) ∧
      (∫ z, R z ∂gaussianReal 0 1) ≤ K * c ^ 2 / √(σ * σ' * N * N') := by
  have hEq : (σ * σ') ^ 2 * ((1 + T) * (1 + T')) = (N * N') ^ 2 := by
    rw [mul_pow, mul_pow, hNorm, hNorm']; ring
  have hDen := scaled_fourth_denominator (mul_pos hσ hσ') (mul_nonneg hN hN')
    (by positivity : 0 ≤ (1 + T) * (1 + T')) hEq
  obtain ⟨hi, hb⟩ := integrated_price_of_envelope hK hσ hσ' hT hT' hRm hR0 hR
  refine ⟨hi, hb.trans (le_of_eq ?_)⟩
  rw [div_div, hDen]
  congr 2
  ring

/-- Lower cutoffs for both projected and full norms supply the regular-pair coefficient. -/
theorem regular_remainder {K c σ σ' N N' a b : ℝ} (hK : 0 ≤ K)
    (ha : 0 < a) (hb : 0 < b) (hσ : a ≤ σ) (hσ' : a ≤ σ')
    (hN : b ≤ N) (hN' : b ≤ N') :
    K * c ^ 2 / √(σ * σ' * N * N') ≤ K / (a * b) * c ^ 2 := by
  have hσσ : a * a ≤ σ * σ' := mul_le_mul hσ hσ' ha.le (ha.le.trans hσ)
  have hNN : b * b ≤ N * N' := mul_le_mul hN hN' hb.le (hb.le.trans hN)
  have hProd : (a * b) ^ 2 ≤ σ * σ' * N * N' := by
    have h := mul_le_mul hσσ hNN (mul_nonneg hb.le hb.le)
      (mul_nonneg (ha.le.trans hσ) (ha.le.trans hσ'))
    nlinarith only [h]
  have hDen : a * b ≤ √(σ * σ' * N * N') := by
    have h := sqrt_le_sqrt hProd
    rwa [sqrt_sq (mul_nonneg ha.le hb.le)] at h
  have hInv := one_div_le_one_div_of_le (mul_pos ha hb) hDen
  calc K * c ^ 2 / √(σ * σ' * N * N')
      = (K * c ^ 2) * (1 / √(σ * σ' * N * N')) := by ring
    _ ≤ (K * c ^ 2) * (1 / (a * b)) :=
      mul_le_mul_of_nonneg_left hInv (mul_nonneg hK (sq_nonneg _))
    _ = _ := by ring

/-- The unchanged linear MF coefficient admits the paper's rational enclosure. -/
theorem linear_coefficient_bound : 4 * (√2 - 1) ^ 2 ≤ (6863 : ℝ) / 10000 := by
  have hLower : (1414213 : ℝ) / 1000000 ≤ √2 := by
    have h := sqrt_le_sqrt
      (show ((1414213 : ℝ) / 1000000) ^ 2 ≤ 2 by norm_num)
    rwa [sqrt_sq (by norm_num : (0 : ℝ) ≤ 1414213 / 1000000)] at h
  have hs : (√2 : ℝ) ^ 2 = 2 := sq_sqrt (by norm_num)
  nlinarith

#print axioms linear_coefficient_bound
#print axioms regular_remainder
#print axioms scaled_fourth_denominator
#print axioms integrated_price_norm
#print axioms price_quadratic
#print axioms price_density_bound
#print axioms gaussian_exp_pair
#print axioms regression_denominator
#print axioms integrated_price_of_envelope
end BstLean.Part194
