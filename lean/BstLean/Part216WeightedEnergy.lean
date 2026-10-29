import BstLean.Part216PlaneEnergy
import BstLean.Part216Weighted

/-! Weighted BE18 directly from whole-row supplies on one common distribution. -/
namespace BstLean.Part216
open MeasureTheory ProbabilityTheory Real
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part202

variable {G V P : Type*} [MeasurableSpace G] [MeasurableSpace V] [MeasurableSpace P]
variable {μ : Measure V} [IsProbabilityMeasure μ]
variable {ρ : Measure P} [IsProbabilityMeasure ρ] {d m : ℕ}

/-- The covariance and trace caps give the latitude factor before node integration. -/
theorem rowScale_latitude_bound {a : V → Fin d → ℝ} {ell q lam0 σ : ℝ}
    (hq : 0 ≤ q) (hlam0 : 0 ≤ lam0) (hσ : 0 ≤ σ)
    (hell : |ell| ≤ lam0 * sqrt q)
    (htrace : covarianceTrace μ a ≤ σ ^ 2 * q) :
    rowScale μ a ell ≤ (lam0 * σ) * q := by
  have hs : sqrt (covarianceTrace μ a) ≤ σ * sqrt q := by
    have h := sqrt_le_sqrt htrace
    rwa [sqrt_mul (sq_nonneg σ), sqrt_sq hσ] at h
  calc rowScale μ a ell = |ell| * sqrt (covarianceTrace μ a) := rfl
    _ ≤ (lam0 * sqrt q) * (σ * sqrt q) :=
      mul_le_mul hell hs (sqrt_nonneg _) (mul_nonneg hlam0 (sqrt_nonneg _))
    _ = (lam0 * σ) * sqrt q ^ 2 := by ring
    _ = (lam0 * σ) * q := by rw [sq_sqrt hq]

/-- The weighted BE18 moment is derived from row-scale and latitude bounds.
Only whole rows are independent. The nodes share one Gaussian product distribution. -/
theorem weighted_whole_energy18 (ν : Measure G) (n : ℕ)
    (a : G → V → Fin d → ℝ) (ell : G → ℝ)
    (S : ∀ g, RowSplit μ ρ (a g) m (ell g))
    (ha : ∀ g, Measurable (a g))
    (hK : ∀ g, ∃ K : ℝ, ∀ v, ‖a g v‖ ≤ K)
    (q : G → ℝ) (hq : ∀ g, 0 ≤ q g)
    {R H Q : ℝ} (hR : 0 ≤ R) (hH : 0 ≤ H) (hQ : 0 ≤ Q)
    (hqQ : ∀ g, q g ≤ Q)
    (hscale : ∀ g, rowScale μ (a g) (ell g) ≤ R * q g)
    (h12 : ∫⁻ g, ENNReal.ofReal (q g ^ 12) ∂ν ≤ ENNReal.ofReal (H ^ 12)) :
    ∫⁻ g, ∫⁻ y, ENNReal.ofReal (|wholeRowSum (S g) (n ^ 2) y| ^ 18)
      ∂(Measure.pi fun _ : Fin (n ^ 2) => ρ.prod (stdGauss (Fin m))) ∂ν ≤
      ENNReal.ofReal ((R * (2 * n * (2 * ((9 : ℕ).factorial : ℝ)) ^ ((18 : ℝ)⁻¹) +
        BstLean.Part202.beta * (2 * ((18 : ℕ).factorial : ℝ)) ^ ((18 : ℝ)⁻¹))) ^ 18 * H ^ 12 * Q ^ 6) := by
  let D := 2 * n * (2 * ((9 : ℕ).factorial : ℝ)) ^ ((18 : ℝ)⁻¹) +
    BstLean.Part202.beta * (2 * ((18 : ℕ).factorial : ℝ)) ^ ((18 : ℝ)⁻¹)
  have hD : 0 ≤ D := by
    have hb := BstLean.Part202.beta_pos.le
    dsimp [D]
    positivity
  apply weighted_energy18 hq hH hQ (mul_nonneg hR hD) hqQ h12
  intro g
  obtain ⟨K, hgK⟩ := hK g
  have h := whole_sum_order18_width (S g) (ha g) hgK n
  refine h.trans (ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (mul_nonneg rowScale_nonneg hD) ?_ 18))
  calc rowScale μ (a g) (ell g) * D ≤ (R * q g) * D :=
      mul_le_mul_of_nonneg_right (hscale g) hD
    _ = (R * D) * q g := by ring

#print axioms weighted_whole_energy18
#print axioms rowScale_latitude_bound
end BstLean.Part216
