import BstLean.Part59Defs

/-!
# Part 71, wave 0: definitions — Theorem 4 under a chi-square bound, and quadratic tilts

Source: `delegations/answers/omQT-opus-prover.md` (§A.1, §A.3, §B.1) and
`delegations/answers/omQT-cx-disprover.md` (§2, §4). Specification: `delegations/statements/p71-spec.md`.

* `ChiLaw n μ K`: `μ` is a probability distribution with a density `ρ` relative to the uniform
  distribution `σ` on the sphere, and `E_σ ρ² ≤ 1 + K` (that is, `χ²(μ‖σ) ≤ K`).
* `SphereFourth71 d C`: Lemma SH in feature form, `E_σ (a·φ)⁴ ≤ C (E_σ (a·φ)²)²`.
* `qf A x = xᵀAx`, `ctrM A = A − (tr A / n) I`, `frobM A = Σ A_ij²`, `quadTilt n A ∝ exp(xᵀAx) σ`.

Do not use `native_decide` or `axiom`.
-/

namespace BstLean.Part71

open MeasureTheory
open BstLean.Part29 (uniformSphere)
open BstLean.Part41 (Mono phiM)

variable {n : ℕ}

/-- `μ` is a probability distribution with density `ρ` relative to the uniform distribution on the
sphere, and `∫ ρ² dσ ≤ 1 + K` (chi-square divergence at most `K`). -/
def ChiLaw (n : ℕ) (μ : Measure (Fin n → ℝ)) (K : ℝ) : Prop :=
  IsProbabilityMeasure μ ∧
  ∃ ρ : (Fin n → ℝ) → ℝ, Measurable ρ ∧ (∀ x, 0 ≤ ρ x) ∧
    μ = (uniformSphere n).withDensity (fun x => ENNReal.ofReal (ρ x)) ∧
    Integrable (fun x => ρ x ^ 2) (uniformSphere n) ∧
    ∫ x, ρ x ^ 2 ∂uniformSphere n ≤ 1 + K

/-- **Lemma SH** (feature form): for every coefficient vector `a`,
`E_σ (Σ_p a_p φ_p)⁴ ≤ C · (E_σ (Σ_p a_p φ_p)²)²`. -/
def SphereFourth71 (d : ℕ) (C : ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ a : Mono n d → ℝ,
    ∫ x, (∑ p, a p * phiM x p) ^ 4 ∂uniformSphere n ≤
      C * (∫ x, (∑ p, a p * phiM x p) ^ 2 ∂uniformSphere n) ^ 2

/-! ## Quadratic tilts -/

/-- The quadratic form `xᵀAx`. -/
def qf (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : ℝ := ∑ i, ∑ j, A i j * x i * x j

/-- The traceless part `A₀ = A − (tr A / n) I`. -/
noncomputable def ctrM (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  A - (A.trace / n) • (1 : Matrix (Fin n) (Fin n) ℝ)

/-- The squared Frobenius norm `‖A‖_F² = Σ_{ij} A_ij²`. -/
def frobM (A : Matrix (Fin n) (Fin n) ℝ) : ℝ := ∑ i, ∑ j, A i j ^ 2

/-- The normalizing constant `Z(A) = E_σ exp(xᵀAx)`. -/
noncomputable def tiltZ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∫ x, Real.exp (qf A x) ∂uniformSphere n

/-- The quadratic tilt `D_A`: density `exp(xᵀAx)/Z(A)` relative to the uniform distribution. -/
noncomputable def quadTilt (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) : Measure (Fin n → ℝ) :=
  (uniformSphere n).withDensity (fun x => ENNReal.ofReal (Real.exp (qf A x) / tiltZ n A))

end BstLean.Part71
