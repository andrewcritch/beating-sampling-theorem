import BstLean.Part151J
import BstLean.Part153Op

/-!
# Part 153, item 4: definitions for the tangent Jacobian and the covariance quantities `Ξ`, `Ξ₄`

Paper source: `proofs/option-n/theorem5-01-statement-notation.tex` ("Variables of the proof") and
`theorem5-05-covariance.tex`. `jac A₁ A₂ x = D₂·A₂·D₁·A₁` (strict masks at `x`) is the Jacobian
matrix of Part 151 (file `Part151J`).

* `projT x = I − x xᵀ`: for a unit vector `x`, the orthogonal projection `Π_x` on `x^⊥`.
* `jacT A₁ A₂ x = 𝒥(x)·Π_x`: **the tangent Jacobian**.
* `XiS A₁ A₂ c τ = t·τ²·E_ξ[‖𝒥(x)Π_x‖_op²/|y|²]` (`t = 2/m`): the quantity `Ξ`.
* `Xi4 A₁ A₂ c τ = t·τ²·(E_ξ[‖𝒥(x)Π_x‖_op⁴/|y|⁴])^{1/2}`: the quantity `Ξ₄`.
Here `y = c + τξ`, `x = sphPt y = y/|y|`, `‖·‖_op = opN` (Part 152), and `1/|y|²` is
`(normSq y)⁻¹` (it is `0` at `y = 0`, a null event).
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part153

open MeasureTheory ProbabilityTheory Real Set Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part152
open BstLean.Part151 (jac)

variable {n m m₂ : ℕ}

/-- `Π_x = I − x xᵀ`. -/
def projT (x : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ := 1 - Matrix.vecMulVec x x

/-- **The tangent Jacobian** `𝒥(x)·Π_x`. -/
noncomputable def jacT (A₁ : Matrix (Fin m) (Fin n) ℝ) (A₂ : Matrix (Fin m₂) (Fin m) ℝ)
    (x : Fin n → ℝ) : Matrix (Fin m₂) (Fin n) ℝ :=
  jac A₁ A₂ x * projT x

/-- `Ξ = t·τ²·E_ξ[‖𝒥(x)Π_x‖_op²/|y|²]`, `t = 2/m`. -/
noncomputable def XiS (A₁ : Matrix (Fin m) (Fin n) ℝ) (A₂ : Matrix (Fin m) (Fin m) ℝ)
    (c : Fin n → ℝ) (τ : ℝ) : ℝ :=
  2 / (m : ℝ) * τ ^ 2 * ∫ ξ, opN (jacT A₁ A₂ (sphPt (c + τ • ξ))) ^ 2 *
    (normSq (c + τ • ξ))⁻¹ ∂stdGauss (Fin n)

/-- `Ξ₄ = t·τ²·(E_ξ[‖𝒥(x)Π_x‖_op⁴/|y|⁴])^{1/2}`, `t = 2/m`. -/
noncomputable def Xi4 (A₁ : Matrix (Fin m) (Fin n) ℝ) (A₂ : Matrix (Fin m) (Fin m) ℝ)
    (c : Fin n → ℝ) (τ : ℝ) : ℝ :=
  2 / (m : ℝ) * τ ^ 2 * √(∫ ξ, opN (jacT A₁ A₂ (sphPt (c + τ • ξ))) ^ 4 *
    (normSq (c + τ • ξ))⁻¹ ^ 2 ∂stdGauss (Fin n))

end BstLean.Part153
