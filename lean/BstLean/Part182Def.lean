import BstLean.Part153SJ
import BstLean.Part153PP

/-!
# Part 182 (file `Def`): definitions for the covariance (Schur) route

No proof is left open; no `native_decide` or `axiom` is used.

Paper source: `proofs/option-n/theorem7-04-frame-numerator.tex` (Lemma `t7:p04:dual`, the input
sets before Lemma `t7:p04:schur`, Lemma `t7:p04:ti`). Fix the retained World values `c = ĉ`,
`τ = τ₀ > 0` and the Agent matrices `A₁`, `A₂`. Put `y = c + τξ`, `x = y/|y|` (`sphPt`),
`w = τ²/|y|²`, `t = 2/m`.

* `Dq A₁ A₂ c τ v = t·τ²·E_ξ[|(𝒥(x)Π_x)ᵀ v|²/|y|²]`: the quadratic form `vᵀ D v` of the paper's
  matrix `D = E[B Bᵀ]`, `B = √(t w)·𝒥(x)Π_x`.
* `uC c = c/|c|` (`0` if `c = 0`), `perpC c ξ = ξ − (u·ξ)u`.
* `OmegaS c t0 z0`: the input set `Ω = {|u·ξ| ≤ t₀, n − 2√(n z₀) ≤ |ξ|² ≤ n + 2√(n z₀) + 2z₀}`.
* `gPlus n z0 = √(n + 2√(n z₀) + 2z₀)`.
* `GammaS c t0 z0 t1`: the pair set `Γ = {(ξ, ξ') ∈ Ω² : |ξ_⊥·ξ'_⊥| ≤ t₁ g₊}`.
* `pairBad A₁ A₂ lam x x'`: the pair bound fails: `‖(𝒥(x)Π_x)ᵀ(𝒥(x')Π_{x'})‖_op > n·λ`.
* `TI_hyp n cm cp lam δ`: **the two-input hypothesis** (Lemma `t7:p04:ti` with Lemma
  `t7:p04:MS`, in operator form): for every FIXED pair of unit inputs with
  `cm ≤ x·x' ≤ cp`, `Pr_{A₁,A₂}(pairBad) ≤ δ`.
-/

namespace BstLean.Part182

open MeasureTheory ProbabilityTheory Real Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part152
open BstLean.Part153 (nrm jacT nuA)

variable {n m : ℕ}

/-- **The quadratic form of `D`**: `Dq A₁ A₂ c τ v = t·τ²·E_ξ[|vᵀ𝒥(x)Π_x|²/|y|²]`, `t = 2/m`. -/
noncomputable def Dq (A₁ : Matrix (Fin m) (Fin n) ℝ) (A₂ : Matrix (Fin m) (Fin m) ℝ)
    (c : Fin n → ℝ) (τ : ℝ) (v : Fin m → ℝ) : ℝ :=
  2 / (m : ℝ) * τ ^ 2 * ∫ ξ, normSq (vecMul v (jacT A₁ A₂ (sphPt (c + τ • ξ)))) *
    (normSq (c + τ • ξ))⁻¹ ∂stdGauss (Fin n)

/-- The unit vector `u = c/|c|` (`0` if `c = 0`). -/
noncomputable def uC (c : Fin n → ℝ) : Fin n → ℝ := (nrm c)⁻¹ • c

/-- `ξ_⊥ = ξ − (u·ξ)u`. -/
noncomputable def perpC (c : Fin n → ℝ) (ξ : Fin n → ℝ) : Fin n → ℝ :=
  ξ - (uC c ⬝ᵥ ξ) • uC c

/-- `g₊ = √(n + 2√(n z₀) + 2z₀)`. -/
noncomputable def gPlus (n : ℕ) (z0 : ℝ) : ℝ := √((n : ℝ) + 2 * √((n : ℝ) * z0) + 2 * z0)

/-- **The input set `Ω`** with parameters `(t₀, z₀)`. -/
def OmegaS (c : Fin n → ℝ) (t0 z0 : ℝ) : Set (Fin n → ℝ) :=
  {ξ | |uC c ⬝ᵥ ξ| ≤ t0 ∧ (n : ℝ) - 2 * √((n : ℝ) * z0) ≤ normSq ξ ∧
    normSq ξ ≤ (n : ℝ) + 2 * √((n : ℝ) * z0) + 2 * z0}

/-- **The pair set `Γ`** with parameters `(t₀, z₀, t₁)`. -/
def GammaS (c : Fin n → ℝ) (t0 z0 t1 : ℝ) : Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
  {p | p.1 ∈ OmegaS c t0 z0 ∧ p.2 ∈ OmegaS c t0 z0 ∧
    |perpC c p.1 ⬝ᵥ perpC c p.2| ≤ t1 * gPlus n z0}

/-- **The pair bound fails** at the pair of inputs `(x, x')`: `‖(𝒥(x)Π_x)ᵀ 𝒥(x')Π_{x'}‖_op > n λ`. -/
def pairBad (A₁ : Matrix (Fin m) (Fin n) ℝ) (A₂ : Matrix (Fin m) (Fin m) ℝ) (lam : ℝ)
    (x x' : Fin n → ℝ) : Prop :=
  (n : ℝ) * lam < opN ((jacT A₁ A₂ x)ᵀ * jacT A₁ A₂ x')

/-- **The two-input hypothesis** (paper: Lemma `t7:p04:ti` with Lemma `t7:p04:MS`, operator
form): for every fixed pair of unit inputs with `cm ≤ x·x' ≤ cp`, the Agent weights `(A₁, A₂)`
make the pair bound `n λ` fail with probability at most `δ`. -/
def TI_hyp (n : ℕ) (cm cp lam δ : ℝ) : Prop :=
  ∀ x x' : Fin n → ℝ, normSq x = 1 → normSq x' = 1 → cm ≤ x ⬝ᵥ x' → x ⬝ᵥ x' ≤ cp →
    (nuA n).real {θ | pairBad θ.1 θ.2 lam x x'} ≤ δ

end BstLean.Part182
