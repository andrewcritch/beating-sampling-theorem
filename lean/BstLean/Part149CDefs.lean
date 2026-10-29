import BstLean.Part149Defs
import BstLean.Part137Smooth

/-!
# Part 149, item 5: definitions for a centre of `A` computed in one pass (mean-field centre)

Do not use `sorry`, `native_decide` or `axiom`.

The stand-in inputs are `x(γ) = sphPt (c + τ·γ)`. `A₁`, `A₂` are the two hidden matrices of `A`
(hidden width `m`).

* `a1 c τ A₁ γ = ReLU(A₁ x(γ))`: the FIRST hidden vector of `A`.
* `b1 c τ A₁ = E_γ a₁(x(γ))`: the exact mean of the first hidden layer (an ORACLE: `m` numbers,
  each a function of `(A₁c)_k`, `|row_k(A₁)|`, `|c|`, `τ`, `n`); `N2 c τ A₁ = E_γ |a₁(x(γ))|²`
  (one more oracle number).
* `sMF = √((2/m)(N2 − |b1|²))`, and **the mean-field centre**
  `bMF c τ (A₁, A₂) = ψ_s(A₂ b1)` (`psiS` of Part 137, in each coordinate): ONE product with `A₂`.
* `tauOutOf n b = √(max 0 (2/n − (2/m)|b|²))`: the constant scalar for a centre `b`.
* `eC c τ θ = |bMF − b̄|²`: the squared distance to the exact centre `bbar`.
* `V1`, `uMF`, `Qu`, `Qk`, `errD1`: statistics of the first hidden layer over the inputs.
-/

namespace BstLean.Part149

open MeasureTheory ProbabilityTheory Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part132 BstLean.Part134
open BstLean.Part136 (HidParam hidGauss hbar)
open BstLean.Part137 (psiS)

variable {n m : ℕ}

/-- The first hidden vector of `A` at the stand-in input `sphPt (c + τ·γ)`. -/
noncomputable def a1 (c : Fin n → ℝ) (τ : ℝ) (A₁ : Matrix (Fin m) (Fin n) ℝ) (γ : Fin n → ℝ) :
    Fin m → ℝ :=
  reluV (A₁.mulVec (sphPt (c + τ • γ)))

/-- The exact mean of the first hidden layer over the stand-in inputs (an oracle). -/
noncomputable def b1 (c : Fin n → ℝ) (τ : ℝ) (A₁ : Matrix (Fin m) (Fin n) ℝ) : Fin m → ℝ :=
  hbar (stdGauss (Fin n)) (a1 c τ A₁)

/-- The mean of the squared length of the first hidden layer (an oracle). -/
noncomputable def N2 (c : Fin n → ℝ) (τ : ℝ) (A₁ : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  ∫ γ, normSq (a1 c τ A₁ γ) ∂stdGauss (Fin n)

/-- The scale of the Gaussian smoothing of the mean-field centre. -/
noncomputable def sMF (c : Fin n → ℝ) (τ : ℝ) (A₁ : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  √(2 / (m : ℝ) * (N2 c τ A₁ - normSq (b1 c τ A₁)))

/-- **The mean-field centre** `ψ_s(A₂ b1)`: a centre for the last hidden layer of `A` computed
with one product with `A₂` (and the oracles `b1`, `N2`, `ψ_s`). -/
noncomputable def bMF (c : Fin n → ℝ) (τ : ℝ) (θ : HidParam n m) : Fin m → ℝ :=
  fun i => psiS (sMF c τ θ.1) ((θ.2.mulVec (b1 c τ θ.1)) i)

/-- The constant scalar of the stand-in of `A` for a centre `b`. -/
noncomputable def tauOutOf (n : ℕ) (b : Fin m → ℝ) : ℝ :=
  √(max 0 (2 / (n : ℝ) - 2 / (m : ℝ) * normSq b))

lemma tauOut_eq (c : Fin n → ℝ) (τ : ℝ) (θ : HidParam n m) :
    tauOut c τ θ = tauOutOf n (bbar c τ θ) := rfl

/-- The squared distance of the mean-field centre to the exact centre. -/
noncomputable def eC (c : Fin n → ℝ) (τ : ℝ) (θ : HidParam n m) : ℝ :=
  normSq (bMF c τ θ - bbar c τ θ)

/-- The variance of the length of the first hidden vector. -/
noncomputable def V1 (c : Fin n → ℝ) (τ : ℝ) (A₁ : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  N2 c τ A₁ - (∫ γ, nrm (a1 c τ A₁ γ) ∂stdGauss (Fin n)) ^ 2

/-- The cosine level of the first hidden layer: `|b1|²/N2`. -/
noncomputable def uMF (c : Fin n → ℝ) (τ : ℝ) (A₁ : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  normSq (b1 c τ A₁) / N2 c τ A₁

/-- The integrated squared error of the first-layer Gram kernel against `k·|a||a'|`. -/
noncomputable def Qk (k : ℝ) (c : Fin n → ℝ) (τ : ℝ) (A₁ : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  ∫ p, (dotp (a1 c τ A₁ p.1) (a1 c τ A₁ p.2) -
    k * (nrm (a1 c τ A₁ p.1) * nrm (a1 c τ A₁ p.2))) ^ 2
    ∂((stdGauss (Fin n)).prod (stdGauss (Fin n)))

/-- `Qk` at the level `uMF`. -/
noncomputable def Qu (c : Fin n → ℝ) (τ : ℝ) (A₁ : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  Qk (uMF c τ A₁) c τ A₁

/-- The integrated squared error of `|a₁|²` against `m/n`. -/
noncomputable def errD1 (c : Fin n → ℝ) (τ : ℝ) (A₁ : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  ∫ γ, (normSq (a1 c τ A₁ γ) - (m : ℝ) / n) ^ 2 ∂stdGauss (Fin n)

lemma hA_eq_a1 (c : Fin n → ℝ) (τ : ℝ) (θ : HidParam n m) (γ : Fin n → ℝ) :
    hA c τ θ γ = reluV (θ.2.mulVec (a1 c τ θ.1 γ)) := rfl

end BstLean.Part149
