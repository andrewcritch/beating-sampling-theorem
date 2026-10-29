import BstLean.Part153Sc
import BstLean.Part131Block
import BstLean.Part134Mehler

/-!
# Part 154, definitions: the mean-field lemma (Lemma MF) in a general input space

Role: `delegations/statements/p154-spec.md`, item 3. Paper source:
`proofs/option-n/theorem5-06-centre.tex`, Lemma MF.

`(Ω, μ)` is a probability space (the input variable `ξ` of the document is `ω` here);
`f : Ω → ℝ^m` is a measurable map. `z` is a standard Gaussian vector of `ℝ^m`.

* `fbar = E f`, `GamF = E|f|²`, `GamBarF = |E f|²`, `sF2 = GamF − GamBarF` (`s²`), `sF = √sF2`.
* `betaF ω = ⟨f ω, fbar⟩/GamBarF` (`β`), `gF ω = f ω − β(ω)·fbar` (`Π_{f̄} f`),
  `sig2F ω = |gF ω|²` (`ς²`).
* `covF i j = Cov(f_i, f_j)` (the matrix `H_f`), `hsF = Σ_{i,j} covF i j²` (`‖H_f‖²_HS`).
* `XF z = E_ω relu⟨z, f ω⟩` (`𝖷`), `DF z = XF z − ψ_s(⟨z, fbar⟩)` (`𝖣`).
* `Ures a = Φ(a)Φ(−a) − ψ₁(a)ψ₁(−a)`: the variance of `relu(a + Z)` minus the square of its first
  Hermite coefficient `Φ(a)`. Lemma PR (i) holds with every constant `K ≥ sup_a Ures a`.
* `K0 = (π − 2)/(4π)`, `nuR ϱ = 4ϱ + ϱ²`, `cc0`, `cc1`, `cc2`, `QB`: the constants of Lemma MF.
* `MFHyp`: the hypotheses of Lemma MF ((M1), (M2), (M3) and the moment conditions).
* `PRvecBound K`: Lemma PR (i) (upper bound) for two linear forms of one standard Gaussian vector.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part154

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (relu reluV normSq)
open BstLean.Part137 (psiS)
open BstLean.Part153 (phiG PhiG psiG nrm)

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}

/-- `f̄ = E f`. -/
def fbar (μ : Measure Ω) (f : Ω → Fin m → ℝ) : Fin m → ℝ := fun i => ∫ ω, f ω i ∂μ

/-- `Γ_f = E|f|²`. -/
def GamF (μ : Measure Ω) (f : Ω → Fin m → ℝ) : ℝ := ∫ ω, normSq (f ω) ∂μ

/-- `Γ̄_f = |f̄|²`. -/
def GamBarF (μ : Measure Ω) (f : Ω → Fin m → ℝ) : ℝ := normSq (fbar μ f)

/-- `s² = Γ_f − Γ̄_f`. -/
def sF2 (μ : Measure Ω) (f : Ω → Fin m → ℝ) : ℝ := GamF μ f - GamBarF μ f

/-- `s = √(s²)`. -/
def sF (μ : Measure Ω) (f : Ω → Fin m → ℝ) : ℝ := √(sF2 μ f)

/-- `β(ω) = ⟨f(ω), f̄⟩/Γ̄_f`. -/
def betaF (μ : Measure Ω) (f : Ω → Fin m → ℝ) (ω : Ω) : ℝ := (f ω ⬝ᵥ fbar μ f) / GamBarF μ f

/-- `Π_{f̄} f(ω) = f(ω) − β(ω) f̄`. -/
def gF (μ : Measure Ω) (f : Ω → Fin m → ℝ) (ω : Ω) : Fin m → ℝ :=
  f ω - betaF μ f ω • fbar μ f

/-- `ς(ω)² = |Π_{f̄} f(ω)|²`. -/
def sig2F (μ : Measure Ω) (f : Ω → Fin m → ℝ) (ω : Ω) : ℝ := normSq (gF μ f ω)

/-- `H_f(i, j) = Cov(f_i, f_j)`. -/
def covF (μ : Measure Ω) (f : Ω → Fin m → ℝ) (i j : Fin m) : ℝ :=
  ∫ ω, (f ω i - fbar μ f i) * (f ω j - fbar μ f j) ∂μ

/-- `‖H_f‖²_HS = Σ_{i,j} H_f(i, j)²`. -/
def hsF (μ : Measure Ω) (f : Ω → Fin m → ℝ) : ℝ := ∑ i, ∑ j, covF μ f i j ^ 2

/-- `𝖷(z) = E_ω relu⟨z, f(ω)⟩`. -/
def XF (μ : Measure Ω) (f : Ω → Fin m → ℝ) (z : Fin m → ℝ) : ℝ := ∫ ω, relu (z ⬝ᵥ f ω) ∂μ

/-- `𝖣(z) = 𝖷(z) − ψ_s(⟨z, f̄⟩)`. -/
def DF (μ : Measure Ω) (f : Ω → Fin m → ℝ) (z : Fin m → ℝ) : ℝ :=
  XF μ f z - psiS (sF μ f) (z ⬝ᵥ fbar μ f)

/-- `Y_a(z′) = E_ω relu(β(ω)·a + ⟨z′, Π_{f̄} f(ω)⟩)`: the variable `𝖷` for a fixed value `a` of
`ā = ⟨z, f̄⟩`, as a function of the part `z′` of `z` orthogonal to `f̄`. -/
def YF (μ : Measure Ω) (f : Ω → Fin m → ℝ) (a : ℝ) (z' : Fin m → ℝ) : ℝ :=
  ∫ ω, relu (betaF μ f ω * a + z' ⬝ᵥ gF μ f ω) ∂μ

/-- `U(a) = Φ(a)Φ(−a) − ψ₁(a)ψ₁(−a) = Var relu(a + Z) − Φ(a)²`. -/
def Ures (a : ℝ) : ℝ := PhiG a * PhiG (-a) - psiG a * psiG (-a)

/-- `K₀ = (π − 2)/(4π)`. -/
def K0 : ℝ := (π - 2) / (4 * π)

/-- `ν = 4ϱ + ϱ²`. -/
def nuR (ϱ : ℝ) : ℝ := 4 * ϱ + ϱ ^ 2

/-- `𝔠₀`. -/
def cc0 (ϱ πg : ℝ) : ℝ :=
  phiG 0 * ϱ / 2 + phiG 0 * nuR ϱ / (2 * √2) + 3 / 2 * phiG 0 * √(πg * nuR ϱ)

/-- `𝔠₁`. -/
def cc1 (ϱ πg : ℝ) : ℝ := phiG 1 * √(ϱ * nuR ϱ) + 2 * √(πg * ϱ)

/-- `𝔠₂`. -/
def cc2 (ϱ : ℝ) : ℝ := phiG 0 * ϱ / √2

/-- `Q_B(ϱ, π_g)`. -/
def QB (ϱ πg : ℝ) : ℝ :=
  cc0 ϱ πg ^ 2 + cc1 ϱ πg ^ 2 + 3 * cc2 ϱ ^ 2 + 2 * √(2 / π) * cc0 ϱ πg * cc1 ϱ πg +
    2 * cc0 ϱ πg * cc2 ϱ + 4 * √(2 / π) * cc1 ϱ πg * cc2 ϱ

/-- **The hypotheses of Lemma MF.** `hf`, `h4`: `f` is measurable with `E|f|⁴ < ∞` (the document
has `E|f|² < ∞`; (M2) needs the fourth moment to have a meaning). `hbar`: `f̄ ≠ 0`. `hs`: `s² > 0`.
(M1): `wᵀH_f w ≤ ℓ²|w|²`. (M2): `Var ς² ≤ 4ℓ²·E ς²`. (M3): `Pr(ς² < s²/2) ≤ π_g`. -/
structure MFHyp (μ : Measure Ω) (f : Ω → Fin m → ℝ) (ℓ πg : ℝ) : Prop where
  hf : Measurable f
  h4 : Integrable (fun ω => normSq (f ω) ^ 2) μ
  hbar : 0 < GamBarF μ f
  hs : 0 < sF2 μ f
  hℓ : 0 < ℓ
  hπ0 : 0 ≤ πg
  hπ1 : πg ≤ 1
  M1 : ∀ w : Fin m → ℝ, ∫ ω, (w ⬝ᵥ f ω - w ⬝ᵥ fbar μ f) ^ 2 ∂μ ≤ ℓ ^ 2 * normSq w
  M2 : ∫ ω, (sig2F μ f ω - ∫ ω', sig2F μ f ω' ∂μ) ^ 2 ∂μ ≤ 4 * ℓ ^ 2 * ∫ ω, sig2F μ f ω ∂μ
  M3 : μ.real {ω | sig2F μ f ω < sF2 μ f / 2} ≤ πg

/-- **Lemma PR (i), upper bound, for two linear forms** `⟨z, g⟩`, `⟨z, g′⟩` of one standard
Gaussian vector `z` of `ℝ^m`, with the constant `K`:
`Cov(relu(a + ⟨z, g⟩), relu(a′ + ⟨z, g′⟩)) ≤ ⟨g, g′⟩Φ(a/|g|)Φ(a′/|g′|) + K⟨g, g′⟩²/(|g||g′|)`.
(Division by zero is `0` in Lean; if `g = 0` or `g′ = 0` both sides are `0`.) -/
def PRvecBound (K : ℝ) : Prop :=
  ∀ (m : ℕ) (g g' : Fin m → ℝ) (a a' : ℝ),
    ∫ z, relu (a + z ⬝ᵥ g) * relu (a' + z ⬝ᵥ g') ∂stdGauss (Fin m) -
        psiS (nrm g) a * psiS (nrm g') a' ≤
      (g ⬝ᵥ g') * PhiG (a / nrm g) * PhiG (a' / nrm g') +
        K * (g ⬝ᵥ g') ^ 2 / (nrm g * nrm g')

end

end BstLean.Part154
