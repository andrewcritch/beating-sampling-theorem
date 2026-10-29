import BstLean.Part80Defs3

/-!
# Part 80, wave 0d: the conditional model for `D_{t,v}`, given the anchors (frozen)

For a fixed coefficient array `Z` (it enters through its three anchors `u_j = ancRK Z v j` only),
the abstract model of `Part80Defs` is used with `ν = lawRK n t v`, `J = Mono n 2`,
`ψ = psiR v` (the residual features) and `mu = muR Z v` (the conditional mean field).
-/

namespace BstLean.Part80

open MeasureTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part36 (CoefIdxD)
open BstLean.Part41 (Mono varU)
open BstLean.Part56 (UnitV lawRK kJ ancRK mux)
open BstLean.Part56.Orth (residualFeature)
open BstLean.Part78 (nsq frobH trH qfun aU zv)

variable {n : ℕ}

/-- The residual features of the line program at `d = 2`. -/
noncomputable def psiR (v : Fin n → ℝ) : (Fin n → ℝ) → Mono n 2 → ℝ :=
  fun x => residualFeature (d := 2) v x

/-- The conditional mean field given the anchors of `Z`. -/
noncomputable def muR (Z : CoefIdxD n 2 → ℝ) (v : Fin n → ℝ) : (Fin n → ℝ) → Fin n → ℝ :=
  fun x => mux Z v x

/-- `H u`. -/
def Hmul (H : Matrix (Fin n) (Fin n) ℝ) (u : Fin n → ℝ) : Fin n → ℝ := fun i => ∑ j, H i j * u j

/-- `Y = 8(‖H u₁‖² + ‖H u₂‖²/‖φ₂(v)‖²)`, a bound for `‖2H(s u₁ + β₂ u₂)‖²`. -/
noncomputable def Yanc (H : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) (Z : CoefIdxD n 2 → ℝ) : ℝ :=
  8 * (nsq (Hmul H (ancRK Z v 1)) + nsq (Hmul H (ancRK Z v 2)) / kJ 2 2 v v)

/-- **The conditional bounds for `D_{t,v}`, `t ∈ [0, n]`, for each value of the anchors.**
With `m = V̄ = VbarA`: the floor `φV ‖H‖² ≤ m`; the error `E_W (B − g)² ≤ m/(n−2)`;
`Var_x Φ ≤ m`; and `Var_W V ≤ (CV0 + CV1 · Y/‖H‖²)/(n−1) · m²`. -/
def CondRK (n : ℕ) (CV0 CV1 φV : ℝ) : Prop :=
  ∀ v : Fin n → ℝ, UnitV v → ∀ t : ℝ, 0 ≤ t → t ≤ n →
    ∀ (f0 : ℝ) (ℓ : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ), H.IsSymm → 0 < frobH H →
    ∀ Z : CoefIdxD n 2 → ℝ,
      φV * frobH H ≤ VbarA (lawRK n t v) f0 ℓ H (muR Z v) (psiR v) ∧
      ∫ W, (BA (lawRK n t v) f0 ℓ H (muR Z v) (psiR v) W -
          gA (lawRK n t v) f0 ℓ H (muR Z v) (psiR v)) ^ 2 ∂stdGauss (Mono n 2 × Fin n) ≤
        VbarA (lawRK n t v) f0 ℓ H (muR Z v) (psiR v) / ((n : ℝ) - 2) ∧
      varU (lawRK n t v) (PhiA f0 ℓ H (muR Z v) (psiR v)) ≤
        VbarA (lawRK n t v) f0 ℓ H (muR Z v) (psiR v) ∧
      ∫ W, (VA (lawRK n t v) f0 ℓ H (muR Z v) (psiR v) W -
          VbarA (lawRK n t v) f0 ℓ H (muR Z v) (psiR v)) ^ 2 ∂stdGauss (Mono n 2 × Fin n) ≤
        (CV0 + CV1 * (Yanc H v Z / frobH H)) / ((n : ℝ) - 1) *
          VbarA (lawRK n t v) f0 ℓ H (muR Z v) (psiR v) ^ 2

end BstLean.Part80
