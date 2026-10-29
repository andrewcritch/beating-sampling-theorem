import BstLean.Part80Defs5

/-!
# Part 80, wave 0f: sharper interfaces for the second pass (frozen)
-/

namespace BstLean.Part80

open MeasureTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part40 (SphLaw)
open BstLean.Part41 (Mono varU)
open BstLean.Part56 (UnitV lawRK tauR)
open BstLean.Part78 (nsq frobH trH qfun aU zv)

/-- **Conditional variance bound, first chaos separated** (`poincareMv2`):
`Var_W V ≤ 2 Γ ((2+η) S + ((1+1/η) √(35/2)·8√3 + 8) ‖H‖²) V̄`. -/
def VarBoundA3 : Prop :=
  ∀ (n : ℕ) (J : Type) [Fintype J] (ν : Measure (Fin n → ℝ)), SphLaw n ν →
    ∀ (f0 : ℝ) (ℓ : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ), H.IsSymm →
    ∀ (mu : (Fin n → ℝ) → Fin n → ℝ) (ψ : (Fin n → ℝ) → J → ℝ), Continuous mu → Continuous ψ →
    ∀ Γ S η : ℝ, 0 ≤ Γ → 0 < η → FeatOpA ν ψ Γ →
      (∀ x : Fin n → ℝ, ∑ i, x i ^ 2 = 1 → nsq (aA ℓ H mu x) ≤ S ∧ kA ψ x ≤ 2) →
      ∫ W, (VA ν f0 ℓ H mu ψ W - VbarA ν f0 ℓ H mu ψ) ^ 2 ∂stdGauss (J × Fin n) ≤
        2 * Γ * ((2 + η) * S +
          ((1 + 1 / η) * ((4184 / 1000) * (8 * (1733 / 1000))) + 8) * frobH H) *
            VbarA ν f0 ℓ H mu ψ

/-- **Sharp moments of `s = v·x`** for `t ∈ [0, n]` (Stein): `E s² ≤ 1/2 + 1/n` and
`E s⁴ ≤ E s²/2 + 1/(2n)`. -/
def MomSharp (n : ℕ) : Prop :=
  ∀ v : Fin n → ℝ, UnitV v → ∀ t : ℝ, 0 ≤ t → t ≤ n →
    ∫ x, (∑ i, v i * x i) ^ 2 ∂lawRK n t v ≤ 1 / 2 + 1 / (n : ℝ) ∧
    ∫ x, (∑ i, v i * x i) ^ 4 ∂lawRK n t v ≤
      1 / 2 * ∫ x, (∑ i, v i * x i) ^ 2 ∂lawRK n t v + 1 / (2 * (n : ℝ))

end BstLean.Part80
