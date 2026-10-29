import BstLean.Part80Defs

/-!
# Part 80, wave 0b: three sharper interface statements (added after wave 0; frozen)
-/

namespace BstLean.Part80

open MeasureTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part40 (SphLaw)
open BstLean.Part41 (Mono varU)
open BstLean.Part56 (UnitV lawRK tauR)
open BstLean.Part78 (nsq frobH trH qfun aU zv)

/-- **Conditional variance bound, sharper form**: the `‖a(x)‖²` part of `‖T‖²` is constant in `W`,
so the Hölder step is needed for the `|HR|²` part only:
`Var_W V ≤ 4 Γ ((1+η) S + (1+1/η) √(35/2)·8√3 ‖H‖²) V̄`. -/
def VarBoundA2 : Prop :=
  ∀ (n : ℕ) (J : Type) [Fintype J] (ν : Measure (Fin n → ℝ)), SphLaw n ν →
    ∀ (f0 : ℝ) (ℓ : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ), H.IsSymm →
    ∀ (mu : (Fin n → ℝ) → Fin n → ℝ) (ψ : (Fin n → ℝ) → J → ℝ), Continuous mu → Continuous ψ →
    ∀ Γ S η : ℝ, 0 ≤ Γ → 0 < η → FeatOpA ν ψ Γ →
      (∀ x : Fin n → ℝ, ∑ i, x i ^ 2 = 1 → nsq (aA ℓ H mu x) ≤ S ∧ kA ψ x ≤ 2) →
      ∫ W, (VA ν f0 ℓ H mu ψ W - VbarA ν f0 ℓ H mu ψ) ^ 2 ∂stdGauss (J × Fin n) ≤
        4 * Γ * ((1 + η) * S +
          (1 + 1 / η) * ((4184 / 1000) * (8 * (1733 / 1000))) * frobH H) * VbarA ν f0 ℓ H mu ψ

/-- **Lower bound for the residual kernel** (`omLL-opus-prover.md` Lemma 3.3):
`τ(x) ≥ (1 − s²)(3 + s²)/2`, `s = v·x`, on the unit sphere. -/
def KernelLow (n : ℕ) : Prop :=
  ∀ v : Fin n → ℝ, UnitV v → ∀ x : Fin n → ℝ, ∑ i, x i ^ 2 = 1 →
    (1 - (∑ i, v i * x i) ^ 2) * (3 + (∑ i, v i * x i) ^ 2) / 2 ≤ tauR 2 v x

/-- **Fourth moment of `s = v·x`** for `t ∈ [0, n]`: `E_D s⁴ ≤ (53/100) E_D s² + 1/n`.
(The exact Stein identity gives `E s⁴ ≤ E s²/2 + 1/(2n)`.) -/
def PLow4RK (n : ℕ) : Prop :=
  ∀ v : Fin n → ℝ, UnitV v → ∀ t : ℝ, 0 ≤ t → t ≤ n →
    ∫ x, (∑ i, v i * x i) ^ 4 ∂lawRK n t v ≤
      53 / 100 * ∫ x, (∑ i, v i * x i) ^ 2 ∂lawRK n t v + 1 / (n : ℝ)

end BstLean.Part80
