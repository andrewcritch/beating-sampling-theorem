import BstLean.Part80Defs2

/-!
# Part 80, wave 0c: the weighted feature operator route (added after wave 0; frozen)

`omLL-opus-prover.md` Lemma 3.5 and §4.1: with the weighted bound `E[(c·ψ)²/κ] ≤ Λ‖c‖²` the
conditional error is `≤ Λ/(1−Λ) · V̄` for each value of the anchors.
-/

namespace BstLean.Part80

open MeasureTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part40 (SphLaw)
open BstLean.Part41 (Mono varU)
open BstLean.Part56 (UnitV lawRK tauR)
open BstLean.Part56.Orth (residualFeature)
open BstLean.Part78 (nsq frobH trH qfun aU zv)

/-- **Symmetric sphere integrals, sharper form**: as `SphSymm`, with
`max(2 E[h s² ρ²], E[h ρ⁴])` in place of `max(E[h ρ²], E[h]/2)`. -/
def SphSymm2 (n : ℕ) : Prop :=
  ∀ v : Fin n → ℝ, UnitV v → ∀ h : ℝ → ℝ, Continuous h → (∀ s, 0 ≤ h s) →
    ∀ c : Fin n → ℝ, ∑ i, c i * v i = 0 →
    ∀ S : Matrix (Fin n) (Fin n) ℝ, S.IsSymm → ∑ i, ∑ j, S i j * v i * v j = 0 →
      ∫ x, h ((∑ i, v i * x i) ^ 2) * (∑ i, c i * x i + ∑ i, ∑ j, S i j * x i * x j) ^ 2
          ∂uniformSphere n ≤
        ((∑ i, c i ^ 2) *
            ∫ x, h ((∑ i, v i * x i) ^ 2) * (1 - (∑ i, v i * x i) ^ 2) ∂uniformSphere n +
          (∑ i, ∑ j, S i j ^ 2) *
            max (2 * ∫ x, h ((∑ i, v i * x i) ^ 2) *
                ((∑ i, v i * x i) ^ 2 * (1 - (∑ i, v i * x i) ^ 2)) ∂uniformSphere n)
              (∫ x, h ((∑ i, v i * x i) ^ 2) * (1 - (∑ i, v i * x i) ^ 2) ^ 2
                ∂uniformSphere n)) / ((n : ℝ) - 1)

section abstract
variable {n : ℕ} {J : Type} [Fintype J]

/-- The weighted feature operator bound: `E_x[(c·ψ(x))²/κ(x)] ≤ Λ ‖c‖²`. -/
def WFeatOpA (ν : Measure (Fin n → ℝ)) (ψ : (Fin n → ℝ) → J → ℝ) (κw : (Fin n → ℝ) → ℝ)
    (Λ : ℝ) : Prop :=
  ∀ c : J → ℝ, ∫ x, (∑ q, c q * ψ x q) ^ 2 / κw x ∂ν ≤ Λ * ∑ q, c q ^ 2

/-- `A_k = E_x[‖a(x)‖² k(x)] + 2‖H‖² E_x k(x)²`. -/
noncomputable def AkA (ν : Measure (Fin n → ℝ)) (ℓ : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ)
    (mu : (Fin n → ℝ) → Fin n → ℝ) (ψ : (Fin n → ℝ) → J → ℝ) : ℝ :=
  ∫ x, nsq (aA ℓ H mu x) * kA ψ x ∂ν + 2 * frobH H * ∫ x, kA ψ x ^ 2 ∂ν

end abstract

/-- The regularized weight `κ_δ(x) = (3 + s²)(|1 − s²| + δ)/2`, `s = v·x`. On the sphere,
`κ_δ ≤ τ + 2δ` by `KernelLow`. -/
noncomputable def kapW (v : Fin n → ℝ) (δ : ℝ) (x : Fin n → ℝ) : ℝ :=
  (3 + (∑ i, v i * x i) ^ 2) * (|1 - (∑ i, v i * x i) ^ 2| + δ) / 2

/-- **Weighted conditional bounds.** `κw` is a positive continuous weight with `κw ≤ k + δ'` on
the sphere. -/
def CondBoundsW : Prop :=
  ∀ (n : ℕ) (J : Type) [Fintype J] (ν : Measure (Fin n → ℝ)), SphLaw n ν →
    ∀ (f0 : ℝ) (ℓ : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ), H.IsSymm →
    ∀ (mu : (Fin n → ℝ) → Fin n → ℝ) (ψ : (Fin n → ℝ) → J → ℝ), Continuous mu → Continuous ψ →
    ∀ (κw : (Fin n → ℝ) → ℝ), Continuous κw → (∀ x, 0 < κw x) →
    ∀ Λ S I δ' : ℝ, 0 ≤ Λ → 0 ≤ δ' → WFeatOpA ν ψ κw Λ →
      (∀ x : Fin n → ℝ, ∑ i, x i ^ 2 = 1 →
        nsq (aA ℓ H mu x) ≤ S ∧ I ≤ nsq (aA ℓ H mu x) ∧ kA ψ x ≤ 2 ∧ κw x ≤ kA ψ x + δ') →
      ∫ W, (BA ν f0 ℓ H mu ψ W - gA ν f0 ℓ H mu ψ) ^ 2 ∂stdGauss (J × Fin n) ≤
        Λ * (AkA ν ℓ H mu ψ + δ' * (S + 4 * frobH H)) ∧
      AkA ν ℓ H mu ψ - Λ * (AkA ν ℓ H mu ψ + δ' * (S + 4 * frobH H)) ≤ VbarA ν f0 ℓ H mu ψ ∧
      I * eA ν ψ + 2 * frobH H * eA ν ψ ^ 2 ≤ AkA ν ℓ H mu ψ ∧
      2 * frobH H * eA ν ψ ^ 2 ≤ AkA ν ℓ H mu ψ

/-- **The weighted residual feature operator bound** for `D_{t,v}`: for every `δ > 0`,
`E_D[(c·ψ(x))²/κ_δ(x)] ≤ ‖c‖²/(n−1)`. -/
def WFeatOpRK (n : ℕ) : Prop :=
  ∀ v : Fin n → ℝ, UnitV v → ∀ t : ℝ, ∀ δ : ℝ, 0 < δ →
    WFeatOpA (lawRK n t v) (fun x => residualFeature (d := 2) v x) (kapW v δ)
      (1 / ((n : ℝ) - 1))

end BstLean.Part80
