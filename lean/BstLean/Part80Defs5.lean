import BstLean.Part80Defs4

/-!
# Part 80, wave 0e: the Gaussian model on the full coefficient array, and its probability bounds
(frozen)

`Z : CoefIdxD n 2 → ℝ` is the standard Gaussian coefficient array (the scaling `σ` is in `f`).
* `BGm ν f0 ℓ H Z = E_{x∼ν} f(Z φ(x))`, `VGm = Var_{x∼ν} f(Z φ(x))`.
* `gLm ν f0 ℓ H v Z = E_{x∼ν}[f(μ_Z(x)) + tr H · τ(x)]` (the line program's value, heat form).
* `VbG n t v f0 ℓ H Z = V̄` given the anchors of `Z` (`VbarA` of the conditional model).
* `cmb v Z Z' = Π Z + (Z' − Π Z')`: the anchors of `Z`, the residual of `Z'`.
-/

namespace BstLean.Part80

open MeasureTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part36 (CoefIdxD mapMD)
open BstLean.Part41 (Mono varU)
open BstLean.Part56 (UnitV lawRK kJ tauR ancRK mux projA)
open BstLean.Part78 (nsq frobH trH qfun aU zv)

variable {n : ℕ}

/-- `B(Z) = E_{x∼ν} f(Z φ(x))`. -/
noncomputable def BGm (ν : Measure (Fin n → ℝ)) (f0 : ℝ) (ℓ : Fin n → ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) (Z : CoefIdxD n 2 → ℝ) : ℝ :=
  ∫ x, qfun f0 ℓ H (mapMD Z x) ∂ν

/-- `V(Z) = Var_{x∼ν} f(Z φ(x))`. -/
noncomputable def VGm (ν : Measure (Fin n → ℝ)) (f0 : ℝ) (ℓ : Fin n → ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) (Z : CoefIdxD n 2 → ℝ) : ℝ :=
  varU ν (fun x => qfun f0 ℓ H (mapMD Z x))

/-- `Φ_Z(x) = f(μ_Z(x)) + tr H · τ(x)`. -/
noncomputable def PhiL (f0 : ℝ) (ℓ : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ)
    (Z : CoefIdxD n 2 → ℝ) (x : Fin n → ℝ) : ℝ :=
  qfun f0 ℓ H (mux Z v x) + trH H * tauR 2 v x

/-- `g_ν(Z) = E_{x∼ν} Φ_Z(x)`. -/
noncomputable def gLm (ν : Measure (Fin n → ℝ)) (f0 : ℝ) (ℓ : Fin n → ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) (Z : CoefIdxD n 2 → ℝ) : ℝ :=
  ∫ x, PhiL f0 ℓ H v Z x ∂ν

/-- `V̄(Z)`: the mean of `V` given the anchors of `Z`. -/
noncomputable def VbG (n : ℕ) (t : ℝ) (v : Fin n → ℝ) (f0 : ℝ) (ℓ : Fin n → ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) (Z : CoefIdxD n 2 → ℝ) : ℝ :=
  VbarA (lawRK n t v) f0 ℓ H (muR Z v) (psiR v)

/-- `Π Z + (Z' − Π Z')`. -/
noncomputable def cmb (v : Fin n → ℝ) (Z Z' : CoefIdxD n 2 → ℝ) : CoefIdxD n 2 → ℝ :=
  projA v Z + (Z' - projA v Z')

/-- **The conditional facts in the coordinates of the Gaussian split** `Z ↦ cmb v Z Z'`. -/
def GaussCond (n : ℕ) (CV0 CV1 φV : ℝ) : Prop :=
  ∀ v : Fin n → ℝ, UnitV v → ∀ t : ℝ, 0 ≤ t → t ≤ n →
    ∀ (f0 : ℝ) (ℓ : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ), H.IsSymm → 0 < frobH H →
      Measurable (VbG n t v f0 ℓ H) ∧
      ∀ Z : CoefIdxD n 2 → ℝ,
        φV * frobH H ≤ VbG n t v f0 ℓ H Z ∧
        varU (lawRK n t v) (PhiL f0 ℓ H v Z) ≤ VbG n t v f0 ℓ H Z ∧
        (∀ Z', VbG n t v f0 ℓ H (cmb v Z Z') = VbG n t v f0 ℓ H Z) ∧
        (∀ (ν : Measure (Fin n → ℝ)) Z', gLm ν f0 ℓ H v (cmb v Z Z') = gLm ν f0 ℓ H v Z) ∧
        Integrable (fun Z' => VGm (lawRK n t v) f0 ℓ H (cmb v Z Z')) (stdGauss (CoefIdxD n 2)) ∧
        ∫ Z', VGm (lawRK n t v) f0 ℓ H (cmb v Z Z') ∂stdGauss (CoefIdxD n 2) =
          VbG n t v f0 ℓ H Z ∧
        Integrable (fun Z' => (BGm (lawRK n t v) f0 ℓ H (cmb v Z Z') -
            gLm (lawRK n t v) f0 ℓ H v Z) ^ 2) (stdGauss (CoefIdxD n 2)) ∧
        ∫ Z', (BGm (lawRK n t v) f0 ℓ H (cmb v Z Z') - gLm (lawRK n t v) f0 ℓ H v Z) ^ 2
            ∂stdGauss (CoefIdxD n 2) ≤ VbG n t v f0 ℓ H Z / ((n : ℝ) - 2) ∧
        Integrable (fun Z' => (VGm (lawRK n t v) f0 ℓ H (cmb v Z Z') - VbG n t v f0 ℓ H Z) ^ 2)
          (stdGauss (CoefIdxD n 2)) ∧
        ∫ Z', (VGm (lawRK n t v) f0 ℓ H (cmb v Z Z') - VbG n t v f0 ℓ H Z) ^ 2
            ∂stdGauss (CoefIdxD n 2) ≤
          (CV0 + CV1 * (Yanc H v Z / frobH H)) / ((n : ℝ) - 1) * VbG n t v f0 ℓ H Z ^ 2

/-- **The probability bounds of the Gaussian model** (`omLL-opus-prover.md` §6, events E2–E5). -/
def ProbRK (n : ℕ) (CV : ℝ) : Prop :=
  ∀ v : Fin n → ℝ, UnitV v → ∀ t : ℝ, 0 ≤ t → t ≤ n →
    ∀ (f0 : ℝ) (ℓ : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ), H.IsSymm → 0 < frobH H →
      (∀ ε₁ : ℝ, 0 < ε₁ →
        stdGauss (CoefIdxD n 2) {Z | ε₁ ^ 2 * VbG n t v f0 ℓ H Z <
            (BGm (lawRK n t v) f0 ℓ H Z - gLm (lawRK n t v) f0 ℓ H v Z) ^ 2} ≤
          ENNReal.ofReal (1 / (((n : ℝ) - 2) * ε₁ ^ 2))) ∧
      (∀ κ : ℝ, 0 ≤ κ → κ < 1 →
        stdGauss (CoefIdxD n 2) {Z | VGm (lawRK n t v) f0 ℓ H Z < κ * VbG n t v f0 ℓ H Z} ≤
          ENNReal.ofReal (CV / (((n : ℝ) - 1) * (1 - κ) ^ 2))) ∧
      (∀ T : ℝ, 0 < T →
        stdGauss (CoefIdxD n 2) {Z | T <
            (BGm (lawRK n t v) 0 0 H Z - gLm (lawRK n t v) 0 0 H v Z) ^ 2} ≤
          ENNReal.ofReal (((n : ℝ) / 16 + 18) * frobH H / (((n : ℝ) - 2) * T))) ∧
      (∀ T : ℝ, 0 < T →
        stdGauss (CoefIdxD n 2) {Z | T < VbG n t v 0 0 H Z} ≤
          ENNReal.ofReal (((n : ℝ) / 16 + 18) * frobH H / T)) ∧
      (∀ T : ℝ, 0 < T →
        stdGauss (CoefIdxD n 2) {Z | T < VGm (lawRK n t v) 0 0 H Z} ≤
          ENNReal.ofReal (((n : ℝ) / 16 + 18) * frobH H / T))

end BstLean.Part80
