import BstLean.Part149Asm3

/-!
# Part 149, item 5: the sample output of the program with the mean-field centre

Do not use `sorry`, `native_decide` or `axiom`.

* `preB W A γ = A₃ bMF + τ_A·γ`: an input of `F` (no forward pass of `A`).
* `gSampB k W A F γ`: the mean of `F` at `k` such inputs.
* `gOutB_eq`: `gOutB` is the exact mean of `F(preB W A γ)` over a Gaussian vector `γ`.
-/

namespace BstLean.Part149

open MeasureTheory ProbabilityTheory Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part132 BstLean.Part134
open BstLean.Part141

variable {n : ℕ}

/-- An input of `F` in the program with the mean-field centre: `A₃ bMF + τ_A·γ`. -/
noncomputable def preB (W : MlpParam (2 * n) (mW n) n) (A : MlpParam n (mA n) n)
    (γ : Fin n → ℝ) : Fin n → ℝ :=
  A.2.2.mulVec (bMFW W A) + tauOutOf n (bMFW W A) • γ

/-- **The sample output**: the mean of `F` at the `k` inputs `preB W A (γ i)`. -/
noncomputable def gSampB {mF : ℕ} (k : ℕ) (W : MlpParam (2 * n) (mW n) n)
    (A : MlpParam n (mA n) n) (F : MlpParam n mF 1) (γ : Fin k → Fin n → ℝ) : ℝ :=
  (k : ℝ)⁻¹ * ∑ i, evF F (preB W A (γ i))

lemma gOutB_eq {mF : ℕ} (W : MlpParam (2 * n) (mW n) n) (A : MlpParam n (mA n) n)
    (F : MlpParam n mF 1) :
    gOutB W A F = ∫ γ, evF F (preB W A γ) ∂stdGauss (Fin n) := rfl

end BstLean.Part149
