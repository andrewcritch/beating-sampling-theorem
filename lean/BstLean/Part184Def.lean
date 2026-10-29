import BstLean.Part183Def
import BstLean.Part183D19

/-!
# Part 184 (file `Def`): the interface of the descent to `n ≥ 18 500`

No proof is left open; no `native_decide` or `axiom` is used.

* `WflB n O q = 2·(1.81·L)·√(m t T/2)`, `L = √(t·qO²/(n − 2))`, `T = q n O²/(n − 2)`: the energy
  fluctuation allowance of the moment expansion for independent rows (Lemma BE in the form
  "eighth moment of a sum of independent centred row terms"). Against Part 183's `WflJ`
  (`2c₈L(√(m t T/2) + c₈√t·O)`, `c₈ = 1.8·π/2`) the main constant `1.8·π/2 ≈ 2.827` becomes
  `1.81` (`105^{1/8} ≈ 1.789`): the rotation constant `π/2` is removed, and the concentration term
  `c₈√t·O` is not needed.
* `EnB_stmt`: Part 183's `EnJ_stmt` with `WflB`, for `n ≥ 16 000` and `q ≥ 1/10`.
* `roomT185 = −0.0007`, `FREE185_stmt = FREEg_stmt 18500 roomT185`, `HQF185_stmt`.
-/

namespace BstLean.Part184

open MeasureTheory ProbabilityTheory Real Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part170

/-- **The energy fluctuation allowance of the row moment expansion**:
`W_fl = 2·(1.81·L)·√(m t T/2)`, `L = √(t·qO²/(n − 2))`, `T = q n O²/(n − 2)`. -/
noncomputable def WflB (n : ℕ) (O q : ℝ) : ℝ :=
  2 * (181 / 100 * √(tA n * (q * O ^ 2 / ((n : ℝ) - 2)))) *
    √((mA n : ℝ) * tA n * (q * n * O ^ 2 / ((n : ℝ) - 2)) / 2)

/-- **The energy fluctuation bound of the row moment expansion** (statement): Part 183's
`EnJ_stmt` with the allowance `WflB`, for `n ≥ 16 000` and `q ≥ 1/10`. -/
def EnB_stmt : Prop :=
  ∀ {n : ℕ}, 16000 ≤ n → ∀ (c : Ret n) (g : ℕ), nodeS c g ^ 2 ≤ 1 → ∀ {O : ℝ}, 0 < O →
    OpB (A1 c) O → ∀ {q : ℝ}, 1 / 10 ≤ q → 1 - nodeS c g ^ 2 ≤ q → ∀ {B : ℝ}, 0 < B →
    ∫⁻ ξ₁, ∫⁻ ξ₂, ENNReal.ofReal (biasW c g ξ₁ ξ₂ ^ 8) ∂stdGauss (Fin (mA n))
      ∂stdGauss (Fin (mA n)) ≤ ENNReal.ofReal (B ^ 8) →
    ∫⁻ M, ENNReal.ofReal (exWn (withA2 c M) g ^ 8) ∂gaussMat (mA n) (mA n) (tA n) ≤
      ENNReal.ofReal ((WflB n O q + B) ^ 8)

/-- **The extra room `−0.0007` at `n ≥ 18 500`** (negative: the frame tails at `18 500` exceed the
frame share of the budget, and the chain pays the difference from its own room). -/
noncomputable def roomT185 : ℝ := -(7 / 10000)

lemma roomT185_eq : roomT185 = -(7 / 10000) := rfl

/-- **The frame junction at `n ≥ 18 500`.** -/
def FREE185_stmt : Prop := BstLean.Part183.FREEg_stmt 18500 roomT185

/-- Lemma HQ and the frame junction at `18 500`. -/
def HQF185_stmt : Prop := BstLean.Part180.HQ_stmt ∧ FREE185_stmt

end BstLean.Part184
