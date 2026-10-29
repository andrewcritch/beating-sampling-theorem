import BstLean.Part184Def
import BstLean.Part173Cov

/-!
# Part 184 (file `Def2`): the location fluctuation statement of the row moment expansion

No proof is left open; no `native_decide` or `axiom` is used.

* `FflB n O q = 1.81·√n·√(t·qO²/(n − 2))/2`: Part 173's `FflQ` (`(π/2)·1.8·√n·√(tΛ)/2`) with the
  rotation constant `π/2·1.8 ≈ 2.83` replaced by `1.81` (moment expansion over independent rows).
* `EnFB_stmt`: Part 173's `exFn_mom_q` with `FflB`, for `n ≥ 16 000` and `q ≥ 1/10`.
-/

namespace BstLean.Part184

open MeasureTheory ProbabilityTheory Real Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part170

/-- **The location fluctuation allowance of the row moment expansion**. -/
noncomputable def FflB (n : ℕ) (O q : ℝ) : ℝ :=
  181 / 100 * √(n : ℝ) * √(tA n * (q * O ^ 2 / ((n : ℝ) - 2))) / 2

/-- **The location fluctuation bound of the row moment expansion** (statement). -/
def EnFB_stmt : Prop :=
  ∀ {n : ℕ}, 16000 ≤ n → ∀ (c : Ret n) (g : ℕ), nodeS c g ^ 2 ≤ 1 → ∀ {O : ℝ}, 0 < O →
    OpB (A1 c) O → ∀ {q : ℝ}, 1 / 10 ≤ q → 1 - nodeS c g ^ 2 ≤ q → ∀ {B : ℝ}, 0 < B →
    ∫⁻ ξ₁, ∫⁻ ξ₂, ENNReal.ofReal (biasF c g ξ₁ ξ₂ ^ 8) ∂stdGauss (Fin (mA n))
      ∂stdGauss (Fin (mA n)) ≤ ENNReal.ofReal (B ^ 8) →
    ∫⁻ M, ENNReal.ofReal (exFn (withA2 c M) g ^ 8) ∂gaussMat (mA n) (mA n) (tA n) ≤
      ENNReal.ofReal ((FflB n O q + B) ^ 8)

end BstLean.Part184
