import BstLean.Part170All

/-!
# Part 173 (file `Def`): the two fluctuation allowances with the latitude factor `q ≥ 1 − s²`

No proof is left open; no `native_decide` or `axiom` is used.

Part 170's `Ffl n O` and `Wfl n O` use the covariance bound `Λ = O²/(n − 2)` of `cov_bound`. The
transverse sphere at latitude `s` has radius `√(1 − s²)`, so the covariance has the extra factor
`1 − s²` (the paper's `(1 − s²)` in `t7:p08:fl`, `t7:p08:energy`). `FflQ n O q`, `WflQ n O q` are
Part 170's two allowances with `Λ = q·O²/(n − 2)`.
-/

namespace BstLean.Part173

open Real
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part170

/-- Part 170's `Ffl` with the covariance `q·O²/(n − 2)`. -/
noncomputable def FflQ (n : ℕ) (O q : ℝ) : ℝ :=
  π / 2 * (18 / 10) * √(n : ℝ) * √(tA n * (q * O ^ 2 / ((n : ℝ) - 2))) / 2

/-- Part 170's `Wfl` with the covariance `q·O²/(n − 2)` (the sup factor `√(t_A O²)` unchanged). -/
noncomputable def WflQ (n : ℕ) (O q : ℝ) : ℝ :=
  ((π / 2 * (25 / 10) * √(tA n * (q * O ^ 2 / ((n : ℝ) - 2)))) ^ 2 +
    2 * (π / 2 * (18 / 10) * √(tA n * (q * O ^ 2 / ((n : ℝ) - 2)))) +
    (π / 2 * √(tA n * (q * O ^ 2 / ((n : ℝ) - 2)))) ^ 2) +
  2 * (π / 2 * (18 / 10) * √(tA n * (q * O ^ 2 / ((n : ℝ) - 2)))) * √(tA n * O ^ 2) *
    (√3 * √((mA n : ℝ) + 8))

end BstLean.Part173
