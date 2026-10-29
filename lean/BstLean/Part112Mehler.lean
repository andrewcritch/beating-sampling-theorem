import BstLean.Part112MehlerA
import BstLean.Part112Chaos

/-!
# Part 112: the second-order Gebelein inequality (signed Mehler step)

`mehler2 : Mehler2`: for a Gaussian pair with correlation `ρ ∈ [−1, 1]` and bounded measurable
`f`, `g`: `|Cov(f(X), g(Y)) − ρ·c_f·c_g| ≤ 2ρ²·a₂(f)·a₂(g)`, `c_f = E[f(X) X]`,
`a₂(f)² = Var f − |c_f|²`.

Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part112

/-- **The second-order Gebelein inequality.** -/
theorem mehler2 : Mehler2 := mehler2_of chaosLimit

#print axioms mehler2

end BstLean.Part112
