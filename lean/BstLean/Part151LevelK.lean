import BstLean.Part151LevelNum
import BstLean.Part151Kap

/-!
# Part 151, item 5: the level with the constant `κ = 1/3` of the Gaussian tail

Role: `delegations/statements/p151-spec.md`, item 5 ("sharper constants").
`two_PhiBar_le_third` (`Part151Kap`): `2Φ̄(a) ≤ (1/3)/a²` (the best constant is `0.3311…`).

* **`gaussLevel151_third`**: the straight-line program `fullProg150 k n n` of Part 150 succeeds
  with probability at least `393/500 = 0.786`, for every `n ≥ 16 384`, `k ≥ 100n`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part151

open MeasureTheory ProbabilityTheory Set
open BstLean.Part130
open BstLean.Part150 (fullProg150 fullVal)

variable {k n : ℕ}

/-- **The Lean level with the Gaussian last step and the constant `κ = 1/3`: the program
`fullProg150 k n n` of Part 150 succeeds with probability at least `0.786`, for every
`n ≥ 16 384`, `k ≥ 100n`.** (Part 150, with Chebyshev's inequality at the last step: `7/10`.) -/
theorem gaussLevel151_third (hn : 16384 ≤ n) (hk : 100 * n ≤ k) :
    393 / 500 ≤ (jointP k n).real
      {p | |(fullProg150 k n n).eval (fullVal p.1.1 p.1.2.1 p.1.2.2 p.2) () -
          Bn p.1.1 p.1.2.1 p.1.2.2| ≤ sdn p.1.1 p.1.2.1 p.1.2.2 / 2} := by
  have h := gaussLevel151_of_kap (κ := 1 / 3) (fun a ha => two_PhiBar_le_third ha) (by norm_num)
    hn hk
  refine le_trans ?_ h
  norm_num

end BstLean.Part151
