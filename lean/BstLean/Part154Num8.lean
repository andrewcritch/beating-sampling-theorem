import BstLean.Part154NumA8
import BstLean.Part154NumB8

/-!
# Part 154: the numbers of the centre bounds for `n ≥ 8192`, `0.457 ≤ θ ≤ 0.555`, `J = n`,
`M_P = 1.2578` (the window of `θ_in` that the `W` stage of Lean gives at `n ≥ 8192`)
The proofs are in `Part154NumA8` and `Part154NumB8`; this file joins them.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part154

open Real
open BstLean.Part150 (epsJ)
open BstLean.Part153 (wn N22bar N24bar)

theorem xiCn_le8 {n : ℕ} (hn : 8192 ≤ n) {θ : ℝ} (h0 : 457 / 1000 ≤ θ) (h1 : θ ≤ 555 / 1000) :
    0 ≤ xiCn n θ ∧ xiCn n θ ≤ 3370 / 10000 ∧ 0 ≤ bN n csC θ ∧ bN n csC θ ≤ 231 / 100000 :=
  xiCn_leA8 hn h0 h1

theorem eMP_le8 {n : ℕ} (hn : 8192 ≤ n) {θ : ℝ} (h0 : 457 / 1000 ≤ θ) (h1 : θ ≤ 555 / 1000) :
    eMP n (11 / 1000) (xiCn n θ) (bN n csC θ) ≤ 1 / 10 :=
  eMP_leA8 hn h0 h1

theorem x1_le8 {n : ℕ} (hn : 8192 ≤ n) {θ : ℝ} (h0 : 457 / 1000 ≤ θ) (h1 : θ ≤ 555 / 1000) :
    cD n 12 (11 / 1000) (xiCn n θ) + xiNr n θ (12578 / 10000) ≤ 7500 / 10000 :=
  x1_leB8 hn h0 h1 (xiCn_leA8 hn h0 h1).1 (xiCn_leA8 hn h0 h1).2.1

theorem x2_le8 {n : ℕ} (hn : 8192 ≤ n) {θ : ℝ} (h0 : 457 / 1000 ≤ θ) (h1 : θ ≤ 555 / 1000) :
    LamMP n 12 (11 / 1000) (xiCn n θ) (bN n csC θ) + xiNr n θ (12578 / 10000) ≤
      2280 / 10000 :=
  x2_leB8 hn h0 h1 (xiCn_leA8 hn h0 h1).1 (xiCn_leA8 hn h0 h1).2.1
    (xiCn_leA8 hn h0 h1).2.2.1 (xiCn_leA8 hn h0 h1).2.2.2

theorem ebo_le8 :
    1 + 2 * (11 / 1000 : ℝ) - (1 - 1 / π) * (csC / 2) * (457 / 1000) ≤ 8203 / 10000 :=
  ebo_leB8

theorem Nbar_le8 {n : ℕ} (hn : 8192 ≤ n) :
    0 ≤ N22bar n 12 ∧ N22bar n 12 ≤ 18340 / 1000 / (n : ℝ) ∧
    0 ≤ N24bar n 12 ∧ N24bar n 12 ≤ 24779 / 1000 / (n : ℝ) :=
  Nbar_leB8 hn

end BstLean.Part154
