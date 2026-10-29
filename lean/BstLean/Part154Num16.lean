import BstLean.Part154NumA16
import BstLean.Part154NumB16

/-!
# Part 154: the numbers of the centre bounds for `n ≥ 16384`, `0.46 ≤ θ ≤ 0.55`, `J = n`,
`M_P = 1.1911`
The proofs are in `Part154NumA16` and `Part154NumB16`; this file joins them.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part154

open Real
open BstLean.Part150 (epsJ)
open BstLean.Part153 (wn N22bar N24bar)

theorem rhoBar_lt16 {n : ℕ} (hn : 16384 ≤ n) : rhoBar n csC < 1 / 4 :=
  rhoBar_ltA16 hn

/-- `ξ_c(θ) ≤ 0.3235`, `b_n(θ) ≤ 0.00112`. -/
theorem xiCn_le16 {n : ℕ} (hn : 16384 ≤ n) {θ : ℝ} (h0 : 46 / 100 ≤ θ) (h1 : θ ≤ 55 / 100) :
    0 ≤ xiCn n θ ∧ xiCn n θ ≤ 3235 / 10000 ∧ 0 ≤ bN n csC θ ∧ bN n csC θ ≤ 112 / 100000 :=
  xiCn_leA16 hn h0 h1

theorem eMP_le16 {n : ℕ} (hn : 16384 ≤ n) {θ : ℝ} (h0 : 46 / 100 ≤ θ) (h1 : θ ≤ 55 / 100) :
    eMP n (11 / 1000) (xiCn n θ) (bN n csC θ) ≤ 1 / 10 :=
  eMP_leA16 hn h0 h1

/-- `√ξ°_hp ≤ 0.6885`. -/
theorem x1_le16 {n : ℕ} (hn : 16384 ≤ n) {θ : ℝ} (h0 : 46 / 100 ≤ θ) (h1 : θ ≤ 55 / 100) :
    cD n 12 (11 / 1000) (xiCn n θ) + xiNr n θ (11911 / 10000) ≤ 6885 / 10000 :=
  x1_leB16 hn h0 h1 (xiCn_leA16 hn h0 h1).1 (xiCn_leA16 hn h0 h1).2.1

/-- `√ξ°_∥ ≤ 0.1595`. -/
theorem x2_le16 {n : ℕ} (hn : 16384 ≤ n) {θ : ℝ} (h0 : 46 / 100 ≤ θ) (h1 : θ ≤ 55 / 100) :
    LamMP n 12 (11 / 1000) (xiCn n θ) (bN n csC θ) + xiNr n θ (11911 / 10000) ≤
      1595 / 10000 :=
  x2_leB16 hn h0 h1 (xiCn_leA16 hn h0 h1).1 (xiCn_leA16 hn h0 h1).2.1 (xiCn_leA16 hn h0 h1).2.2.1 (xiCn_leA16 hn h0 h1).2.2.2

theorem plow_ge16 {n : ℕ} (hn : 16384 ≤ n) : 56 / 100 ≤ plow n (11 / 1000) :=
  plow_geB16 hn

/-- `ϵ_J ≤ 0.0075` for `J = n` atoms. -/
theorem epsJ_le16 {n : ℕ} (hn : 16384 ≤ n) :
    0 ≤ epsJ n n n (wn n) csC (11 / 1000) (deltaChi n 12) ∧
    epsJ n n n (wn n) csC (11 / 1000) (deltaChi n 12) ≤ 75 / 10000 :=
  epsJ_leB16 hn

theorem ebo_le16 : 1 + 2 * (11 / 1000 : ℝ) - (1 - 1 / π) * (csC / 2) * (46 / 100) ≤ 819 / 1000 :=
  ebo_leB

/-- The norm deviations in the form of Part 151. -/
theorem Nbar_le16 {n : ℕ} (hn : 16384 ≤ n) :
    0 ≤ N22bar n 12 ∧ N22bar n 12 ≤ 18334 / 1000 / (n : ℝ) ∧
    0 ≤ N24bar n 12 ∧ N24bar n 12 ≤ 24779 / 1000 / (n : ℝ) :=
  Nbar_leB16 hn

end BstLean.Part154
