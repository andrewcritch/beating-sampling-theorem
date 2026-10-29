import BstLean.Part154NumA
import BstLean.Part154NumB

/-!
# Part 154: the numbers of the centre bounds for `n ≥ 8192`, `0.46 ≤ θ ≤ 0.541`, `J = n`
The proofs are in `Part154NumA` and `Part154NumB`; this file joins them.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part154

open Real
open BstLean.Part150 (epsJ)
open BstLean.Part153 (wn N22bar)

theorem rhoBar_lt {n : ℕ} (hn : 8192 ≤ n) : rhoBar n csC < 1 / 4 :=
  rhoBar_ltA hn

/-- `ξ_c(θ) ≤ 0.3285`, `b_n(θ) ≤ 0.00225` (the document's script: `0.3276`, `0.00224` at
`n = 8192`, `θ_max = 0.5408`). -/
theorem xiCn_le {n : ℕ} (hn : 8192 ≤ n) {θ : ℝ} (h0 : 46 / 100 ≤ θ) (h1 : θ ≤ 541 / 1000) :
    0 ≤ xiCn n θ ∧ xiCn n θ ≤ 3285 / 10000 ∧ 0 ≤ bN n csC θ ∧ bN n csC θ ≤ 225 / 100000 :=
  xiCn_leA hn h0 h1

theorem eMP_le {n : ℕ} (hn : 8192 ≤ n) {θ : ℝ} (h0 : 46 / 100 ≤ θ) (h1 : θ ≤ 541 / 1000) :
    eMP n (11 / 1000) (xiCn n θ) (bN n csC θ) ≤ 1 / 10 :=
  eMP_leA hn h0 h1

/-- `√ξ°_hp ≤ 0.7422` (so `ξ°_hp ≤ 0.5509`; the document's script: `0.5496`). -/
theorem x1_le {n : ℕ} (hn : 8192 ≤ n) {θ : ℝ} (h0 : 46 / 100 ≤ θ) (h1 : θ ≤ 541 / 1000) :
    cD n 12 (11 / 1000) (xiCn n θ) + xiNr n θ (12578 / 10000) ≤ 7422 / 10000 :=
  x1_leB hn h0 h1 (xiCn_leA hn h0 h1).1 (xiCn_leA hn h0 h1).2.1

/-- `√ξ°_∥ ≤ 0.2270` (so `ξ°_∥ ≤ 0.0516`; the document's script: `0.0512`). -/
theorem x2_le {n : ℕ} (hn : 8192 ≤ n) {θ : ℝ} (h0 : 46 / 100 ≤ θ) (h1 : θ ≤ 541 / 1000) :
    LamMP n 12 (11 / 1000) (xiCn n θ) (bN n csC θ) + xiNr n θ (12578 / 10000) ≤
      2270 / 10000 :=
  x2_leB hn h0 h1 (xiCn_leA hn h0 h1).1 (xiCn_leA hn h0 h1).2.1 (xiCn_leA hn h0 h1).2.2.1 (xiCn_leA hn h0 h1).2.2.2

/-- `p_low ≥ 0.56`. -/
theorem plow_ge {n : ℕ} (hn : 8192 ≤ n) : 56 / 100 ≤ plow n (11 / 1000) :=
  plow_geB hn

/-- `ϵ_J ≤ 0.0106` for `J = n` atoms. -/
theorem epsJ_le {n : ℕ} (hn : 8192 ≤ n) :
    0 ≤ epsJ n n n (wn n) csC (11 / 1000) (deltaChi n 12) ∧
    epsJ n n n (wn n) csC (11 / 1000) (deltaChi n 12) ≤ 106 / 10000 :=
  epsJ_leB hn

/-- `√e°_{b,max} ≤ 0.905` for `θ ≥ 0.46`: `1 + 2δ_e − (1 − 1/π)(c_s/2)·0.46 ≤ 0.819`. -/
theorem ebo_le : 1 + 2 * (11 / 1000 : ℝ) - (1 - 1 / π) * (csC / 2) * (46 / 100) ≤ 819 / 1000 :=
  ebo_leB

end BstLean.Part154
