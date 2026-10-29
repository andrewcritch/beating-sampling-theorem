import BstLean.Part43Defs

/-!
# Part 44: Theorem G of Part 43 at failure probability `δ` (instantiated at `δ = 1/100`)

Role: `delegations/statements/p44-delta01.md`. This is a copy of the Part 43 formalization in which
the failure probability `1/2` is a parameter `δ`. Every Part 41–43 lemma that does not depend on `δ` is
reused by import.

* `BudgetOK44 n d k q δ` is `BudgetOK43 n d k q` with the last conjunct `Φ43 ≤ 1/2` replaced by
  `Φ43 ≤ δ`. `BudgetOK43 n d k q` is `BudgetOK44 n d k q (1/2)` by definition.
* `prm44 = (p_sb, x, β, η_c) = (0.0086, 16, 10⁻⁶, 0.01)`: the parameters of the certificates at
  `δ = 1/100` (script `delegations/checks/p44delta/n0_p44.py`).

Do not use `native_decide` or `axiom` anywhere.
-/

namespace BstLean.Part44

open BstLean.Part41 (thetaT Kc etaR Bfix Pn)
open BstLean.Part43

/-- The conditions of the proof of Theorem G at `n`, with failure budget `δ`. -/
def BudgetOK44 (n d k : ℕ) (q : Params43) (δ : ℝ) : Prop :=
  2 ≤ n ∧ 1 ≤ d ∧ 0 < tau43 n d k ∧
  0 < q.psb ∧ q.psb < 1 - Real.exp (-1) ∧ 0 < q.x ∧ 0 < q.beta ∧ 0 < q.eta ∧
  (1 + 1 / q.eta) * thetaT n d k < 1 ∧ etaR n d q.x < 1 ∧ 0 < Kc n d k q.eta ∧
  0 < gam43 n d k q ∧ 455 / 1000 * Bfix n k < (1 - nu43) * (91 / 100) * Pn n d ∧
  Phi43 n d k q ≤ δ

/-- `BudgetOK43` is the case `δ = 1/2`. -/
theorem budgetOK43_iff (n d k : ℕ) (q : Params43) : BudgetOK43 n d k q ↔ BudgetOK44 n d k q (1 / 2) :=
  Iff.rfl

/-- A budget at `δ ≤ 1/2` is a Part 43 budget. -/
theorem BudgetOK44.toOK43 {n d k : ℕ} {q : Params43} {δ : ℝ} (h : BudgetOK44 n d k q δ) (hδ : δ ≤ 1 / 2) :
    BudgetOK43 n d k q := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14.trans hδ⟩

/-- The parameters of the certificates at `δ = 1/100`: `p_sb = 0.0086`, `x = 16`, `β = 10⁻⁶`,
`η_c = 0.01`. -/
noncomputable def prm44 : Params43 := ⟨86 / 10000, 16, 1 / 1000000, 1 / 100⟩

end BstLean.Part44
