import BstLean.Part48Defs

/-!
# Part 66, definitions: the weighted-rotation small-ball level

Source: `delegations/answers/omSBL-cx.md`, "Preferred route" (the simple level).
Specification: `delegations/statements/p66-spec.md`.

`tW h p = (p / (2 (2h+1)²))^{2h}`. `Part66Level.sb_level_weighted` proves `SBLevel h p (tW h p)`
for `1 ≤ h`, `0 < p`.
-/

namespace BstLean.Part66

/-- The weighted-rotation small-ball level `(p / (2 (2h+1)²))^{2h}`. -/
noncomputable def tW (h : ℕ) (p : ℝ) : ℝ := (p / (2 * (2 * (h : ℝ) + 1) ^ 2)) ^ (2 * h)

lemma tW_pos (h : ℕ) (p : ℝ) (hp : 0 < p) : 0 < tW h p := by
  unfold tW; positivity

end BstLean.Part66
