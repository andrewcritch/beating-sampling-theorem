import BstLean.Part66General
import BstLean.Part66Ordered

/-!
# Part 66, Stage A item 2: the ordered-node small-ball level

Source: `delegations/answers/omSBL-cx.md`, "Preferred route", step 1 (ordered interpolation).

  `tO h p = p^{2h} (2h)! / (4^{2h} (2h+1)^{4h−1})`,
  `sb_level_ordered h (1 ≤ h) p (0 < p) : SBLevel h p (tO h p)`.

Route: `Part66Ordered.trig_sublevel_ord` gives the sublevel constant `C = 8πN/((2h)!)^α`, and
`Part66General.sb_level_of_C` applies, with `C t^α N^{1−α} = 2π p` exactly.

Do not use `native_decide` or `axiom` anywhere.
-/

namespace BstLean.Part66

open MeasureTheory
open scoped ENNReal
open BstLean.Part48 (SBLevel IsTrig circ)

/-- The ordered-node small-ball level `p^{2h} (2h)! / (4^{2h} (2h+1)^{4h−1})`. -/
noncomputable def tO (h : ℕ) (p : ℝ) : ℝ :=
  p ^ (2 * h) * ((2 * h).factorial : ℝ) / (4 ^ (2 * h) * (2 * (h : ℝ) + 1) ^ (4 * h - 1))

lemma tO_pos (h : ℕ) (p : ℝ) (hp : 0 < p) : 0 < tO h p := by
  unfold tO
  have : (0 : ℝ) < (2 * h).factorial := by exact_mod_cast (2 * h).factorial_pos
  positivity

lemma tO_eq (h : ℕ) (hh : 1 ≤ h) (p : ℝ) :
    tO h p = (p / (4 * (2 * (h : ℝ) + 1) ^ 2)) ^ (2 * h) *
      (((2 * h).factorial : ℝ) * (2 * (h : ℝ) + 1)) := by
  unfold tO
  set N : ℝ := 2 * (h : ℝ) + 1 with hN
  have hN0 : 0 < N := by positivity
  have e : N ^ (4 * h) = N ^ (4 * h - 1) * N := by
    rw [← pow_succ]; congr 1; omega
  rw [div_pow, mul_pow, ← pow_mul, show 2 * (2 * h) = 4 * h by ring, e]
  have : 0 < N ^ (4 * h - 1) := by positivity
  field_simp

/-- **The ordered-node small-ball level** (p66-spec Stage A item 2). -/
theorem sb_level_ordered (h : ℕ) (hh : 1 ≤ h) (p : ℝ) (hp : 0 < p) : SBLevel h p (tO h p) := by
  have hpi := Real.pi_pos
  set N : ℝ := 2 * (h : ℝ) + 1 with hN
  have hN0 : 0 < N := by positivity
  set α : ℝ := (1 : ℝ) / (2 * h) with hα
  set D : ℝ := ((2 * h).factorial : ℝ) with hD
  have hD0 : 0 < D := by rw [hD]; exact_mod_cast (2 * h).factorial_pos
  have hDα : 0 < D ^ α := Real.rpow_pos_of_pos hD0 _
  set C : ℝ := 8 * Real.pi * N / D ^ α with hC
  have hC0 : 0 < C := by positivity
  refine sb_level_of_C h hh C hC0 ?_ p (tO h p) (tO_pos h p hp) ?_
  · intro F hF ε s0 hε hM
    refine (trig_sublevel_ord h hh F hF ε s0 hε hM).trans (le_of_eq ?_)
    congr 1
    rw [show ε / (|F s0| * ((2 * h).factorial : ℝ)) = (ε / |F s0|) / D by rw [hD]; ring,
      Real.div_rpow (by positivity) hD0.le, hC]
    ring
  · apply le_of_eq
    have hH0 : (2 * h : ℕ) ≠ 0 := by omega
    have hinv : α = ((2 * h : ℕ) : ℝ)⁻¹ := by rw [hα]; push_cast; ring
    have ht : tO h p ^ α = p / (4 * N ^ 2) * (D ^ α * N ^ α) := by
      rw [tO_eq h hh p, ← hN, ← hD, Real.mul_rpow (by positivity) (by positivity),
        Real.mul_rpow hD0.le hN0.le, hinv, Real.pow_rpow_inv_natCast (by positivity) hH0]
    rw [← hα, ht, hC]
    have e1 : N ^ α * N ^ (1 - α) = N := by
      rw [← Real.rpow_add hN0]; simp
    calc 8 * Real.pi * N / D ^ α * (p / (4 * N ^ 2) * (D ^ α * N ^ α)) * N ^ (1 - α)
        = 8 * Real.pi * N / D ^ α * (p / (4 * N ^ 2) * D ^ α) * (N ^ α * N ^ (1 - α)) := by ring
      _ = 2 * Real.pi * p := by rw [e1]; field_simp; ring

end BstLean.Part66
