import BstLean.Part282Draw
import BstLean.Part189Search

/-!
# Part 288: a search with arithmetic and control costs

The counting convention is the paper's unit arithmetic convention, including index work.
Each real or index addition, subtraction, multiplication, division, or comparison costs one.
We also charge one for each conditional branch. Register copies, constants, and interpreting
an index as a real are free. The cost counter is bookkeeping, not an executed register.
Each `let` binds a result once; in particular the recursive call is executed once.

An active iteration costs 9 on the upper branch and 10 on the lower branch:
* `lo < hi` and its branch: 2;
* `(lo + hi + 1) / 2`: 3 index operations;
* `g * Δ`, `L + g * Δ`, and comparison with `s`: 3;
* the comparison's branch: 1;
* the lower branch's `g - 1`: 1 (the upper branch only copies `g`).
The terminal loop test and branch cost 2. The setup costs 5 when `L < H`:
the comparison and branch, `H - L`, division by `J`, and `J - 1`.
The degenerate branch costs 2. Thus setup and final work cost at most 7, within the
paper's ten-operation reserve. This also counts the dimension-dependent `J - 1`.
No clipping or real floor primitive is executed: the value theorem proves saturation and ties.
-/

namespace BstLean.Part288

open BstLean.Part282 BstLean.Part157 BstLean.Part189

noncomputable section

open Classical in
/-- Binary search with a cached spacing and an operation count. -/
def searchLoop (L Δ s : ℝ) (lo hi : ℕ) : ℕ × ℕ :=
  if lo < hi then
    let g := (lo + hi + 1) / 2
    let boundary := L + (g : ℝ) * Δ
    if boundary ≤ s then
      let next := searchLoop L Δ s g hi
      (next.1, next.2 + 9)
    else
      let next := searchLoop L Δ s lo (g - 1)
      (next.1, next.2 + 10)
  else (lo, 2)
termination_by hi - lo
decreasing_by all_goals omega

/-- The new loop follows the old loop and charges at most ten per iteration plus two. -/
theorem searchLoop_spec (L Δ s : ℝ) : ∀ d lo hi, hi - lo = d →
    (searchLoop L Δ s lo hi).1 = (bsearch (fun g => L + g * Δ ≤ s) lo hi).1 ∧
    (searchLoop L Δ s lo hi).2 ≤ 10 * (bsearch (fun g => L + g * Δ ≤ s) lo hi).2 + 2 := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro lo hi hd
    rw [searchLoop, bsearch]
    by_cases h : lo < hi
    · rw [if_pos h, if_pos h]
      dsimp only
      by_cases hm : L + ((lo + hi + 1) / 2 : ℕ) * Δ ≤ s
      · rw [if_pos hm, if_pos hm]
        have hr := ih (hi - (lo + hi + 1) / 2) (by omega) _ hi rfl
        exact ⟨hr.1, by dsimp only; omega⟩
      · rw [if_neg hm, if_neg hm]
        have hr := ih ((lo + hi + 1) / 2 - 1 - lo) (by omega) lo _ rfl
        exact ⟨hr.1, by dsimp only; omega⟩
    · rw [if_neg h, if_neg h]
      exact ⟨rfl, by norm_num⟩

open Classical in
/-- Node selection: compute the spacing once, then run the counted loop. -/
def selectNode' (J : ℕ) (L H s : ℝ) : ℕ × ℕ :=
  if L < H then
    let Δ := (H - L) / (J : ℝ)
    let next := searchLoop L Δ s 0 (J - 1)
    (next.1, next.2 + 5)
  else (0, 2)

theorem selectNode'_eq_selectNode (J : ℕ) (L H s : ℝ) :
    (selectNode' J L H s).1 = (selectNode J L H s).1 := by
  unfold selectNode' selectNode
  split_ifs with h
  · exact (searchLoop_spec L ((H - L) / J) s (J - 1 - 0) 0 (J - 1) rfl).1
  · rfl

/-- Includes all endpoints, ties, and degenerate intervals. -/
theorem selectNode'_eq {J : ℕ} (hJ : 1 ≤ J) (L H s : ℝ) :
    (selectNode' J L H s).1 = nodeIdx J L H s := by
  rw [selectNode'_eq_selectNode, selectNode_eq hJ]

/-- At most `clog 2 J` active iterations, including when `J` is a power of two. -/
theorem bsearch_count_clog {J : ℕ} (hJ : 1 ≤ J) (p : ℕ → Prop) :
    (bsearch p 0 (J - 1)).2 ≤ Nat.clog 2 J := by
  have hc := bsearch_count p (J - 1) 0 (J - 1) (by omega)
  by_cases h : J - 1 = 0
  · rw [if_pos h] at hc
    omega
  · rw [if_neg h] at hc
    have hp := Nat.le_pow_clog (by norm_num : 1 < 2) J
    have hl : Nat.log 2 (J - 1) < Nat.clog 2 J :=
      Nat.log_lt_of_lt_pow h (by omega)
    omega

/-- The full search fits the paper's ten-per-iteration and ten setup/final allowance. -/
theorem selectNode'_cost {J : ℕ} (hJ : 1 ≤ J) (L H s : ℝ) :
    (selectNode' J L H s).2 ≤ 10 * Nat.clog 2 J + 10 := by
  unfold selectNode'
  split_ifs with h
  · have hc := (searchLoop_spec L ((H - L) / J) s (J - 1 - 0) 0 (J - 1) rfl).2
    have hb := bsearch_count_clog hJ (fun g => L + g * ((H - L) / J) ≤ s)
    dsimp only
    omega
  · dsimp only
    omega

/-- The concrete search cost is bounded by the Part 189 search price. -/
theorem selectNode'_le_searchPrice {n : ℕ} (hn : 8000 ≤ n) (L H s : ℝ) :
    (selectNode' (Js n) L H s).2 ≤ searchPrice n := by
  exact selectNode'_cost (by unfold Js; omega) L H s

theorem selectNode'_cost_le {n : ℕ} (hn : 8000 ≤ n) (L H s : ℝ) :
    (selectNode' (Js n) L H s).2 ≤ 5 * n + 70 :=
  (selectNode'_le_searchPrice hn L H s).trans (searchPrice_le hn)

end
end BstLean.Part288
