import Mathlib

/-!
# Part 66: factorial identities for ordered Lagrange interpolation

* `prod_dist`: `∏_{j ≤ d, j ≠ i} |i − j| = i! (d − i)!`.
* `sum_inv_fact`: `Σ_{i ≤ d} 1/(i! (d − i)!) = 2^d / d!`.

Do not use `native_decide` or `axiom` anywhere.
-/

namespace BstLean.Part66

open Finset

lemma prod_dist (d i : ℕ) (hi : i ≤ d) :
    ∏ j ∈ (range (d + 1)).erase i, |(i : ℝ) - j| = (i.factorial : ℝ) * (d - i).factorial := by
  have hsplit : (range (d + 1)).erase i = range i ∪ Ico (i + 1) (d + 1) := by
    ext j; simp only [mem_erase, mem_range, mem_union, mem_Ico]; omega
  have hdisj : Disjoint (range i) (Ico (i + 1) (d + 1)) := by
    rw [Finset.disjoint_left]; intro j hj hj'; simp only [mem_range, mem_Ico] at hj hj'; omega
  rw [hsplit, prod_union hdisj]
  congr 1
  · have : ∀ j ∈ range i, |(i : ℝ) - j| = ((i - 1 - j : ℕ) : ℝ) + 1 := by
      intro j hj
      have hj' := mem_range.mp hj
      rw [abs_of_nonneg (by have : (j : ℝ) ≤ i := by exact_mod_cast hj'.le
                            linarith)]
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
    rw [prod_congr rfl this]
    rw [prod_range_reflect (fun k => (k : ℝ) + 1) i]
    exact_mod_cast (prod_range_add_one_eq_factorial i)
  · rw [prod_Ico_eq_prod_range]
    have : ∀ k ∈ range (d + 1 - (i + 1)), |(i : ℝ) - ((i + 1 + k : ℕ) : ℝ)| = (k : ℝ) + 1 := by
      intro k _
      push_cast
      rw [abs_of_nonpos (by linarith)]; ring
    rw [prod_congr rfl this, show d + 1 - (i + 1) = d - i by omega]
    exact_mod_cast (prod_range_add_one_eq_factorial (d - i))

lemma sum_inv_fact (d : ℕ) :
    ∑ i ∈ range (d + 1), (1 : ℝ) / ((i.factorial : ℝ) * (d - i).factorial) =
      2 ^ d / d.factorial := by
  have hd : (0 : ℝ) < d.factorial := by exact_mod_cast d.factorial_pos
  have : ∀ i ∈ range (d + 1), (1 : ℝ) / ((i.factorial : ℝ) * (d - i).factorial) =
      (d.choose i : ℝ) / d.factorial := by
    intro i hi
    have hi' : i ≤ d := Nat.lt_succ_iff.mp (mem_range.mp hi)
    rw [Nat.cast_choose ℝ hi']
    have : (0 : ℝ) < i.factorial := by exact_mod_cast i.factorial_pos
    have : (0 : ℝ) < (d - i).factorial := by exact_mod_cast (d - i).factorial_pos
    field_simp
  rw [sum_congr rfl this, ← sum_div]
  congr 1
  exact_mod_cast Nat.sum_range_choose d

end BstLean.Part66
