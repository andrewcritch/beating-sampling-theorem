import BstLean.Part262Root

/-! A fixed enclosure in Part252 does not hold throughout the target interval.
This is an obstruction to direct substitution, not a network counterexample. -/
namespace BstLean.Part262
open Real

theorem fixed_sigma_lower_fails12349 :
    √(2 / (12349 : ℝ) * BstLean.Part252.mixtureFloor) < 596 / 10 ^ 5 := by
  apply (sqrt_lt' (by norm_num : (0 : ℝ) < 596 / 10 ^ 5)).mpr
  norm_num [BstLean.Part252.mixtureFloor]

theorem fixed_sigma_enclosure_not_uniform :
    ¬ ∀ n ∈ Set.Icc (12225 : ℕ) 12349,
      (596 / 10 ^ 5 : ℝ) ≤ √(2 / (n : ℝ) * BstLean.Part252.mixtureFloor) := by
  intro h
  have hn : (12349 : ℕ) ∈ Set.Icc 12225 12349 := by norm_num
  exact (not_le_of_gt fixed_sigma_lower_fails12349) (h 12349 hn)

end BstLean.Part262
