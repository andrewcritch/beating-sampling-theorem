import BstLean.Part269TailBounds
namespace BstLean.BlueprintLow
open Real Set
theorem lowCentreTail1_3 : exp (-((3864459967/250000000) : ℝ)) ≤ (96764365109/500000000000000000) := by
  apply BstLean.Part269.Tails.exp_negative_sixteen_bound (E := ((2627715903749/1000000000000) : ℝ))
  all_goals norm_num [Finset.sum_range_succ,Nat.factorial]

end BstLean.BlueprintLow
