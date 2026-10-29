import BstLean.Part269TailBounds
namespace BstLean.BlueprintLow
open Real Set
theorem lowCentreTail1_0 : exp (-((3426487313/250000000) : ℝ)) ≤ (557894237989/500000000000000000) := by
  apply BstLean.Part269.Tails.exp_negative_sixteen_bound (E := ((294398874967/125000000000) : ℝ))
  all_goals norm_num [Finset.sum_range_succ,Nat.factorial]

end BstLean.BlueprintLow
