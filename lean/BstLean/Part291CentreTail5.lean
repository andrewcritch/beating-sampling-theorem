import BstLean.Part269TailBounds
namespace BstLean.BlueprintLow
open Real Set
theorem lowCentreTail1_5 : exp (-((9483806891/500000000) : ℝ)) ≤ (2893610299/500000000000000000) := by
  apply BstLean.Part269.Tails.exp_negative_sixteen_bound (E := ((3272243567681/1000000000000) : ℝ))
  all_goals norm_num [Finset.sum_range_succ,Nat.factorial]

end BstLean.BlueprintLow
