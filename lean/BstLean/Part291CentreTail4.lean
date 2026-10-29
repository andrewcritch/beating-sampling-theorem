import BstLean.Part269TailBounds
namespace BstLean.BlueprintLow
open Real Set
theorem lowCentreTail1_4 : exp (-((17211830679/1000000000) : ℝ)) ≤ (33496306793/1000000000000000000) := by
  apply BstLean.Part269.Tails.exp_negative_sixteen_bound (E := ((36652002301/12500000000) : ℝ))
  all_goals norm_num [Finset.sum_range_succ,Nat.factorial]

end BstLean.BlueprintLow
