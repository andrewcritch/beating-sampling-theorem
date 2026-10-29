import BstLean.Part269TailBounds
namespace BstLean.BlueprintLow
open Real Set
theorem lowCentreTail1_1 : exp (-((14143704813/1000000000) : ℝ)) ≤ (36011155079/50000000000000000) := by
  apply BstLean.Part269.Tails.exp_negative_sixteen_bound (E := ((2420517960671/1000000000000) : ℝ))
  all_goals norm_num [Finset.sum_range_succ,Nat.factorial]

end BstLean.BlueprintLow
