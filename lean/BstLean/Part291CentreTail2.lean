import BstLean.Part269TailBounds
namespace BstLean.BlueprintLow
open Real Set
theorem lowCentreTail1_2 : exp (-((1458160937/100000000) : ℝ)) ≤ (464822899471/1000000000000000000) := by
  apply BstLean.Part269.Tails.exp_negative_sixteen_bound (E := ((2487680089773/1000000000000) : ℝ))
  all_goals norm_num [Finset.sum_range_succ,Nat.factorial]

end BstLean.BlueprintLow
