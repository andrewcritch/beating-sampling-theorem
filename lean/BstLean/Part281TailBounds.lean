import BstLean.Part269TailBounds
namespace BstLean.Part281.Tails
open Real
theorem exp_minus_16_3_upper : exp (-16.3 : ℝ) ≤ 8.3369E-8 := by
  apply BstLean.Part269.Tails.exp_negative_sixteen_bound (E := (2.769730433335 : ℝ))
  all_goals norm_num [Finset.sum_range_succ, Nat.factorial]

theorem exp_minus_16_4_upper : exp (-16.4 : ℝ) ≤ 7.5435E-8 := by
  apply BstLean.Part269.Tails.exp_negative_sixteen_bound (E := (2.787095457519 : ℝ))
  all_goals norm_num [Finset.sum_range_succ, Nat.factorial]

theorem exp_minus_16_5_upper : exp (-16.5 : ℝ) ≤ 6.8257E-8 := by
  apply BstLean.Part269.Tails.exp_negative_sixteen_bound (E := (2.804569352958 : ℝ))
  all_goals norm_num [Finset.sum_range_succ, Nat.factorial]

theorem exp_minus_16_6_upper : exp (-16.6 : ℝ) ≤ 6.1761E-8 := by
  apply BstLean.Part269.Tails.exp_negative_sixteen_bound (E := (2.822152802228 : ℝ))
  all_goals norm_num [Finset.sum_range_succ, Nat.factorial]

theorem exp_minus_16_7_upper : exp (-16.7 : ℝ) ≤ 5.5884E-8 := by
  apply BstLean.Part269.Tails.exp_negative_sixteen_bound (E := (2.839846492184 : ℝ))
  all_goals norm_num [Finset.sum_range_succ, Nat.factorial]

theorem exp_minus_16_8_upper : exp (-16.8 : ℝ) ≤ 5.0566E-8 := by
  apply BstLean.Part269.Tails.exp_negative_sixteen_bound (E := (2.857651113986 : ℝ))
  all_goals norm_num [Finset.sum_range_succ, Nat.factorial]

theorem exp_minus_16_9_upper : exp (-16.9 : ℝ) ≤ 4.5754E-8 := by
  apply BstLean.Part269.Tails.exp_negative_sixteen_bound (E := (2.875567363129 : ℝ))
  all_goals norm_num [Finset.sum_range_succ, Nat.factorial]

end BstLean.Part281.Tails
