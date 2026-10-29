import BstLean.Part239Correction

/-! Exact singleton-free counts, by small recurrence steps. -/
namespace BstLean.Part292
open BstLean.Part239

theorem count_0_0 : noSingleton 0 0 = 1 := by
  norm_num [noSingleton]

theorem count_1_0 : noSingleton 1 0 = 0 := by
  norm_num [noSingleton]

theorem count_2_0 : noSingleton 2 0 = 0 := by
  exact noSingleton_zero_column 1

theorem count_2_1 : noSingleton 2 1 = 1 := by
  rw [noSingleton_recurrence 0 0]
  rw [noSingleton_support 1 1 (by omega)]
  rw [count_0_0]
  all_goals norm_num

theorem count_3_0 : noSingleton 3 0 = 0 := by
  exact noSingleton_zero_column 2

theorem count_3_1 : noSingleton 3 1 = 1 := by
  rw [noSingleton_recurrence 1 0]
  rw [count_2_1]
  rw [count_1_0]
  all_goals norm_num

theorem count_4_0 : noSingleton 4 0 = 0 := by
  exact noSingleton_zero_column 3

theorem count_4_1 : noSingleton 4 1 = 1 := by
  rw [noSingleton_recurrence 2 0]
  rw [count_3_1]
  rw [count_2_0]
  all_goals norm_num

theorem count_4_2 : noSingleton 4 2 = 3 := by
  rw [noSingleton_recurrence 2 1]
  rw [noSingleton_support 3 2 (by omega)]
  rw [count_2_1]
  all_goals norm_num

theorem count_5_0 : noSingleton 5 0 = 0 := by
  exact noSingleton_zero_column 4

theorem count_5_1 : noSingleton 5 1 = 1 := by
  rw [noSingleton_recurrence 3 0]
  rw [count_4_1]
  rw [count_3_0]
  all_goals norm_num

theorem count_5_2 : noSingleton 5 2 = 10 := by
  rw [noSingleton_recurrence 3 1]
  rw [count_4_2]
  rw [count_3_1]
  all_goals norm_num

theorem count_6_0 : noSingleton 6 0 = 0 := by
  exact noSingleton_zero_column 5

theorem count_6_1 : noSingleton 6 1 = 1 := by
  rw [noSingleton_recurrence 4 0]
  rw [count_5_1]
  rw [count_4_0]
  all_goals norm_num

theorem count_6_2 : noSingleton 6 2 = 25 := by
  rw [noSingleton_recurrence 4 1]
  rw [count_5_2]
  rw [count_4_1]
  all_goals norm_num

theorem count_6_3 : noSingleton 6 3 = 15 := by
  rw [noSingleton_recurrence 4 2]
  rw [noSingleton_support 5 3 (by omega)]
  rw [count_4_2]
  all_goals norm_num

theorem count_7_0 : noSingleton 7 0 = 0 := by
  exact noSingleton_zero_column 6

theorem count_7_1 : noSingleton 7 1 = 1 := by
  rw [noSingleton_recurrence 5 0]
  rw [count_6_1]
  rw [count_5_0]
  all_goals norm_num

theorem count_7_2 : noSingleton 7 2 = 56 := by
  rw [noSingleton_recurrence 5 1]
  rw [count_6_2]
  rw [count_5_1]
  all_goals norm_num

theorem count_7_3 : noSingleton 7 3 = 105 := by
  rw [noSingleton_recurrence 5 2]
  rw [count_6_3]
  rw [count_5_2]
  all_goals norm_num

end BstLean.Part292
