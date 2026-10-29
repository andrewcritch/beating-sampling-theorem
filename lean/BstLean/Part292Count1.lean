import BstLean.Part292Count0

/-! Exact singleton-free counts, by small recurrence steps. -/
namespace BstLean.Part292
open BstLean.Part239

theorem count_8_0 : noSingleton 8 0 = 0 := by
  exact noSingleton_zero_column 7

theorem count_8_1 : noSingleton 8 1 = 1 := by
  rw [noSingleton_recurrence 6 0]
  rw [count_7_1]
  rw [count_6_0]
  all_goals norm_num

theorem count_8_2 : noSingleton 8 2 = 119 := by
  rw [noSingleton_recurrence 6 1]
  rw [count_7_2]
  rw [count_6_1]
  all_goals norm_num

theorem count_8_3 : noSingleton 8 3 = 490 := by
  rw [noSingleton_recurrence 6 2]
  rw [count_7_3]
  rw [count_6_2]
  all_goals norm_num

theorem count_8_4 : noSingleton 8 4 = 105 := by
  rw [noSingleton_recurrence 6 3]
  rw [noSingleton_support 7 4 (by omega)]
  rw [count_6_3]
  all_goals norm_num

theorem count_9_0 : noSingleton 9 0 = 0 := by
  exact noSingleton_zero_column 8

theorem count_9_1 : noSingleton 9 1 = 1 := by
  rw [noSingleton_recurrence 7 0]
  rw [count_8_1]
  rw [count_7_0]
  all_goals norm_num

theorem count_9_2 : noSingleton 9 2 = 246 := by
  rw [noSingleton_recurrence 7 1]
  rw [count_8_2]
  rw [count_7_1]
  all_goals norm_num

theorem count_9_3 : noSingleton 9 3 = 1918 := by
  rw [noSingleton_recurrence 7 2]
  rw [count_8_3]
  rw [count_7_2]
  all_goals norm_num

theorem count_9_4 : noSingleton 9 4 = 1260 := by
  rw [noSingleton_recurrence 7 3]
  rw [count_8_4]
  rw [count_7_3]
  all_goals norm_num

theorem count_10_0 : noSingleton 10 0 = 0 := by
  exact noSingleton_zero_column 9

theorem count_10_1 : noSingleton 10 1 = 1 := by
  rw [noSingleton_recurrence 8 0]
  rw [count_9_1]
  rw [count_8_0]
  all_goals norm_num

theorem count_10_2 : noSingleton 10 2 = 501 := by
  rw [noSingleton_recurrence 8 1]
  rw [count_9_2]
  rw [count_8_1]
  all_goals norm_num

theorem count_10_3 : noSingleton 10 3 = 6825 := by
  rw [noSingleton_recurrence 8 2]
  rw [count_9_3]
  rw [count_8_2]
  all_goals norm_num

theorem count_10_4 : noSingleton 10 4 = 9450 := by
  rw [noSingleton_recurrence 8 3]
  rw [count_9_4]
  rw [count_8_3]
  all_goals norm_num

theorem count_10_5 : noSingleton 10 5 = 945 := by
  rw [noSingleton_recurrence 8 4]
  rw [noSingleton_support 9 5 (by omega)]
  rw [count_8_4]
  all_goals norm_num

theorem count_11_0 : noSingleton 11 0 = 0 := by
  exact noSingleton_zero_column 10

theorem count_11_1 : noSingleton 11 1 = 1 := by
  rw [noSingleton_recurrence 9 0]
  rw [count_10_1]
  rw [count_9_0]
  all_goals norm_num

theorem count_11_2 : noSingleton 11 2 = 1012 := by
  rw [noSingleton_recurrence 9 1]
  rw [count_10_2]
  rw [count_9_1]
  all_goals norm_num

theorem count_11_3 : noSingleton 11 3 = 22935 := by
  rw [noSingleton_recurrence 9 2]
  rw [count_10_3]
  rw [count_9_2]
  all_goals norm_num

theorem count_11_4 : noSingleton 11 4 = 56980 := by
  rw [noSingleton_recurrence 9 3]
  rw [count_10_4]
  rw [count_9_3]
  all_goals norm_num

theorem count_11_5 : noSingleton 11 5 = 17325 := by
  rw [noSingleton_recurrence 9 4]
  rw [count_10_5]
  rw [count_9_4]
  all_goals norm_num

theorem count_12_0 : noSingleton 12 0 = 0 := by
  exact noSingleton_zero_column 11

theorem count_12_1 : noSingleton 12 1 = 1 := by
  rw [noSingleton_recurrence 10 0]
  rw [count_11_1]
  rw [count_10_0]
  all_goals norm_num

theorem count_12_2 : noSingleton 12 2 = 2035 := by
  rw [noSingleton_recurrence 10 1]
  rw [count_11_2]
  rw [count_10_1]
  all_goals norm_num

theorem count_12_3 : noSingleton 12 3 = 74316 := by
  rw [noSingleton_recurrence 10 2]
  rw [count_11_3]
  rw [count_10_2]
  all_goals norm_num

theorem count_12_4 : noSingleton 12 4 = 302995 := by
  rw [noSingleton_recurrence 10 3]
  rw [count_11_4]
  rw [count_10_3]
  all_goals norm_num

theorem count_12_5 : noSingleton 12 5 = 190575 := by
  rw [noSingleton_recurrence 10 4]
  rw [count_11_5]
  rw [count_10_4]
  all_goals norm_num

theorem count_12_6 : noSingleton 12 6 = 10395 := by
  rw [noSingleton_recurrence 10 5]
  rw [noSingleton_support 11 6 (by omega)]
  rw [count_10_5]
  all_goals norm_num

theorem count_13_0 : noSingleton 13 0 = 0 := by
  exact noSingleton_zero_column 12

theorem count_13_1 : noSingleton 13 1 = 1 := by
  rw [noSingleton_recurrence 11 0]
  rw [count_12_1]
  rw [count_11_0]
  all_goals norm_num

theorem count_13_2 : noSingleton 13 2 = 4082 := by
  rw [noSingleton_recurrence 11 1]
  rw [count_12_2]
  rw [count_11_1]
  all_goals norm_num

theorem count_13_3 : noSingleton 13 3 = 235092 := by
  rw [noSingleton_recurrence 11 2]
  rw [count_12_3]
  rw [count_11_2]
  all_goals norm_num

theorem count_13_4 : noSingleton 13 4 = 1487200 := by
  rw [noSingleton_recurrence 11 3]
  rw [count_12_4]
  rw [count_11_3]
  all_goals norm_num

theorem count_13_5 : noSingleton 13 5 = 1636635 := by
  rw [noSingleton_recurrence 11 4]
  rw [count_12_5]
  rw [count_11_4]
  all_goals norm_num

theorem count_13_6 : noSingleton 13 6 = 270270 := by
  rw [noSingleton_recurrence 11 5]
  rw [count_12_6]
  rw [count_11_5]
  all_goals norm_num

theorem count_14_0 : noSingleton 14 0 = 0 := by
  exact noSingleton_zero_column 13

theorem count_14_1 : noSingleton 14 1 = 1 := by
  rw [noSingleton_recurrence 12 0]
  rw [count_13_1]
  rw [count_12_0]
  all_goals norm_num

theorem count_14_2 : noSingleton 14 2 = 8177 := by
  rw [noSingleton_recurrence 12 1]
  rw [count_13_2]
  rw [count_12_1]
  all_goals norm_num

theorem count_14_3 : noSingleton 14 3 = 731731 := by
  rw [noSingleton_recurrence 12 2]
  rw [count_13_3]
  rw [count_12_2]
  all_goals norm_num

theorem count_14_4 : noSingleton 14 4 = 6914908 := by
  rw [noSingleton_recurrence 12 3]
  rw [count_13_4]
  rw [count_12_3]
  all_goals norm_num

theorem count_14_5 : noSingleton 14 5 = 12122110 := by
  rw [noSingleton_recurrence 12 4]
  rw [count_13_5]
  rw [count_12_4]
  all_goals norm_num

theorem count_14_6 : noSingleton 14 6 = 4099095 := by
  rw [noSingleton_recurrence 12 5]
  rw [count_13_6]
  rw [count_12_5]
  all_goals norm_num

theorem count_14_7 : noSingleton 14 7 = 135135 := by
  rw [noSingleton_recurrence 12 6]
  rw [noSingleton_support 13 7 (by omega)]
  rw [count_12_6]
  all_goals norm_num

theorem count_15_0 : noSingleton 15 0 = 0 := by
  exact noSingleton_zero_column 14

theorem count_15_1 : noSingleton 15 1 = 1 := by
  rw [noSingleton_recurrence 13 0]
  rw [count_14_1]
  rw [count_13_0]
  all_goals norm_num

theorem count_15_2 : noSingleton 15 2 = 16368 := by
  rw [noSingleton_recurrence 13 1]
  rw [count_14_2]
  rw [count_13_1]
  all_goals norm_num

theorem count_15_3 : noSingleton 15 3 = 2252341 := by
  rw [noSingleton_recurrence 13 2]
  rw [count_14_3]
  rw [count_13_2]
  all_goals norm_num

theorem count_15_4 : noSingleton 15 4 = 30950920 := by
  rw [noSingleton_recurrence 13 3]
  rw [count_14_4]
  rw [count_13_3]
  all_goals norm_num

theorem count_15_5 : noSingleton 15 5 = 81431350 := by
  rw [noSingleton_recurrence 13 4]
  rw [count_14_5]
  rw [count_13_4]
  all_goals norm_num

theorem count_15_6 : noSingleton 15 6 = 47507460 := by
  rw [noSingleton_recurrence 13 5]
  rw [count_14_6]
  rw [count_13_5]
  all_goals norm_num

theorem count_15_7 : noSingleton 15 7 = 4729725 := by
  rw [noSingleton_recurrence 13 6]
  rw [count_14_7]
  rw [count_13_6]
  all_goals norm_num

end BstLean.Part292
