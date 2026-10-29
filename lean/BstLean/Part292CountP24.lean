import BstLean.Part292Count2

/-! Fixed moment order 24; no dimension data. -/
namespace BstLean.Part292
open BstLean.Part239

theorem count_24_0 : noSingleton 24 0 = 0 := by
  exact noSingleton_zero_column 23

theorem count_24_1 : noSingleton 24 1 = 1 := by
  rewrite [noSingleton_recurrence 22 0]
  rewrite [count_23_1]
  rewrite [count_22_0]
  norm_num

theorem count_24_2 : noSingleton 24 2 = 8388583 := by
  rewrite [noSingleton_recurrence 22 1]
  rewrite [count_23_2]
  rewrite [count_22_1]
  norm_num

theorem count_24_3 : noSingleton 24 3 = 46962537810 := by
  rewrite [noSingleton_recurrence 22 2]
  rewrite [count_23_3]
  rewrite [count_22_2]
  norm_num

theorem count_24_4 : noSingleton 24 4 = 11305163394129 := by
  rewrite [noSingleton_recurrence 22 3]
  rewrite [count_23_4]
  rewrite [count_22_3]
  norm_num

theorem count_24_5 : noSingleton 24 5 = 416449389324276 := by
  rewrite [noSingleton_recurrence 22 4]
  rewrite [count_23_5]
  rewrite [count_22_4]
  norm_num

theorem count_24_6 : noSingleton 24 6 = 3973576687375988 := by
  rewrite [noSingleton_recurrence 22 5]
  rewrite [count_23_6]
  rewrite [count_22_5]
  norm_num

theorem count_24_7 : noSingleton 24 7 = 12623010132252520 := by
  rewrite [noSingleton_recurrence 22 6]
  rewrite [count_23_7]
  rewrite [count_22_6]
  norm_num

theorem count_24_8 : noSingleton 24 8 = 15006064187108995 := by
  rewrite [noSingleton_recurrence 22 7]
  rewrite [count_23_8]
  rewrite [count_22_7]
  norm_num

theorem count_24_9 : noSingleton 24 9 = 6859789072171035 := by
  rewrite [noSingleton_recurrence 22 8]
  rewrite [count_23_9]
  rewrite [count_22_8]
  norm_num

theorem count_24_10 : noSingleton 24 10 = 1129764045234825 := by
  rewrite [noSingleton_recurrence 22 9]
  rewrite [count_23_10]
  rewrite [count_22_9]
  norm_num

theorem count_24_11 : noSingleton 24 11 = 53338158823950 := by
  rewrite [noSingleton_recurrence 22 10]
  rewrite [count_23_11]
  rewrite [count_22_10]
  norm_num

theorem count_24_12 : noSingleton 24 12 = 316234143225 := by
  rewrite [noSingleton_recurrence 22 11]
  rewrite [noSingleton_support 23 12 (by omega)]
  rewrite [count_22_11]
  norm_num

end BstLean.Part292
