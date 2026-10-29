import BstLean.Part292CountStep

/-! Fixed moment order 25; explicit recurrence indices. -/
namespace BstLean.Part292
open BstLean.Part239

theorem count_25_0 : noSingleton 25 0 = 0 := by
  exact count_zero_checked 25 24 (by norm_num)

theorem count_25_1 : noSingleton 25 1 = 1 := by
  exact count_step_checked 25 24 23 1 0 1 0 1
    (by norm_num) (by norm_num) (by norm_num) count_24_1 count_23_0 (by norm_num)

theorem count_25_2 : noSingleton 25 2 = 16777190 := by
  exact count_step_checked 25 24 23 2 1 8388583 1 16777190
    (by norm_num) (by norm_num) (by norm_num) count_24_2 count_23_1 (by norm_num)

theorem count_25_3 : noSingleton 25 3 = 140988276150 := by
  exact count_step_checked 25 24 23 3 2 46962537810 4194280 140988276150
    (by norm_num) (by norm_num) (by norm_num) count_24_3 count_23_2 (by norm_num)

theorem count_25_4 : noSingleton 25 4 = 45595968007260 := by
  exact count_step_checked 25 24 23 4 3 11305163394129 15638101281 45595968007260
    (by norm_num) (by norm_num) (by norm_num) count_24_4 count_23_3 (by norm_num)

theorem count_25_5 : noSingleton 25 5 = 2149359635463876 := by
  exact count_step_checked 25 24 23 5 4 416449389324276 2796362035104 2149359635463876
    (by norm_num) (by norm_num) (by norm_num) count_24_5 count_23_4 (by norm_num)

theorem count_25_6 : noSingleton 25 6 = 25764288866731800 := by
  exact count_step_checked 25 24 23 6 5 3973576687375988 80117864269828 25764288866731800
    (by norm_num) (by norm_num) (by norm_num) count_24_6 count_23_5 (by norm_num)

theorem count_25_7 : noSingleton 25 7 = 102849770508700600 := by
  exact count_step_checked 25 24 23 7 6 12623010132252520 603695815955540 102849770508700600
    (by norm_num) (by norm_num) (by norm_num) count_24_7 count_23_6 (by norm_num)

theorem count_25_8 : noSingleton 25 8 = 156226380361251200 := by
  exact count_step_checked 25 24 23 8 7 15006064187108995 1507411119349135 156226380361251200
    (by norm_num) (by norm_num) (by norm_num) count_24_8 count_23_7 (by norm_num)

theorem count_25_9 : noSingleton 25 9 = 94745202202525875 := by
  exact count_step_checked 25 24 23 9 8 6859789072171035 1375295856374440 94745202202525875
    (by norm_num) (by norm_num) (by norm_num) count_24_9 count_23_8 (by norm_num)

theorem count_25_10 : noSingleton 25 10 = 22298773748501250 := by
  exact count_step_checked 25 24 23 10 9 1129764045234825 458380554006375 22298773748501250
    (by norm_num) (by norm_num) (by norm_num) count_24_10 count_23_9 (by norm_num)

theorem count_25_11 : noSingleton 25 11 = 1774073543492250 := by
  exact count_step_checked 25 24 23 11 10 53338158823950 49473074851200 1774073543492250
    (by norm_num) (by norm_num) (by norm_num) count_24_11 count_23_10 (by norm_num)

theorem count_25_12 : noSingleton 25 12 = 31623414322500 := by
  exact count_step_checked 25 24 23 12 11 316234143225 1159525191825 31623414322500
    (by norm_num) (by norm_num) (by norm_num) count_24_12 count_23_11 (by norm_num)

end BstLean.Part292
