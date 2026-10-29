import BstLean.Part292Count1

/-! Exact singleton-free counts, by small recurrence steps. -/
namespace BstLean.Part292
open BstLean.Part239

theorem count_16_0 : noSingleton 16 0 = 0 := by
  exact noSingleton_zero_column 15

theorem count_16_1 : noSingleton 16 1 = 1 := by
  rw [noSingleton_recurrence 14 0]
  rw [count_15_1]
  rw [count_14_0]
  all_goals norm_num

theorem count_16_2 : noSingleton 16 2 = 32751 := by
  rw [noSingleton_recurrence 14 1]
  rw [count_15_2]
  rw [count_14_1]
  all_goals norm_num

theorem count_16_3 : noSingleton 16 3 = 6879678 := by
  rw [noSingleton_recurrence 14 2]
  rw [count_15_3]
  rw [count_14_2]
  all_goals norm_num

theorem count_16_4 : noSingleton 16 4 = 134779645 := by
  rw [noSingleton_recurrence 14 3]
  rw [count_15_4]
  rw [count_14_3]
  all_goals norm_num

theorem count_16_5 : noSingleton 16 5 = 510880370 := by
  rw [noSingleton_recurrence 14 4]
  rw [count_15_5]
  rw [count_14_4]
  all_goals norm_num

theorem count_16_6 : noSingleton 16 6 = 466876410 := by
  rw [noSingleton_recurrence 14 5]
  rw [count_15_6]
  rw [count_14_5]
  all_goals norm_num

theorem count_16_7 : noSingleton 16 7 = 94594500 := by
  rw [noSingleton_recurrence 14 6]
  rw [count_15_7]
  rw [count_14_6]
  all_goals norm_num

theorem count_16_8 : noSingleton 16 8 = 2027025 := by
  rw [noSingleton_recurrence 14 7]
  rw [noSingleton_support 15 8 (by omega)]
  rw [count_14_7]
  all_goals norm_num

theorem count_17_0 : noSingleton 17 0 = 0 := by
  exact noSingleton_zero_column 16

theorem count_17_1 : noSingleton 17 1 = 1 := by
  rw [noSingleton_recurrence 15 0]
  rw [count_16_1]
  rw [count_15_0]
  all_goals norm_num

theorem count_17_2 : noSingleton 17 2 = 65518 := by
  rw [noSingleton_recurrence 15 1]
  rw [count_16_2]
  rw [count_15_1]
  all_goals norm_num

theorem count_17_3 : noSingleton 17 3 = 20900922 := by
  rw [noSingleton_recurrence 15 2]
  rw [count_16_3]
  rw [count_15_2]
  all_goals norm_num

theorem count_17_4 : noSingleton 17 4 = 575156036 := by
  rw [noSingleton_recurrence 15 3]
  rw [count_16_4]
  rw [count_15_3]
  all_goals norm_num

theorem count_17_5 : noSingleton 17 5 = 3049616570 := by
  rw [noSingleton_recurrence 15 4]
  rw [count_16_5]
  rw [count_15_4]
  all_goals norm_num

theorem count_17_6 : noSingleton 17 6 = 4104160060 := by
  rw [noSingleton_recurrence 15 5]
  rw [count_16_6]
  rw [count_15_5]
  all_goals norm_num

theorem count_17_7 : noSingleton 17 7 = 1422280860 := by
  rw [noSingleton_recurrence 15 6]
  rw [count_16_7]
  rw [count_15_6]
  all_goals norm_num

theorem count_17_8 : noSingleton 17 8 = 91891800 := by
  rw [noSingleton_recurrence 15 7]
  rw [count_16_8]
  rw [count_15_7]
  all_goals norm_num

theorem count_18_0 : noSingleton 18 0 = 0 := by
  exact noSingleton_zero_column 17

theorem count_18_1 : noSingleton 18 1 = 1 := by
  rw [noSingleton_recurrence 16 0]
  rw [count_17_1]
  rw [count_16_0]
  all_goals norm_num

theorem count_18_2 : noSingleton 18 2 = 131053 := by
  rw [noSingleton_recurrence 16 1]
  rw [count_17_2]
  rw [count_16_1]
  all_goals norm_num

theorem count_18_3 : noSingleton 18 3 = 63259533 := by
  rw [noSingleton_recurrence 16 2]
  rw [count_17_3]
  rw [count_16_2]
  all_goals norm_num

theorem count_18_4 : noSingleton 18 4 = 2417578670 := by
  rw [noSingleton_recurrence 16 3]
  rw [count_17_4]
  rw [count_16_3]
  all_goals norm_num

theorem count_18_5 : noSingleton 18 5 = 17539336815 := by
  rw [noSingleton_recurrence 16 4]
  rw [count_17_5]
  rw [count_16_4]
  all_goals norm_num

theorem count_18_6 : noSingleton 18 6 = 33309926650 := by
  rw [noSingleton_recurrence 16 5]
  rw [count_17_6]
  rw [count_16_5]
  all_goals norm_num

theorem count_18_7 : noSingleton 18 7 = 17892864990 := by
  rw [noSingleton_recurrence 16 6]
  rw [count_17_7]
  rw [count_16_6]
  all_goals norm_num

theorem count_18_8 : noSingleton 18 8 = 2343240900 := by
  rw [noSingleton_recurrence 16 7]
  rw [count_17_8]
  rw [count_16_7]
  all_goals norm_num

theorem count_18_9 : noSingleton 18 9 = 34459425 := by
  rw [noSingleton_recurrence 16 8]
  rw [noSingleton_support 17 9 (by omega)]
  rw [count_16_8]
  all_goals norm_num

theorem count_19_0 : noSingleton 19 0 = 0 := by
  exact noSingleton_zero_column 18

theorem count_19_1 : noSingleton 19 1 = 1 := by
  rw [noSingleton_recurrence 17 0]
  rw [count_18_1]
  rw [count_17_0]
  all_goals norm_num

theorem count_19_2 : noSingleton 19 2 = 262124 := by
  rw [noSingleton_recurrence 17 1]
  rw [count_18_2]
  rw [count_17_1]
  all_goals norm_num

theorem count_19_3 : noSingleton 19 3 = 190957923 := by
  rw [noSingleton_recurrence 17 2]
  rw [count_18_3]
  rw [count_17_2]
  all_goals norm_num

theorem count_19_4 : noSingleton 19 4 = 10046531276 := by
  rw [noSingleton_recurrence 17 3]
  rw [count_18_4]
  rw [count_17_3]
  all_goals norm_num

theorem count_19_5 : noSingleton 19 5 = 98049492723 := by
  rw [noSingleton_recurrence 17 4]
  rw [count_18_5]
  rw [count_17_4]
  all_goals norm_num

theorem count_19_6 : noSingleton 19 6 = 254752658160 := by
  rw [noSingleton_recurrence 17 5]
  rw [count_18_6]
  rw [count_17_5]
  all_goals norm_num

theorem count_19_7 : noSingleton 19 7 = 199124936010 := by
  rw [noSingleton_recurrence 17 6]
  rw [count_18_7]
  rw [count_17_6]
  all_goals norm_num

theorem count_19_8 : noSingleton 19 8 = 44346982680 := by
  rw [noSingleton_recurrence 17 7]
  rw [count_18_8]
  rw [count_17_7]
  all_goals norm_num

theorem count_19_9 : noSingleton 19 9 = 1964187225 := by
  rw [noSingleton_recurrence 17 8]
  rw [count_18_9]
  rw [count_17_8]
  all_goals norm_num

theorem count_20_0 : noSingleton 20 0 = 0 := by
  exact noSingleton_zero_column 19

theorem count_20_1 : noSingleton 20 1 = 1 := by
  rw [noSingleton_recurrence 18 0]
  rw [count_19_1]
  rw [count_18_0]
  all_goals norm_num

theorem count_20_2 : noSingleton 20 2 = 524267 := by
  rw [noSingleton_recurrence 18 1]
  rw [count_19_2]
  rw [count_18_1]
  all_goals norm_num

theorem count_20_3 : noSingleton 20 3 = 575363776 := by
  rw [noSingleton_recurrence 18 2]
  rw [count_19_3]
  rw [count_18_2]
  all_goals norm_num

theorem count_20_4 : noSingleton 20 4 = 41388056231 := by
  rw [noSingleton_recurrence 18 3]
  rw [count_19_4]
  rw [count_18_3]
  all_goals norm_num

theorem count_20_5 : noSingleton 20 5 = 536181458345 := by
  rw [noSingleton_recurrence 18 4]
  rw [count_19_5]
  rw [count_18_4]
  all_goals norm_num

theorem count_20_6 : noSingleton 20 6 = 1861763348445 := by
  rw [noSingleton_recurrence 18 5]
  rw [count_19_6]
  rw [count_18_5]
  all_goals norm_num

theorem count_20_7 : noSingleton 20 7 = 2026763158420 := by
  rw [noSingleton_recurrence 18 6]
  rw [count_19_7]
  rw [count_18_6]
  all_goals norm_num

theorem count_20_8 : noSingleton 20 8 = 694740296250 := by
  rw [noSingleton_recurrence 18 7]
  rw [count_19_8]
  rw [count_18_7]
  all_goals norm_num

theorem count_20_9 : noSingleton 20 9 = 62199262125 := by
  rw [noSingleton_recurrence 18 8]
  rw [count_19_9]
  rw [count_18_8]
  all_goals norm_num

theorem count_20_10 : noSingleton 20 10 = 654729075 := by
  rw [noSingleton_recurrence 18 9]
  rw [noSingleton_support 19 10 (by omega)]
  rw [count_18_9]
  all_goals norm_num

theorem count_21_0 : noSingleton 21 0 = 0 := by
  exact noSingleton_zero_column 20

theorem count_21_1 : noSingleton 21 1 = 1 := by
  rw [noSingleton_recurrence 19 0]
  rw [count_20_1]
  rw [count_19_0]
  all_goals norm_num

theorem count_21_2 : noSingleton 21 2 = 1048554 := by
  rw [noSingleton_recurrence 19 1]
  rw [count_20_2]
  rw [count_19_1]
  all_goals norm_num

theorem count_21_3 : noSingleton 21 3 = 1731333808 := by
  rw [noSingleton_recurrence 19 2]
  rw [count_20_3]
  rw [count_19_2]
  all_goals norm_num

theorem count_21_4 : noSingleton 21 4 = 169371383384 := by
  rw [noSingleton_recurrence 19 3]
  rw [count_20_4]
  rw [count_19_3]
  all_goals norm_num

theorem count_21_5 : noSingleton 21 5 = 2881837917245 := by
  rw [noSingleton_recurrence 19 4]
  rw [count_20_5]
  rw [count_19_4]
  all_goals norm_num

theorem count_21_6 : noSingleton 21 6 = 13131569945130 := by
  rw [noSingleton_recurrence 19 5]
  rw [count_20_6]
  rw [count_19_5]
  all_goals norm_num

theorem count_21_7 : noSingleton 21 7 = 19282395272140 := by
  rw [noSingleton_recurrence 19 6]
  rw [count_20_7]
  rw [count_19_6]
  all_goals norm_num

theorem count_21_8 : noSingleton 21 8 = 9540421090200 := by
  rw [noSingleton_recurrence 19 7]
  rw [count_20_8]
  rw [count_19_7]
  all_goals norm_num

theorem count_21_9 : noSingleton 21 9 = 1446733012725 := by
  rw [noSingleton_recurrence 19 8]
  rw [count_20_9]
  rw [count_19_8]
  all_goals norm_num

theorem count_21_10 : noSingleton 21 10 = 45831035250 := by
  rw [noSingleton_recurrence 19 9]
  rw [count_20_10]
  rw [count_19_9]
  all_goals norm_num

theorem count_22_0 : noSingleton 22 0 = 0 := by
  exact noSingleton_zero_column 21

theorem count_22_1 : noSingleton 22 1 = 1 := by
  rw [noSingleton_recurrence 20 0]
  rw [count_21_1]
  rw [count_20_0]
  all_goals norm_num

theorem count_22_2 : noSingleton 22 2 = 2097129 := by
  rw [noSingleton_recurrence 20 1]
  rw [count_21_2]
  rw [count_20_1]
  all_goals norm_num

theorem count_22_3 : noSingleton 22 3 = 5205011031 := by
  rw [noSingleton_recurrence 20 2]
  rw [count_21_3]
  rw [count_20_2]
  all_goals norm_num

theorem count_22_4 : noSingleton 22 4 = 689568172832 := by
  rw [noSingleton_recurrence 20 3]
  rw [count_21_4]
  rw [count_20_3]
  all_goals norm_num

theorem count_22_5 : noSingleton 22 5 = 15278338767076 := by
  rw [noSingleton_recurrence 20 4]
  rw [count_21_5]
  rw [count_20_4]
  all_goals norm_num

theorem count_22_6 : noSingleton 22 6 = 90049230296025 := by
  rw [noSingleton_recurrence 20 5]
  rw [count_21_6]
  rw [count_20_5]
  all_goals norm_num

theorem count_22_7 : noSingleton 22 7 = 174073797222325 := by
  rw [noSingleton_recurrence 20 6]
  rw [count_21_7]
  rw [count_20_6]
  all_goals norm_num

theorem count_22_8 : noSingleton 22 8 = 118885395048420 := by
  rw [noSingleton_recurrence 20 7]
  rw [count_21_8]
  rw [count_20_7]
  all_goals norm_num

theorem count_22_9 : noSingleton 22 9 = 27610143335775 := by
  rw [noSingleton_recurrence 20 8]
  rw [count_21_9]
  rw [count_20_8]
  all_goals norm_num

theorem count_22_10 : noSingleton 22 10 = 1764494857125 := by
  rw [noSingleton_recurrence 20 9]
  rw [count_21_10]
  rw [count_20_9]
  all_goals norm_num

theorem count_22_11 : noSingleton 22 11 = 13749310575 := by
  rw [noSingleton_recurrence 20 10]
  rw [noSingleton_support 21 11 (by omega)]
  rw [count_20_10]
  all_goals norm_num

theorem count_23_0 : noSingleton 23 0 = 0 := by
  exact noSingleton_zero_column 22

theorem count_23_1 : noSingleton 23 1 = 1 := by
  rw [noSingleton_recurrence 21 0]
  rw [count_22_1]
  rw [count_21_0]
  all_goals norm_num

theorem count_23_2 : noSingleton 23 2 = 4194280 := by
  rw [noSingleton_recurrence 21 1]
  rw [count_22_2]
  rw [count_21_1]
  all_goals norm_num

theorem count_23_3 : noSingleton 23 3 = 15638101281 := by
  rw [noSingleton_recurrence 21 2]
  rw [count_22_3]
  rw [count_21_2]
  all_goals norm_num

theorem count_23_4 : noSingleton 23 4 = 2796362035104 := by
  rw [noSingleton_recurrence 21 3]
  rw [count_22_4]
  rw [count_21_3]
  all_goals norm_num

theorem count_23_5 : noSingleton 23 5 = 80117864269828 := by
  rw [noSingleton_recurrence 21 4]
  rw [count_22_5]
  rw [count_21_4]
  all_goals norm_num

theorem count_23_6 : noSingleton 23 6 = 603695815955540 := by
  rw [noSingleton_recurrence 21 5]
  rw [count_22_6]
  rw [count_21_5]
  all_goals norm_num

theorem count_23_7 : noSingleton 23 7 = 1507411119349135 := by
  rw [noSingleton_recurrence 21 6]
  rw [count_22_7]
  rw [count_21_6]
  all_goals norm_num

theorem count_23_8 : noSingleton 23 8 = 1375295856374440 := by
  rw [noSingleton_recurrence 21 7]
  rw [count_22_8]
  rw [count_21_7]
  all_goals norm_num

theorem count_23_9 : noSingleton 23 9 = 458380554006375 := by
  rw [noSingleton_recurrence 21 8]
  rw [count_22_9]
  rw [count_21_8]
  all_goals norm_num

theorem count_23_10 : noSingleton 23 10 = 49473074851200 := by
  rw [noSingleton_recurrence 21 9]
  rw [count_22_10]
  rw [count_21_9]
  all_goals norm_num

theorem count_23_11 : noSingleton 23 11 = 1159525191825 := by
  rw [noSingleton_recurrence 21 10]
  rw [count_22_11]
  rw [count_21_10]
  all_goals norm_num

end BstLean.Part292
