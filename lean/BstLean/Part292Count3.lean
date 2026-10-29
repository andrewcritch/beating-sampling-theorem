import BstLean.Part292CountP25

/-! Fixed moment-order certificates with explicit indices. -/
namespace BstLean.Part292
open BstLean.Part239

theorem count_26_0 : noSingleton 26 0 = 0 := by
  exact count_zero_checked 26 25 (by norm_num)

theorem count_26_1 : noSingleton 26 1 = 1 := by
  exact count_step_checked 26 25 24 1 0 1 0 1
    (by norm_num) (by norm_num) (by norm_num) count_25_1 count_24_0 (by norm_num)

theorem count_26_2 : noSingleton 26 2 = 33554405 := by
  exact count_step_checked 26 25 24 2 1 16777190 1 33554405
    (by norm_num) (by norm_num) (by norm_num) count_25_2 count_24_1 (by norm_num)

theorem count_26_3 : noSingleton 26 3 = 423174543025 := by
  exact count_step_checked 26 25 24 3 2 140988276150 8388583 423174543025
    (by norm_num) (by norm_num) (by norm_num) count_25_3 count_24_2 (by norm_num)

theorem count_26_4 : noSingleton 26 4 = 183557935474290 := by
  exact count_step_checked 26 25 24 4 3 45595968007260 46962537810 183557935474290
    (by norm_num) (by norm_num) (by norm_num) count_25_4 count_24_3 (by norm_num)

theorem count_26_5 : noSingleton 26 5 = 11029427262172605 := by
  exact count_step_checked 26 25 24 5 4 2149359635463876 11305163394129 11029427262172605
    (by norm_num) (by norm_num) (by norm_num) count_25_5 count_24_4 (by norm_num)

theorem count_26_6 : noSingleton 26 6 = 164996967933497700 := by
  exact count_step_checked 26 25 24 6 5 25764288866731800 416449389324276 164996967933497700
    (by norm_num) (by norm_num) (by norm_num) count_25_6 count_24_5 (by norm_num)

theorem count_26_7 : noSingleton 26 7 = 819287810745303900 := by
  exact count_step_checked 26 25 24 7 6 102849770508700600 3973576687375988 819287810745303900
    (by norm_num) (by norm_num) (by norm_num) count_25_7 count_24_6 (by norm_num)

theorem count_26_8 : noSingleton 26 8 = 1565386296196322600 := by
  exact count_step_checked 26 25 24 8 7 156226380361251200 12623010132252520 1565386296196322600
    (by norm_num) (by norm_num) (by norm_num) count_25_8 count_24_7 (by norm_num)

theorem count_26_9 : noSingleton 26 9 = 1227858424500457750 := by
  exact count_step_checked 26 25 24 9 8 94745202202525875 15006064187108995 1227858424500457750
    (by norm_num) (by norm_num) (by norm_num) count_25_9 count_24_8 (by norm_num)

theorem count_26_10 : noSingleton 26 10 = 394482464289288375 := by
  exact count_step_checked 26 25 24 10 9 22298773748501250 6859789072171035 394482464289288375
    (by norm_num) (by norm_num) (by norm_num) count_25_10 count_24_9 (by norm_num)

theorem count_26_11 : noSingleton 26 11 = 47758910109285375 := by
  exact count_step_checked 26 25 24 11 10 1774073543492250 1129764045234825 47758910109285375
    (by norm_num) (by norm_num) (by norm_num) count_25_11 count_24_10 (by norm_num)

theorem count_26_12 : noSingleton 26 12 = 1712934942468750 := by
  exact count_step_checked 26 25 24 12 11 31623414322500 53338158823950 1712934942468750
    (by norm_num) (by norm_num) (by norm_num) count_25_12 count_24_11 (by norm_num)

theorem count_26_13 : noSingleton 26 13 = 7905853580625 := by
  exact count_step_checked 26 25 24 13 12 0 316234143225 7905853580625
    (by norm_num) (by norm_num) (by norm_num) (noSingleton_support 25 13 (by omega)) count_24_12 (by norm_num)

theorem count_27_0 : noSingleton 27 0 = 0 := by
  exact count_zero_checked 27 26 (by norm_num)

theorem count_27_1 : noSingleton 27 1 = 1 := by
  exact count_step_checked 27 26 25 1 0 1 0 1
    (by norm_num) (by norm_num) (by norm_num) count_26_1 count_25_0 (by norm_num)

theorem count_27_2 : noSingleton 27 2 = 67108836 := by
  exact count_step_checked 27 26 25 2 1 33554405 1 67108836
    (by norm_num) (by norm_num) (by norm_num) count_26_2 count_25_1 (by norm_num)

theorem count_27_3 : noSingleton 27 3 = 1269959836015 := by
  exact count_step_checked 27 26 25 3 2 423174543025 16777190 1269959836015
    (by norm_num) (by norm_num) (by norm_num) count_26_3 count_25_2 (by norm_num)

theorem count_27_4 : noSingleton 27 4 = 737897437077060 := by
  exact count_step_checked 27 26 25 4 3 183557935474290 140988276150 737897437077060
    (by norm_num) (by norm_num) (by norm_num) count_26_4 count_25_3 (by norm_num)

theorem count_27_5 : noSingleton 27 5 = 56332631479051785 := by
  exact count_step_checked 27 26 25 5 4 11029427262172605 45595968007260 56332631479051785
    (by norm_num) (by norm_num) (by norm_num) count_26_5 count_25_4 (by norm_num)

theorem count_27_6 : noSingleton 27 6 = 1045865158123046976 := by
  exact count_step_checked 27 26 25 6 5 164996967933497700 2149359635463876 1045865158123046976
    (by norm_num) (by norm_num) (by norm_num) count_26_6 count_25_5 (by norm_num)

theorem count_27_7 : noSingleton 27 7 = 6404886185752154100 := by
  exact count_step_checked 27 26 25 7 6 819287810745303900 25764288866731800 6404886185752154100
    (by norm_num) (by norm_num) (by norm_num) count_26_7 count_25_6 (by norm_num)

theorem count_27_8 : noSingleton 27 8 = 15197184402796796400 := by
  exact count_step_checked 27 26 25 8 7 1565386296196322600 102849770508700600 15197184402796796400
    (by norm_num) (by norm_num) (by norm_num) count_26_8 count_25_7 (by norm_num)

theorem count_27_9 : noSingleton 27 9 = 15112611709896650950 := by
  exact count_step_checked 27 26 25 9 8 1227858424500457750 156226380361251200 15112611709896650950
    (by norm_num) (by norm_num) (by norm_num) count_26_9 count_25_8 (by norm_num)

theorem count_27_10 : noSingleton 27 10 = 6408199900158556500 := by
  exact count_step_checked 27 26 25 10 9 394482464289288375 94745202202525875 6408199900158556500
    (by norm_num) (by norm_num) (by norm_num) count_26_10 count_25_9 (by norm_num)

theorem count_27_11 : noSingleton 27 11 = 1105116128663171625 := by
  exact count_step_checked 27 26 25 11 10 47758910109285375 22298773748501250 1105116128663171625
    (by norm_num) (by norm_num) (by norm_num) count_26_11 count_25_10 (by norm_num)

theorem count_27_12 : noSingleton 27 12 = 66681131440423500 := by
  exact count_step_checked 27 26 25 12 11 1712934942468750 1774073543492250 66681131440423500
    (by norm_num) (by norm_num) (by norm_num) count_26_12 count_25_11 (by norm_num)

theorem count_27_13 : noSingleton 27 13 = 924984868933125 := by
  exact count_step_checked 27 26 25 13 12 7905853580625 31623414322500 924984868933125
    (by norm_num) (by norm_num) (by norm_num) count_26_13 count_25_12 (by norm_num)

theorem count_28_0 : noSingleton 28 0 = 0 := by
  exact count_zero_checked 28 27 (by norm_num)

theorem count_28_1 : noSingleton 28 1 = 1 := by
  exact count_step_checked 28 27 26 1 0 1 0 1
    (by norm_num) (by norm_num) (by norm_num) count_27_1 count_26_0 (by norm_num)

theorem count_28_2 : noSingleton 28 2 = 134217699 := by
  exact count_step_checked 28 27 26 2 1 67108836 1 134217699
    (by norm_num) (by norm_num) (by norm_num) count_27_2 count_26_1 (by norm_num)

theorem count_28_3 : noSingleton 28 3 = 3810785476980 := by
  exact count_step_checked 28 27 26 3 2 1269959836015 33554405 3810785476980
    (by norm_num) (by norm_num) (by norm_num) count_27_3 count_26_2 (by norm_num)

theorem count_28_4 : noSingleton 28 4 = 2963015460969915 := by
  exact count_step_checked 28 27 26 4 3 737897437077060 423174543025 2963015460969915
    (by norm_num) (by norm_num) (by norm_num) count_27_4 count_26_3 (by norm_num)

theorem count_28_5 : noSingleton 28 5 = 286619221653064755 := by
  exact count_step_checked 28 27 26 5 4 56332631479051785 183557935474290 286619221653064755
    (by norm_num) (by norm_num) (by norm_num) count_27_5 count_26_4 (by norm_num)

theorem count_28_6 : noSingleton 28 6 = 6572985484816942191 := by
  exact count_step_checked 28 27 26 6 5 1045865158123046976 11029427262172605 6572985484816942191
    (by norm_num) (by norm_num) (by norm_num) count_27_6 count_26_5 (by norm_num)

theorem count_28_7 : noSingleton 28 7 = 49289121434469516600 := by
  exact count_step_checked 28 27 26 7 6 6404886185752154100 164996967933497700 49289121434469516600
    (by norm_num) (by norm_num) (by norm_num) count_27_7 count_26_6 (by norm_num)

theorem count_28_8 : noSingleton 28 8 = 143698246112497576500 := by
  exact count_step_checked 28 27 26 8 7 15197184402796796400 819287810745303900 143698246112497576500
    (by norm_num) (by norm_num) (by norm_num) count_27_8 count_26_7 (by norm_num)

theorem count_28_9 : noSingleton 28 9 = 178278935386370568750 := by
  exact count_step_checked 28 27 26 9 8 15112611709896650950 1565386296196322600 178278935386370568750
    (by norm_num) (by norm_num) (by norm_num) count_27_9 count_26_8 (by norm_num)

theorem count_28_10 : noSingleton 28 10 = 97234176463097924250 := by
  exact count_step_checked 28 27 26 10 9 6408199900158556500 1227858424500457750 97234176463097924250
    (by norm_num) (by norm_num) (by norm_num) count_27_10 count_26_9 (by norm_num)

theorem count_28_11 : noSingleton 28 11 = 22807303951105674000 := by
  exact count_step_checked 28 27 26 11 10 1105116128663171625 394482464289288375 22807303951105674000
    (by norm_num) (by norm_num) (by norm_num) count_27_11 count_26_10 (by norm_num)

theorem count_28_12 : noSingleton 28 12 = 2089664150235787125 := by
  exact count_step_checked 28 27 26 12 11 66681131440423500 47758910109285375 2089664150235787125
    (by norm_num) (by norm_num) (by norm_num) count_27_12 count_26_11 (by norm_num)

theorem count_28_13 : noSingleton 28 13 = 58274046742786875 := by
  exact count_step_checked 28 27 26 13 12 924984868933125 1712934942468750 58274046742786875
    (by norm_num) (by norm_num) (by norm_num) count_27_13 count_26_12 (by norm_num)

theorem count_28_14 : noSingleton 28 14 = 213458046676875 := by
  exact count_step_checked 28 27 26 14 13 0 7905853580625 213458046676875
    (by norm_num) (by norm_num) (by norm_num) (noSingleton_support 27 14 (by omega)) count_26_13 (by norm_num)

theorem count_29_0 : noSingleton 29 0 = 0 := by
  exact count_zero_checked 29 28 (by norm_num)

theorem count_29_1 : noSingleton 29 1 = 1 := by
  exact count_step_checked 29 28 27 1 0 1 0 1
    (by norm_num) (by norm_num) (by norm_num) count_28_1 count_27_0 (by norm_num)

theorem count_29_2 : noSingleton 29 2 = 268435426 := by
  exact count_step_checked 29 28 27 2 1 134217699 1 268435426
    (by norm_num) (by norm_num) (by norm_num) count_28_2 count_27_1 (by norm_num)

theorem count_29_3 : noSingleton 29 3 = 11434235478348 := by
  exact count_step_checked 29 28 27 3 2 3810785476980 67108836 11434235478348
    (by norm_num) (by norm_num) (by norm_num) count_28_3 count_27_2 (by norm_num)

theorem count_29_4 : noSingleton 29 4 = 11887620719288080 := by
  exact count_step_checked 29 28 27 4 3 2963015460969915 1269959836015 11887620719288080
    (by norm_num) (by norm_num) (by norm_num) count_28_4 count_27_3 (by norm_num)

theorem count_29_5 : noSingleton 29 5 = 1453757236503481455 := by
  exact count_step_checked 29 28 27 5 4 286619221653064755 737897437077060 1453757236503481455
    (by norm_num) (by norm_num) (by norm_num) count_28_5 count_27_4 (by norm_num)

theorem count_29_6 : noSingleton 29 6 = 41015226590315103126 := by
  exact count_step_checked 29 28 27 6 5 6572985484816942191 56332631479051785 41015226590315103126
    (by norm_num) (by norm_num) (by norm_num) count_28_6 count_27_5 (by norm_num)

theorem count_29_7 : noSingleton 29 7 = 374308074468731931528 := by
  exact count_step_checked 29 28 27 7 6 49289121434469516600 1045865158123046976 374308074468731931528
    (by norm_num) (by norm_num) (by norm_num) count_28_7 count_27_6 (by norm_num)

theorem count_29_8 : noSingleton 29 8 = 1328922782101040926800 := by
  exact count_step_checked 29 28 27 8 7 143698246112497576500 6404886185752154100 1328922782101040926800
    (by norm_num) (by norm_num) (by norm_num) count_28_8 count_27_7 (by norm_num)

theorem count_29_9 : noSingleton 29 9 = 2030031581755645417950 := by
  exact count_step_checked 29 28 27 9 8 178278935386370568750 15197184402796796400 2030031581755645417950
    (by norm_num) (by norm_num) (by norm_num) count_28_9 count_27_8 (by norm_num)

theorem count_29_10 : noSingleton 29 10 = 1395494892508085469100 := by
  exact count_step_checked 29 28 27 10 9 97234176463097924250 15112611709896650950 1395494892508085469100
    (by norm_num) (by norm_num) (by norm_num) count_28_10 count_27_9 (by norm_num)

theorem count_29_11 : noSingleton 29 11 = 430309940666601996000 := by
  exact count_step_checked 29 28 27 11 10 22807303951105674000 6408199900158556500 430309940666601996000
    (by norm_num) (by norm_num) (by norm_num) count_28_11 count_27_10 (by norm_num)

theorem count_29_12 : noSingleton 29 12 = 56019221405398251000 := by
  exact count_step_checked 29 28 27 12 11 2089664150235787125 1105116128663171625 56019221405398251000
    (by norm_num) (by norm_num) (by norm_num) count_28_12 count_27_11 (by norm_num)

theorem count_29_13 : noSingleton 29 13 = 2624634287988087375 := by
  exact count_step_checked 29 28 27 13 12 58274046742786875 66681131440423500 2624634287988087375
    (by norm_num) (by norm_num) (by norm_num) count_28_13 count_27_12 (by norm_num)

theorem count_29_14 : noSingleton 29 14 = 28887988983603750 := by
  exact count_step_checked 29 28 27 14 13 213458046676875 924984868933125 28887988983603750
    (by norm_num) (by norm_num) (by norm_num) count_28_14 count_27_13 (by norm_num)

theorem count_30_0 : noSingleton 30 0 = 0 := by
  exact count_zero_checked 30 29 (by norm_num)

theorem count_30_1 : noSingleton 30 1 = 1 := by
  exact count_step_checked 30 29 28 1 0 1 0 1
    (by norm_num) (by norm_num) (by norm_num) count_29_1 count_28_0 (by norm_num)

theorem count_30_2 : noSingleton 30 2 = 536870881 := by
  exact count_step_checked 30 29 28 2 1 268435426 1 536870881
    (by norm_num) (by norm_num) (by norm_num) count_29_2 count_28_1 (by norm_num)

theorem count_30_3 : noSingleton 30 3 = 34306598748315 := by
  exact count_step_checked 30 29 28 3 2 11434235478348 134217699 34306598748315
    (by norm_num) (by norm_num) (by norm_num) count_29_3 count_28_2 (by norm_num)

theorem count_30_4 : noSingleton 30 4 = 47660995655984740 := by
  exact count_step_checked 30 29 28 4 3 11887620719288080 3810785476980 47660995655984740
    (by norm_num) (by norm_num) (by norm_num) count_29_4 count_28_3 (by norm_num)

theorem count_30_5 : noSingleton 30 5 = 7354713630885534810 := by
  exact count_step_checked 30 29 28 5 4 1453757236503481455 2963015460969915 7354713630885534810
    (by norm_num) (by norm_num) (by norm_num) count_29_5 count_28_4 (by norm_num)

theorem count_30_6 : noSingleton 30 6 = 254403316969829496651 := by
  exact count_step_checked 30 29 28 6 5 41015226590315103126 286619221653064755 254403316969829496651
    (by norm_num) (by norm_num) (by norm_num) count_29_6 count_28_5 (by norm_num)

theorem count_30_7 : noSingleton 30 7 = 2810773100340814844235 := by
  exact count_step_checked 30 29 28 7 6 374308074468731931528 6572985484816942191 2810773100340814844235
    (by norm_num) (by norm_num) (by norm_num) count_29_7 count_28_6 (by norm_num)

theorem count_30_8 : noSingleton 30 8 = 12060766778407943395800 := by
  exact count_step_checked 30 29 28 8 7 1328922782101040926800 49289121434469516600 12060766778407943395800
    (by norm_num) (by norm_num) (by norm_num) count_29_8 count_28_7 (by norm_num)

theorem count_30_9 : noSingleton 30 9 = 22437533373063238480050 := by
  exact count_step_checked 30 29 28 9 8 2030031581755645417950 143698246112497576500 22437533373063238480050
    (by norm_num) (by norm_num) (by norm_num) count_29_9 count_28_8 (by norm_num)

theorem count_30_10 : noSingleton 30 10 = 19125038051285601184750 := by
  exact count_step_checked 30 29 28 10 9 1395494892508085469100 178278935386370568750 19125038051285601184750
    (by norm_num) (by norm_num) (by norm_num) count_29_10 count_28_9 (by norm_num)

theorem count_30_11 : noSingleton 30 11 = 7553200464762461759250 := by
  exact count_step_checked 30 29 28 11 10 430309940666601996000 97234176463097924250 7553200464762461759250
    (by norm_num) (by norm_num) (by norm_num) count_29_11 count_28_10 (by norm_num)

theorem count_30_12 : noSingleton 30 12 = 1333642471446843558000 := by
  exact count_step_checked 30 29 28 12 11 56019221405398251000 22807303951105674000 1333642471446843558000
    (by norm_num) (by norm_num) (by norm_num) count_29_12 count_28_11 (by norm_num)

theorem count_30_13 : noSingleton 30 13 = 94720506100682962500 := by
  exact count_step_checked 30 29 28 13 12 2624634287988087375 2089664150235787125 94720506100682962500
    (by norm_num) (by norm_num) (by norm_num) count_29_13 count_28_12 (by norm_num)

theorem count_30_14 : noSingleton 30 14 = 2094379201311271875 := by
  exact count_step_checked 30 29 28 14 13 28887988983603750 58274046742786875 2094379201311271875
    (by norm_num) (by norm_num) (by norm_num) count_29_14 count_28_13 (by norm_num)

theorem count_30_15 : noSingleton 30 15 = 6190283353629375 := by
  exact count_step_checked 30 29 28 15 14 0 213458046676875 6190283353629375
    (by norm_num) (by norm_num) (by norm_num) (noSingleton_support 29 15 (by omega)) count_28_14 (by norm_num)

theorem count_31_0 : noSingleton 31 0 = 0 := by
  exact count_zero_checked 31 30 (by norm_num)

theorem count_31_1 : noSingleton 31 1 = 1 := by
  exact count_step_checked 31 30 29 1 0 1 0 1
    (by norm_num) (by norm_num) (by norm_num) count_30_1 count_29_0 (by norm_num)

theorem count_31_2 : noSingleton 31 2 = 1073741792 := by
  exact count_step_checked 31 30 29 2 1 536870881 1 1073741792
    (by norm_num) (by norm_num) (by norm_num) count_30_2 count_29_1 (by norm_num)

theorem count_31_3 : noSingleton 31 3 = 102927849307725 := by
  exact count_step_checked 31 30 29 3 2 34306598748315 268435426 102927849307725
    (by norm_num) (by norm_num) (by norm_num) count_30_3 count_29_2 (by norm_num)

theorem count_31_4 : noSingleton 31 4 = 190987009688289400 := by
  exact count_step_checked 31 30 29 4 3 47660995655984740 11434235478348 190987009688289400
    (by norm_num) (by norm_num) (by norm_num) count_30_4 count_29_3 (by norm_num)

theorem count_31_5 : noSingleton 31 5 = 37130196776006316450 := by
  exact count_step_checked 31 30 29 5 4 7354713630885534810 11887620719288080 37130196776006316450
    (by norm_num) (by norm_num) (by norm_num) count_30_5 count_29_4 (by norm_num)

theorem count_31_6 : noSingleton 31 6 = 1570032618914081423556 := by
  exact count_step_checked 31 30 29 6 5 254403316969829496651 1453757236503481455 1570032618914081423556
    (by norm_num) (by norm_num) (by norm_num) count_30_6 count_29_5 (by norm_num)

theorem count_31_7 : noSingleton 31 7 = 20905868500095157003425 := by
  exact count_step_checked 31 30 29 7 6 2810773100340814844235 41015226590315103126 20905868500095157003425
    (by norm_num) (by norm_num) (by norm_num) count_30_7 count_29_6 (by norm_num)

theorem count_31_8 : noSingleton 31 8 = 107715376461325505112240 := by
  exact count_step_checked 31 30 29 8 7 12060766778407943395800 374308074468731931528 107715376461325505112240
    (by norm_num) (by norm_num) (by norm_num) count_30_8 count_29_7 (by norm_num)

theorem count_31_9 : noSingleton 31 9 = 241805483820600374124450 := by
  exact count_step_checked 31 30 29 9 8 22437533373063238480050 1328922782101040926800 241805483820600374124450
    (by norm_num) (by norm_num) (by norm_num) count_30_9 count_29_8 (by norm_num)

theorem count_31_10 : noSingleton 31 10 = 252151327965525374386000 := by
  exact count_step_checked 31 30 29 10 9 19125038051285601184750 2030031581755645417950 252151327965525374386000
    (by norm_num) (by norm_num) (by norm_num) count_30_10 count_29_9 (by norm_num)

theorem count_31_11 : noSingleton 31 11 = 124950051887629643424750 := by
  exact count_step_checked 31 30 29 11 10 7553200464762461759250 1395494892508085469100 124950051887629643424750
    (by norm_num) (by norm_num) (by norm_num) count_30_11 count_29_10 (by norm_num)

theorem count_31_12 : noSingleton 31 12 = 28913007877360182576000 := by
  exact count_step_checked 31 30 29 12 11 1333642471446843558000 430309940666601996000 28913007877360182576000
    (by norm_num) (by norm_num) (by norm_num) count_30_12 count_29_11 (by norm_num)

theorem count_31_13 : noSingleton 31 13 = 2911943221470826042500 := by
  exact count_step_checked 31 30 29 13 12 94720506100682962500 56019221405398251000 2911943221470826042500
    (by norm_num) (by norm_num) (by norm_num) count_30_13 count_29_12 (by norm_num)

theorem count_31_14 : noSingleton 31 14 = 108060337458000427500 := by
  exact count_step_checked 31 30 29 14 13 2094379201311271875 2624634287988087375 108060337458000427500
    (by norm_num) (by norm_num) (by norm_num) count_30_14 count_29_13 (by norm_num)

theorem count_31_15 : noSingleton 31 15 = 959493919812553125 := by
  exact count_step_checked 31 30 29 15 14 6190283353629375 28887988983603750 959493919812553125
    (by norm_num) (by norm_num) (by norm_num) count_30_15 count_29_14 (by norm_num)

end BstLean.Part292
