import BstLean.Part292Count3

/-! Fixed moment-order certificates with explicit indices. -/
namespace BstLean.Part292
open BstLean.Part239

theorem count_32_0 : noSingleton 32 0 = 0 := by
  exact count_zero_checked 32 31 (by norm_num)

theorem count_32_1 : noSingleton 32 1 = 1 := by
  exact count_step_checked 32 31 30 1 0 1 0 1
    (by norm_num) (by norm_num) (by norm_num) count_31_1 count_30_0 (by norm_num)

theorem count_32_2 : noSingleton 32 2 = 2147483615 := by
  exact count_step_checked 32 31 30 2 1 1073741792 1 2147483615
    (by norm_num) (by norm_num) (by norm_num) count_31_2 count_30_1 (by norm_num)

theorem count_32_3 : noSingleton 32 3 = 308800190920486 := by
  exact count_step_checked 32 31 30 3 2 102927849307725 536870881 308800190920486
    (by norm_num) (by norm_num) (by norm_num) count_31_3 count_30_2 (by norm_num)

theorem count_32_4 : noSingleton 32 4 = 765011543314355365 := by
  exact count_step_checked 32 31 30 4 3 190987009688289400 34306598748315 765011543314355365
    (by norm_num) (by norm_num) (by norm_num) count_31_4 count_30_3 (by norm_num)

theorem count_32_5 : noSingleton 32 5 = 187128474745367109190 := by
  exact count_step_checked 32 31 30 5 4 37130196776006316450 47660995655984740 187128474745367109190
    (by norm_num) (by norm_num) (by norm_num) count_31_5 count_30_4 (by norm_num)

theorem count_32_6 : noSingleton 32 6 = 9648191836041940120446 := by
  exact count_step_checked 32 31 30 6 5 1570032618914081423556 7354713630885534810 9648191836041940120446
    (by norm_num) (by norm_num) (by norm_num) count_31_6 count_30_5 (by norm_num)

theorem count_32_7 : noSingleton 32 7 = 154227582326730813420156 := by
  exact count_step_checked 32 31 30 7 6 20905868500095157003425 254403316969829496651 154227582326730813420156
    (by norm_num) (by norm_num) (by norm_num) count_31_7 count_30_6 (by norm_num)

theorem count_32_8 : noSingleton 32 8 = 948856977801169301069205 := by
  exact count_step_checked 32 31 30 8 7 107715376461325505112240 2810773100340814844235 948856977801169301069205
    (by norm_num) (by norm_num) (by norm_num) count_31_8 count_30_7 (by norm_num)

theorem count_32_9 : noSingleton 32 9 = 2550133124516049612389850 := by
  exact count_step_checked 32 31 30 9 8 241805483820600374124450 12060766778407943395800 2550133124516049612389850
    (by norm_num) (by norm_num) (by norm_num) count_31_9 count_30_8 (by norm_num)

theorem count_32_10 : noSingleton 32 10 = 3217076814220214136741550 := by
  exact count_step_checked 32 31 30 10 9 252151327965525374386000 22437533373063238480050 3217076814220214136741550
    (by norm_num) (by norm_num) (by norm_num) count_31_10 count_30_9 (by norm_num)

theorem count_32_11 : noSingleton 32 11 = 1967326750353779714399500 := by
  exact count_step_checked 32 31 30 11 10 124950051887629643424750 19125038051285601184750 1967326750353779714399500
    (by norm_num) (by norm_num) (by norm_num) count_31_11 count_30_10 (by norm_num)

theorem count_32_12 : noSingleton 32 12 = 581105308935958505448750 := by
  exact count_step_checked 32 31 30 12 11 28913007877360182576000 7553200464762461759250 581105308935958505448750
    (by norm_num) (by norm_num) (by norm_num) count_31_12 count_30_11 (by norm_num)

theorem count_32_13 : noSingleton 32 13 = 79198178493972888850500 := by
  exact count_step_checked 32 31 30 13 12 2911943221470826042500 1333642471446843558000 79198178493972888850500
    (by norm_num) (by norm_num) (by norm_num) count_31_13 count_30_12 (by norm_num)

theorem count_32_14 : noSingleton 32 14 = 4449180413533177822500 := by
  exact count_step_checked 32 31 30 14 13 108060337458000427500 94720506100682962500 4449180413533177822500
    (by norm_num) (by norm_num) (by norm_num) count_31_14 count_30_13 (by norm_num)

theorem count_32_15 : noSingleton 32 15 = 79318164037837725000 := by
  exact count_step_checked 32 31 30 15 14 959493919812553125 2094379201311271875 79318164037837725000
    (by norm_num) (by norm_num) (by norm_num) count_31_15 count_30_14 (by norm_num)

theorem count_32_16 : noSingleton 32 16 = 191898783962510625 := by
  exact count_step_checked 32 31 30 16 15 0 6190283353629375 191898783962510625
    (by norm_num) (by norm_num) (by norm_num) (noSingleton_support 31 16 (by omega)) count_30_15 (by norm_num)

theorem count_33_0 : noSingleton 33 0 = 0 := by
  exact count_zero_checked 33 32 (by norm_num)

theorem count_33_1 : noSingleton 33 1 = 1 := by
  exact count_step_checked 33 32 31 1 0 1 0 1
    (by norm_num) (by norm_num) (by norm_num) count_32_1 count_31_0 (by norm_num)

theorem count_33_2 : noSingleton 33 2 = 4294967262 := by
  exact count_step_checked 33 32 31 2 1 2147483615 1 4294967262
    (by norm_num) (by norm_num) (by norm_num) count_32_2 count_31_1 (by norm_num)

theorem count_33_3 : noSingleton 33 3 = 926434932498802 := by
  exact count_step_checked 33 32 31 3 2 308800190920486 1073741792 926434932498802
    (by norm_num) (by norm_num) (by norm_num) count_32_3 count_31_2 (by norm_num)

theorem count_33_4 : noSingleton 33 4 = 3063339864435268660 := by
  exact count_step_checked 33 32 31 4 3 765011543314355365 102927849307725 3063339864435268660
    (by norm_num) (by norm_num) (by norm_num) count_32_4 count_31_3 (by norm_num)

theorem count_33_5 : noSingleton 33 5 = 941753958036860806750 := by
  exact count_step_checked 33 32 31 5 4 187128474745367109190 190987009688289400 941753958036860806750
    (by norm_num) (by norm_num) (by norm_num) count_32_5 count_31_4 (by norm_num)

theorem count_33_6 : noSingleton 33 6 = 59077317313083842849076 := by
  exact count_step_checked 33 32 31 6 5 9648191836041940120446 37130196776006316450 59077317313083842849076
    (by norm_num) (by norm_num) (by norm_num) count_32_6 count_31_5 (by norm_num)

theorem count_33_7 : noSingleton 33 7 = 1129834120092366299494884 := by
  exact count_step_checked 33 32 31 7 6 154227582326730813420156 1570032618914081423556 1129834120092366299494884
    (by norm_num) (by norm_num) (by norm_num) count_32_7 count_31_6 (by norm_num)

theorem count_33_8 : noSingleton 33 8 = 8259843614412399432663240 := by
  exact count_step_checked 33 32 31 8 7 948856977801169301069205 20905868500095157003425 8259843614412399432663240
    (by norm_num) (by norm_num) (by norm_num) count_32_8 count_31_7 (by norm_num)

theorem count_33_9 : noSingleton 33 9 = 26398090167406862675100330 := by
  exact count_step_checked 33 32 31 9 8 2550133124516049612389850 107715376461325505112240 26398090167406862675100330
    (by norm_num) (by norm_num) (by norm_num) count_32_9 count_31_8 (by norm_num)

theorem count_33_10 : noSingleton 33 10 = 39908543624461353339397900 := by
  exact count_step_checked 33 32 31 10 9 3217076814220214136741550 241805483820600374124450 39908543624461353339397900
    (by norm_num) (by norm_num) (by norm_num) count_32_10 count_31_9 (by norm_num)

theorem count_33_11 : noSingleton 33 11 = 29709436748788388838746500 := by
  exact count_step_checked 33 32 31 11 10 1967326750353779714399500 252151327965525374386000 29709436748788388838746500
    (by norm_num) (by norm_num) (by norm_num) count_32_11 count_31_10 (by norm_num)

theorem count_33_12 : noSingleton 33 12 = 10971665367635650654977000 := by
  exact count_step_checked 33 32 31 12 11 581105308935958505448750 124950051887629643424750 10971665367635650654977000
    (by norm_num) (by norm_num) (by norm_num) count_32_12 count_31_11 (by norm_num)

theorem count_33_13 : noSingleton 33 13 = 1954792572497173397488500 := by
  exact count_step_checked 33 32 31 13 12 79198178493972888850500 28913007877360182576000 1954792572497173397488500
    (by norm_num) (by norm_num) (by norm_num) count_32_13 count_31_12 (by norm_num)

theorem count_33_14 : noSingleton 33 14 = 155470708876530922875000 := by
  exact count_step_checked 33 32 31 14 13 4449180413533177822500 2911943221470826042500 155470708876530922875000
    (by norm_num) (by norm_num) (by norm_num) count_32_14 count_31_13 (by norm_num)

theorem count_33_15 : noSingleton 33 15 = 4647703259223579555000 := by
  exact count_step_checked 33 32 31 15 14 79318164037837725000 108060337458000427500 4647703259223579555000
    (by norm_num) (by norm_num) (by norm_num) count_32_15 count_31_14 (by norm_num)

theorem count_33_16 : noSingleton 33 16 = 33774185977401870000 := by
  exact count_step_checked 33 32 31 16 15 191898783962510625 959493919812553125 33774185977401870000
    (by norm_num) (by norm_num) (by norm_num) count_32_16 count_31_15 (by norm_num)

theorem count_34_0 : noSingleton 34 0 = 0 := by
  exact count_zero_checked 34 33 (by norm_num)

theorem count_34_1 : noSingleton 34 1 = 1 := by
  exact count_step_checked 34 33 32 1 0 1 0 1
    (by norm_num) (by norm_num) (by norm_num) count_33_1 count_32_0 (by norm_num)

theorem count_34_2 : noSingleton 34 2 = 8589934557 := by
  exact count_step_checked 34 33 32 2 1 4294967262 1 8589934557
    (by norm_num) (by norm_num) (by norm_num) count_33_2 count_32_1 (by norm_num)

theorem count_34_3 : noSingleton 34 3 = 2779375664455701 := by
  exact count_step_checked 34 33 32 3 2 926434932498802 2147483615 2779375664455701
    (by norm_num) (by norm_num) (by norm_num) count_33_3 count_32_2 (by norm_num)

theorem count_34_4 : noSingleton 34 4 = 12263549864041450678 := by
  exact count_step_checked 34 33 32 4 3 3063339864435268660 308800190920486 12263549864041450678
    (by norm_num) (by norm_num) (by norm_num) count_33_4 count_32_3 (by norm_num)

theorem count_34_5 : noSingleton 34 5 = 4734015171113677760795 := by
  exact count_step_checked 34 33 32 5 4 941753958036860806750 765011543314355365 4734015171113677760795
    (by norm_num) (by norm_num) (by norm_num) count_33_5 count_32_4 (by norm_num)

theorem count_34_6 : noSingleton 34 6 = 360639143545100171697726 := by
  exact count_step_checked 34 33 32 6 5 59077317313083842849076 187128474745367109190 360639143545100171697726
    (by norm_num) (by norm_num) (by norm_num) count_33_6 count_32_5 (by norm_num)

theorem count_34_7 : noSingleton 34 7 = 8227229171235948120438906 := by
  exact count_step_checked 34 33 32 7 6 1129834120092366299494884 9648191836041940120446 8227229171235948120438906
    (by norm_num) (by norm_num) (by norm_num) count_33_7 count_32_6 (by norm_num)

theorem count_34_8 : noSingleton 34 8 = 71168259132081312304171068 := by
  exact count_step_checked 34 33 32 8 7 8259843614412399432663240 154227582326730813420156 71168259132081312304171068
    (by norm_num) (by norm_num) (by norm_num) count_33_8 count_32_7 (by norm_num)

theorem count_34_9 : noSingleton 34 9 = 268895091774100351011186735 := by
  exact count_step_checked 34 33 32 9 8 26398090167406862675100330 948856977801169301069205 268895091774100351011186735
    (by norm_num) (by norm_num) (by norm_num) count_33_9 count_32_8 (by norm_num)

theorem count_34_10 : noSingleton 34 10 = 483239829353643170602844050 := by
  exact count_step_checked 34 33 32 10 9 39908543624461353339397900 2550133124516049612389850 483239829353643170602844050
    (by norm_num) (by norm_num) (by norm_num) count_33_10 count_32_9 (by norm_num)

theorem count_34_11 : noSingleton 34 11 = 432967339105939343738682650 := by
  exact count_step_checked 34 33 32 11 10 29709436748788388838746500 3217076814220214136741550 432967339105939343738682650
    (by norm_num) (by norm_num) (by norm_num) count_33_11 count_32_10 (by norm_num)

theorem count_34_12 : noSingleton 34 12 = 196581767173302538434907500 := by
  exact count_step_checked 34 33 32 12 11 10971665367635650654977000 1967326750353779714399500 196581767173302538434907500
    (by norm_num) (by norm_num) (by norm_num) count_33_12 count_32_11 (by norm_num)

theorem count_34_13 : noSingleton 34 13 = 44588778637349884847159250 := by
  exact count_step_checked 34 33 32 13 12 1954792572497173397488500 581105308935958505448750 44588778637349884847159250
    (by norm_num) (by norm_num) (by norm_num) count_33_13 count_32_12 (by norm_num)

theorem count_34_14 : noSingleton 34 14 = 4790129814572538252316500 := by
  exact count_step_checked 34 33 32 14 13 155470708876530922875000 79198178493972888850500 4790129814572538252316500
    (by norm_num) (by norm_num) (by norm_num) count_33_14 count_32_13 (by norm_num)

theorem count_34_15 : noSingleton 34 15 = 216538502534948561467500 := by
  exact count_step_checked 34 33 32 15 14 4647703259223579555000 4449180413533177822500 216538502534948561467500
    (by norm_num) (by norm_num) (by norm_num) count_33_15 count_32_14 (by norm_num)

theorem count_34_16 : noSingleton 34 16 = 3157886388887074845000 := by
  exact count_step_checked 34 33 32 16 15 33774185977401870000 79318164037837725000 3157886388887074845000
    (by norm_num) (by norm_num) (by norm_num) count_33_16 count_32_15 (by norm_num)

theorem count_34_17 : noSingleton 34 17 = 6332659870762850625 := by
  exact count_step_checked 34 33 32 17 16 0 191898783962510625 6332659870762850625
    (by norm_num) (by norm_num) (by norm_num) (noSingleton_support 33 17 (by omega)) count_32_16 (by norm_num)

theorem count_35_0 : noSingleton 35 0 = 0 := by
  exact count_zero_checked 35 34 (by norm_num)

theorem count_35_1 : noSingleton 35 1 = 1 := by
  exact count_step_checked 35 34 33 1 0 1 0 1
    (by norm_num) (by norm_num) (by norm_num) count_34_1 count_33_0 (by norm_num)

theorem count_35_2 : noSingleton 35 2 = 17179869148 := by
  exact count_step_checked 35 34 33 2 1 8589934557 1 17179869148
    (by norm_num) (by norm_num) (by norm_num) count_34_2 count_33_1 (by norm_num)

theorem count_35_3 : noSingleton 35 3 = 8338273022254011 := by
  exact count_step_checked 35 34 33 3 2 2779375664455701 4294967262 8338273022254011
    (by norm_num) (by norm_num) (by norm_num) count_34_3 count_33_2 (by norm_num)

theorem count_35_4 : noSingleton 35 4 = 49085698243870761980 := by
  exact count_step_checked 35 34 33 4 3 12263549864041450678 926434932498802 49085698243870761980
    (by norm_num) (by norm_num) (by norm_num) count_34_4 count_33_3 (by norm_num)

theorem count_35_5 : noSingleton 35 5 = 23774229410959187938415 := by
  exact count_step_checked 35 34 33 5 4 4734015171113677760795 3063339864435268660 23774229410959187938415
    (by norm_num) (by norm_num) (by norm_num) count_34_5 count_33_4 (by norm_num)

theorem count_35_6 : noSingleton 35 6 = 2195854495843854297615856 := by
  exact count_step_checked 35 34 33 6 5 360639143545100171697726 941753958036860806750 2195854495843854297615856
    (by norm_num) (by norm_num) (by norm_num) count_34_6 count_33_5 (by norm_num)

theorem count_35_7 : noSingleton 35 7 = 59599232987296487499940926 := by
  exact count_step_checked 35 34 33 7 6 8227229171235948120438906 59077317313083842849076 59599232987296487499940926
    (by norm_num) (by norm_num) (by norm_num) count_34_7 count_33_6 (by norm_num)

theorem count_35_8 : noSingleton 35 8 = 607760433139790952616194600 := by
  exact count_step_checked 35 34 33 8 7 71168259132081312304171068 1129834120092366299494884 607760433139790952616194600
    (by norm_num) (by norm_num) (by norm_num) count_34_8 count_33_7 (by norm_num)

theorem count_35_9 : noSingleton 35 9 = 2700890508856924739811230775 := by
  exact count_step_checked 35 34 33 9 8 268895091774100351011186735 8259843614412399432663240 2700890508856924739811230775
    (by norm_num) (by norm_num) (by norm_num) count_34_9 count_33_8 (by norm_num)

theorem count_35_10 : noSingleton 35 10 = 5729933359228265036981851720 := by
  exact count_step_checked 35 34 33 10 9 483239829353643170602844050 26398090167406862675100330 5729933359228265036981851720
    (by norm_num) (by norm_num) (by norm_num) count_34_10 count_33_9 (by norm_num)

theorem count_35_11 : noSingleton 35 11 = 6119531213397018794665037750 := by
  exact count_step_checked 35 34 33 11 10 432967339105939343738682650 39908543624461353339397900 6119531213397018794665037750
    (by norm_num) (by norm_num) (by norm_num) count_34_11 count_33_10 (by norm_num)

theorem count_35_12 : noSingleton 35 12 = 3369102055538435681736271000 := by
  exact count_step_checked 35 34 33 12 11 196581767173302538434907500 29709436748788388838746500 3369102055538435681736271000
    (by norm_num) (by norm_num) (by norm_num) count_34_12 count_33_11 (by norm_num)

theorem count_35_13 : noSingleton 35 13 = 952690744785160625282288250 := by
  exact count_step_checked 35 34 33 13 12 44588778637349884847159250 10971665367635650654977000 952690744785160625282288250
    (by norm_num) (by norm_num) (by norm_num) count_34_13 count_33_12 (by norm_num)

theorem count_35_14 : noSingleton 35 14 = 133524764868919431047040000 := by
  exact count_step_checked 35 34 33 14 13 4790129814572538252316500 1954792572497173397488500 133524764868919431047040000
    (by norm_num) (by norm_num) (by norm_num) count_34_14 count_33_13 (by norm_num)

theorem count_35_15 : noSingleton 35 15 = 8534081639826279799762500 := by
  exact count_step_checked 35 34 33 15 14 216538502534948561467500 155470708876530922875000 8534081639826279799762500
    (by norm_num) (by norm_num) (by norm_num) count_34_15 count_33_14 (by norm_num)

theorem count_35_16 : noSingleton 35 16 = 208548093035794902390000 := by
  exact count_step_checked 35 34 33 16 15 3157886388887074845000 4647703259223579555000 208548093035794902390000
    (by norm_num) (by norm_num) (by norm_num) count_34_16 count_33_15 (by norm_num)

theorem count_35_17 : noSingleton 35 17 = 1255977541034632040625 := by
  exact count_step_checked 35 34 33 17 16 6332659870762850625 33774185977401870000 1255977541034632040625
    (by norm_num) (by norm_num) (by norm_num) count_34_17 count_33_16 (by norm_num)

theorem count_36_0 : noSingleton 36 0 = 0 := by
  exact count_zero_checked 36 35 (by norm_num)

theorem count_36_1 : noSingleton 36 1 = 1 := by
  exact count_step_checked 36 35 34 1 0 1 0 1
    (by norm_num) (by norm_num) (by norm_num) count_35_1 count_34_0 (by norm_num)

theorem count_36_2 : noSingleton 36 2 = 34359738331 := by
  exact count_step_checked 36 35 34 2 1 17179869148 1 34359738331
    (by norm_num) (by norm_num) (by norm_num) count_35_2 count_34_1 (by norm_num)

theorem count_36_3 : noSingleton 36 3 = 25015119714471528 := by
  exact count_step_checked 36 35 34 3 2 8338273022254011 8589934557 25015119714471528
    (by norm_num) (by norm_num) (by norm_num) count_35_3 count_34_2 (by norm_num)

theorem count_36_4 : noSingleton 36 4 = 196440071123738997455 := by
  exact count_step_checked 36 35 34 4 3 49085698243870761980 2779375664455701 196440071123738997455
    (by norm_num) (by norm_num) (by norm_num) count_35_4 count_34_3 (by norm_num)

theorem count_36_5 : noSingleton 36 5 = 119300371300037390465805 := by
  exact count_step_checked 36 35 34 5 4 23774229410959187938415 12263549864041450678 119300371300037390465805
    (by norm_num) (by norm_num) (by norm_num) count_35_5 count_34_4 (by norm_num)

theorem count_36_6 : noSingleton 36 6 = 13340817506052104507322961 := by
  exact count_step_checked 36 35 34 6 5 2195854495843854297615856 4734015171113677760795 13340817506052104507322961
    (by norm_num) (by norm_num) (by norm_num) count_35_6 count_34_5 (by norm_num)

theorem count_36_7 : noSingleton 36 7 = 429817000935153918509006892 := by
  exact count_step_checked 36 35 34 7 6 59599232987296487499940926 360639143545100171697726 429817000935153918509006892
    (by norm_num) (by norm_num) (by norm_num) count_35_7 count_34_6 (by norm_num)

theorem count_36_8 : noSingleton 36 8 = 5150036486111585805144918510 := by
  exact count_step_checked 36 35 34 8 7 607760433139790952616194600 8227229171235948120438906 5150036486111585805144918510
    (by norm_num) (by norm_num) (by norm_num) count_35_8 count_34_7 (by norm_num)

theorem count_36_9 : noSingleton 36 9 = 26798903649335168588947064355 := by
  exact count_step_checked 36 35 34 9 8 2700890508856924739811230775 71168259132081312304171068 26798903649335168588947064355
    (by norm_num) (by norm_num) (by norm_num) count_35_9 count_34_8 (by norm_num)

theorem count_36_10 : noSingleton 36 10 = 66710661804376162655210052925 := by
  exact count_step_checked 36 35 34 10 9 5729933359228265036981851720 268895091774100351011186735 66710661804376162655210052925
    (by norm_num) (by norm_num) (by norm_num) count_35_10 count_34_9 (by norm_num)

theorem count_36_11 : noSingleton 36 11 = 84228237374744717712414957000 := by
  exact count_step_checked 36 35 34 11 10 6119531213397018794665037750 483239829353643170602844050 84228237374744717712414957000
    (by norm_num) (by norm_num) (by norm_num) count_35_11 count_34_10 (by norm_num)

theorem count_36_12 : noSingleton 36 12 = 55583081535169105211689144750 := by
  exact count_step_checked 36 35 34 12 11 3369102055538435681736271000 432967339105939343738682650 55583081535169105211689144750
    (by norm_num) (by norm_num) (by norm_num) count_35_12 count_34_11 (by norm_num)

theorem count_36_13 : noSingleton 36 13 = 19265341533272676973891509750 := by
  exact count_step_checked 36 35 34 13 12 952690744785160625282288250 196581767173302538434907500 19265341533272676973891509750
    (by norm_num) (by norm_num) (by norm_num) count_35_13 count_34_12 (by norm_num)

theorem count_36_14 : noSingleton 36 14 = 3429953960472118004309133750 := by
  exact count_step_checked 36 35 34 14 13 133524764868919431047040000 44588778637349884847159250 3429953960472118004309133750
    (by norm_num) (by norm_num) (by norm_num) count_35_14 count_34_13 (by norm_num)

theorem count_36_15 : noSingleton 36 15 = 295665768107433035827515000 := by
  exact count_step_checked 36 35 34 15 14 8534081639826279799762500 4790129814572538252316500 295665768107433035827515000
    (by norm_num) (by norm_num) (by norm_num) count_35_15 count_34_14 (by norm_num)

theorem count_36_16 : noSingleton 36 16 = 10915617077295918089602500 := by
  exact count_step_checked 36 35 34 16 15 208548093035794902390000 216538502534948561467500 10915617077295918089602500
    (by norm_num) (by norm_num) (by norm_num) count_35_16 count_34_15 (by norm_num)

theorem count_36_17 : noSingleton 36 17 = 131877641808636364265625 := by
  exact count_step_checked 36 35 34 17 16 1255977541034632040625 3157886388887074845000 131877641808636364265625
    (by norm_num) (by norm_num) (by norm_num) count_35_17 count_34_16 (by norm_num)

theorem count_36_18 : noSingleton 36 18 = 221643095476699771875 := by
  exact count_step_checked 36 35 34 18 17 0 6332659870762850625 221643095476699771875
    (by norm_num) (by norm_num) (by norm_num) (noSingleton_support 35 18 (by omega)) count_34_17 (by norm_num)

theorem count_37_0 : noSingleton 37 0 = 0 := by
  exact count_zero_checked 37 36 (by norm_num)

theorem count_37_1 : noSingleton 37 1 = 1 := by
  exact count_step_checked 37 36 35 1 0 1 0 1
    (by norm_num) (by norm_num) (by norm_num) count_36_1 count_35_0 (by norm_num)

theorem count_37_2 : noSingleton 37 2 = 68719476698 := by
  exact count_step_checked 37 36 35 2 1 34359738331 1 68719476698
    (by norm_num) (by norm_num) (by norm_num) count_36_2 count_35_1 (by norm_num)

theorem count_37_3 : noSingleton 37 3 = 75045977618703912 := by
  exact count_step_checked 37 36 35 3 2 25015119714471528 17179869148 75045977618703912
    (by norm_num) (by norm_num) (by norm_num) count_36_3 count_35_2 (by norm_num)

theorem count_37_4 : noSingleton 37 4 = 786060462323757134216 := by
  exact count_step_checked 37 36 35 4 3 196440071123738997455 8338273022254011 786060462323757134216
    (by norm_num) (by norm_num) (by norm_num) count_36_4 count_35_3 (by norm_num)

theorem count_37_5 : noSingleton 37 5 = 598268941636966299760305 := by
  exact count_step_checked 37 36 35 5 4 119300371300037390465805 49085698243870761980 598268941636966299760305
    (by norm_num) (by norm_num) (by norm_num) count_36_5 count_35_4 (by norm_num)

theorem count_37_6 : noSingleton 37 6 = 80900777295107157809720706 := by
  exact count_step_checked 37 36 35 6 5 13340817506052104507322961 23774229410959187938415 80900777295107157809720706
    (by norm_num) (by norm_num) (by norm_num) count_36_6 count_35_5 (by norm_num)

theorem count_37_7 : noSingleton 37 7 = 3087769768396456184277219060 := by
  exact count_step_checked 37 36 35 7 6 429817000935153918509006892 2195854495843854297615856 3087769768396456184277219060
    (by norm_num) (by norm_num) (by norm_num) count_36_7 count_35_6 (by norm_num)

theorem count_37_8 : noSingleton 37 8 = 43345864276435359991157221416 := by
  exact count_step_checked 37 36 35 8 7 5150036486111585805144918510 59599232987296487499940926 43345864276435359991157221416
    (by norm_num) (by norm_num) (by norm_num) count_36_8 count_35_7 (by norm_num)

theorem count_37_9 : noSingleton 37 9 = 263069508437048991594706584795 := by
  exact count_step_checked 37 36 35 9 8 26798903649335168588947064355 607760433139790952616194600 263069508437048991594706584795
    (by norm_num) (by norm_num) (by norm_num) count_36_9 count_35_8 (by norm_num)

theorem count_37_10 : noSingleton 37 10 = 764338676362610917185304837150 := by
  exact count_step_checked 37 36 35 10 9 66710661804376162655210052925 2700890508856924739811230775 764338676362610917185304837150
    (by norm_num) (by norm_num) (by norm_num) count_36_10 count_35_9 (by norm_num)

theorem count_37_11 : noSingleton 37 11 = 1132788212054409436167911188920 := by
  exact count_step_checked 37 36 35 11 10 84228237374744717712414957000 5729933359228265036981851720 1132788212054409436167911188920
    (by norm_num) (by norm_num) (by norm_num) count_36_11 count_35_10 (by norm_num)

theorem count_37_12 : noSingleton 37 12 = 887300102104321939148211096000 := by
  exact count_step_checked 37 36 35 12 11 55583081535169105211689144750 6119531213397018794665037750 887300102104321939148211096000
    (by norm_num) (by norm_num) (by norm_num) count_36_12 count_35_11 (by norm_num)

theorem count_37_13 : noSingleton 37 13 = 371737113931928485203095382750 := by
  exact count_step_checked 37 36 35 13 12 19265341533272676973891509750 3369102055538435681736271000 371737113931928485203095382750
    (by norm_num) (by norm_num) (by norm_num) count_36_13 count_35_12 (by norm_num)

theorem count_37_14 : noSingleton 37 14 = 82316222258875434570490249500 := by
  exact count_step_checked 37 36 35 14 13 3429953960472118004309133750 952690744785160625282288250 82316222258875434570490249500
    (by norm_num) (by norm_num) (by norm_num) count_36_14 count_35_13 (by norm_num)

theorem count_37_15 : noSingleton 37 15 = 9241878056892595055106165000 := by
  exact count_step_checked 37 36 35 15 14 295665768107433035827515000 133524764868919431047040000 9241878056892595055106165000
    (by norm_num) (by norm_num) (by norm_num) count_36_15 count_35_14 (by norm_num)

theorem count_37_16 : noSingleton 37 16 = 481876812270480762225090000 := by
  exact count_step_checked 37 36 35 16 15 10915617077295918089602500 8534081639826279799762500 481876812270480762225090000
    (by norm_num) (by norm_num) (by norm_num) count_36_16 count_35_15 (by norm_num)

theorem count_37_17 : noSingleton 37 17 = 9749651260035434678555625 := by
  exact count_step_checked 37 36 35 17 16 131877641808636364265625 208548093035794902390000 9749651260035434678555625
    (by norm_num) (by norm_num) (by norm_num) count_36_17 count_35_16 (by norm_num)

theorem count_37_18 : noSingleton 37 18 = 49204767195827349356250 := by
  exact count_step_checked 37 36 35 18 17 221643095476699771875 1255977541034632040625 49204767195827349356250
    (by norm_num) (by norm_num) (by norm_num) count_36_18 count_35_17 (by norm_num)

theorem count_38_0 : noSingleton 38 0 = 0 := by
  exact count_zero_checked 38 37 (by norm_num)

theorem count_38_1 : noSingleton 38 1 = 1 := by
  exact count_step_checked 38 37 36 1 0 1 0 1
    (by norm_num) (by norm_num) (by norm_num) count_37_1 count_36_0 (by norm_num)

theorem count_38_2 : noSingleton 38 2 = 137438953433 := by
  exact count_step_checked 38 37 36 2 1 68719476698 1 137438953433
    (by norm_num) (by norm_num) (by norm_num) count_37_2 count_36_1 (by norm_num)

theorem count_38_3 : noSingleton 38 3 = 225139204166429983 := by
  exact count_step_checked 38 37 36 3 2 75045977618703912 34359738331 225139204166429983
    (by norm_num) (by norm_num) (by norm_num) count_37_3 count_36_2 (by norm_num)

theorem count_38_4 : noSingleton 38 4 = 3145167408724463983400 := by
  exact count_step_checked 38 37 36 4 3 786060462323757134216 25015119714471528 3145167408724463983400
    (by norm_num) (by norm_num) (by norm_num) count_37_4 count_36_3 (by norm_num)

theorem count_38_5 : noSingleton 38 5 = 2998612990816409841707360 := by
  exact count_step_checked 38 37 36 5 4 598268941636966299760305 196440071123738997455 2998612990816409841707360
    (by norm_num) (by norm_num) (by norm_num) count_37_5 count_36_4 (by norm_num)

theorem count_38_6 : noSingleton 38 6 = 489818777508744330305559021 := by
  exact count_step_checked 38 37 36 6 5 80900777295107157809720706 119300371300037390465805 489818777508744330305559021
    (by norm_num) (by norm_num) (by norm_num) count_37_6 count_36_5 (by norm_num)

theorem count_38_7 : noSingleton 38 7 = 22107998626499121156711482977 := by
  exact count_step_checked 38 37 36 7 6 3087769768396456184277219060 13340817506052104507322961 22107998626499121156711482977
    (by norm_num) (by norm_num) (by norm_num) count_37_7 count_36_6 (by norm_num)

theorem count_38_8 : noSingleton 38 8 = 362670143246083574914091026332 := by
  exact count_step_checked 38 37 36 8 7 43345864276435359991157221416 429817000935153918509006892 362670143246083574914091026332
    (by norm_num) (by norm_num) (by norm_num) count_37_8 count_36_7 (by norm_num)

theorem count_38_9 : noSingleton 38 9 = 2558176925919569599142721248025 := by
  exact count_step_checked 38 37 36 9 8 263069508437048991594706584795 5150036486111585805144918510 2558176925919569599142721248025
    (by norm_num) (by norm_num) (by norm_num) count_37_9 count_36_8 (by norm_num)

theorem count_38_10 : noSingleton 38 10 = 8634946198651510409644089752635 := by
  exact count_step_checked 38 37 36 10 9 764338676362610917185304837150 26798903649335168588947064355 8634946198651510409644089752635
    (by norm_num) (by norm_num) (by norm_num) count_37_10 count_36_9 (by norm_num)

theorem count_38_11 : noSingleton 38 11 = 14928964819360421816089795036345 := by
  exact count_step_checked 38 37 36 11 10 1132788212054409436167911188920 66710661804376162655210052925 14928964819360421816089795036345
    (by norm_num) (by norm_num) (by norm_num) count_37_11 count_36_10 (by norm_num)

theorem count_38_12 : noSingleton 38 12 = 13764046008117417825137886561000 := by
  exact count_step_checked 38 37 36 12 11 887300102104321939148211096000 84228237374744717712414957000 13764046008117417825137886561000
    (by norm_num) (by norm_num) (by norm_num) count_37_12 count_36_11 (by norm_num)

theorem count_38_13 : noSingleton 38 13 = 6889156497916327200472738331500 := by
  exact count_step_checked 38 37 36 13 12 371737113931928485203095382750 55583081535169105211689144750 6889156497916327200472738331500
    (by norm_num) (by norm_num) (by norm_num) count_37_13 count_36_12 (by norm_num)

theorem count_38_14 : noSingleton 38 14 = 1865244748355345132020849353750 := by
  exact count_step_checked 38 37 36 14 13 82316222258875434570490249500 19265341533272676973891509750 1865244748355345132020849353750
    (by norm_num) (by norm_num) (by norm_num) count_37_14 count_36_13 (by norm_num)

theorem count_38_15 : noSingleton 38 15 = 265536467390857291986030423750 := by
  exact count_step_checked 38 37 36 15 14 9241878056892595055106165000 3429953960472118004309133750 265536467390857291986030423750
    (by norm_num) (by norm_num) (by norm_num) count_37_15 count_36_14 (by norm_num)

theorem count_38_16 : noSingleton 38 16 = 18649662416302714521219495000 := by
  exact count_step_checked 38 37 36 16 15 481876812270480762225090000 295665768107433035827515000 18649662416302714521219495000
    (by norm_num) (by norm_num) (by norm_num) count_37_16 count_36_15 (by norm_num)

theorem count_38_17 : noSingleton 38 17 = 569621903280551358850738125 := by
  exact count_step_checked 38 37 36 17 16 9749651260035434678555625 10915617077295918089602500 569621903280551358850738125
    (by norm_num) (by norm_num) (by norm_num) count_37_17 count_36_16 (by norm_num)

theorem count_38_18 : noSingleton 38 18 = 5765158556444437766240625 := by
  exact count_step_checked 38 37 36 18 17 49204767195827349356250 131877641808636364265625 5765158556444437766240625
    (by norm_num) (by norm_num) (by norm_num) count_37_18 count_36_17 (by norm_num)

theorem count_38_19 : noSingleton 38 19 = 8200794532637891559375 := by
  exact count_step_checked 38 37 36 19 18 0 221643095476699771875 8200794532637891559375
    (by norm_num) (by norm_num) (by norm_num) (noSingleton_support 37 19 (by omega)) count_36_18 (by norm_num)

theorem count_39_0 : noSingleton 39 0 = 0 := by
  exact count_zero_checked 39 38 (by norm_num)

theorem count_39_1 : noSingleton 39 1 = 1 := by
  exact count_step_checked 39 38 37 1 0 1 0 1
    (by norm_num) (by norm_num) (by norm_num) count_38_1 count_37_0 (by norm_num)

theorem count_39_2 : noSingleton 39 2 = 274877906904 := by
  exact count_step_checked 39 38 37 2 1 137438953433 1 274877906904
    (by norm_num) (by norm_num) (by norm_num) count_38_2 count_37_1 (by norm_num)

theorem count_39_3 : noSingleton 39 3 = 675420223839404473 := by
  exact count_step_checked 39 38 37 3 2 225139204166429983 68719476698 675420223839404473
    (by norm_num) (by norm_num) (by norm_num) count_38_3 count_37_2 (by norm_num)

theorem count_39_4 : noSingleton 39 4 = 12583521382047366682256 := by
  exact count_step_checked 39 38 37 4 3 3145167408724463983400 75045977618703912 12583521382047366682256
    (by norm_num) (by norm_num) (by norm_num) count_38_4 count_37_3 (by norm_num)

theorem count_39_5 : noSingleton 39 5 = 15022935251650351979637008 := by
  exact count_step_checked 39 38 37 5 4 2998612990816409841707360 786060462323757134216 15022935251650351979637008
    (by norm_num) (by norm_num) (by norm_num) count_38_5 count_37_4 (by norm_num)

theorem count_39_6 : noSingleton 39 6 = 2961646884834670701224245716 := by
  exact count_step_checked 39 38 37 6 5 489818777508744330305559021 598268941636966299760305 2961646884834670701224245716
    (by norm_num) (by norm_num) (by norm_num) count_38_6 count_37_5 (by norm_num)

theorem count_39_7 : noSingleton 39 7 = 157830219922707920093749767667 := by
  exact count_step_checked 39 38 37 7 6 22107998626499121156711482977 80900777295107157809720706 157830219922707920093749767667
    (by norm_num) (by norm_num) (by norm_num) count_38_7 count_37_6 (by norm_num)

theorem count_39_8 : noSingleton 39 8 = 3018696397167733934315262534936 := by
  exact count_step_checked 39 38 37 8 7 362670143246083574914091026332 3087769768396456184277219060 3018696397167733934315262534936
    (by norm_num) (by norm_num) (by norm_num) count_38_8 count_37_7 (by norm_num)

theorem count_39_9 : noSingleton 39 9 = 24670735175780670071948465646033 := by
  exact count_step_checked 39 38 37 9 8 2558176925919569599142721248025 43345864276435359991157221416 24670735175780670071948465646033
    (by norm_num) (by norm_num) (by norm_num) count_38_9 count_37_8 (by norm_num)

theorem count_39_10 : noSingleton 39 10 = 96346103307122965777039747748560 := by
  exact count_step_checked 39 38 37 10 9 8634946198651510409644089752635 263069508437048991594706584795 96346103307122965777039747748560
    (by norm_num) (by norm_num) (by norm_num) count_38_10 count_37_9 (by norm_num)

theorem count_39_11 : noSingleton 39 11 = 193263482714743854830029329211495 := by
  exact count_step_checked 39 38 37 11 10 14928964819360421816089795036345 764338676362610917185304837150 193263482714743854830029329211495
    (by norm_num) (by norm_num) (by norm_num) count_38_11 count_37_10 (by norm_num)

theorem count_39_12 : noSingleton 39 12 = 208214504155476572476035263910960 := by
  exact count_step_checked 39 38 37 12 11 13764046008117417825137886561000 1132788212054409436167911188920 208214504155476572476035263910960
    (by norm_num) (by norm_num) (by norm_num) count_38_12 count_37_11 (by norm_num)

theorem count_39_13 : noSingleton 39 13 = 123276438352876487293777619957500 := by
  exact count_step_checked 39 38 37 13 12 6889156497916327200472738331500 887300102104321939148211096000 123276438352876487293777619957500
    (by norm_num) (by norm_num) (by norm_num) count_38_13 count_37_12 (by norm_num)

theorem count_39_14 : noSingleton 39 14 = 40239436806388114286009515497000 := by
  exact count_step_checked 39 38 37 14 13 1865244748355345132020849353750 371737113931928485203095382750 40239436806388114286009515497000
    (by norm_num) (by norm_num) (by norm_num) count_38_14 count_37_13 (by norm_num)

theorem count_39_15 : noSingleton 39 15 = 7111063456700125893469085837250 := by
  exact count_step_checked 39 38 37 15 14 265536467390857291986030423750 82316222258875434570490249500 7111063456700125893469085837250
    (by norm_num) (by norm_num) (by norm_num) count_38_15 count_37_14 (by norm_num)

theorem count_39_16 : noSingleton 39 16 = 649585964822762044433546190000 := by
  exact count_step_checked 39 38 37 16 15 18649662416302714521219495000 9241878056892595055106165000 649585964822762044433546190000
    (by norm_num) (by norm_num) (by norm_num) count_38_16 count_37_15 (by norm_num)

theorem count_39_17 : noSingleton 39 17 = 27994891222047642065015968125 := by
  exact count_step_checked 39 38 37 17 16 569621903280551358850738125 481876812270480762225090000 27994891222047642065015968125
    (by norm_num) (by norm_num) (by norm_num) count_38_17 count_37_16 (by norm_num)

theorem count_39_18 : noSingleton 39 18 = 474259601897346397577445000 := by
  exact count_step_checked 39 38 37 18 17 5765158556444437766240625 9749651260035434678555625 474259601897346397577445000
    (by norm_num) (by norm_num) (by norm_num) count_38_18 count_37_17 (by norm_num)

theorem count_39_19 : noSingleton 39 19 = 2025596249561559215165625 := by
  exact count_step_checked 39 38 37 19 18 8200794532637891559375 49204767195827349356250 2025596249561559215165625
    (by norm_num) (by norm_num) (by norm_num) count_38_19 count_37_18 (by norm_num)

end BstLean.Part292
