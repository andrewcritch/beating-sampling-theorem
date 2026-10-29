import BstLean.Part255SGlobal32
import BstLean.Part255Numeric10
namespace BstLean.Part255
open Real BstLean.Part130 BstLean.Part182 BstLean.Part197 BstLean.Part246
theorem sGlobal36_hz0 : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal36_hz1 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) ((√(23 : ℝ)) / (12225 : ℝ)) := bdiv sGlobal36_hz0 (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal36_hz2 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) maskSlack := by
    convert sGlobal36_hz1 using 1 <;>
      norm_num [maskSlack] <;> ring

theorem sGlobal36_hz3 : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal36_hz4 : B (6395294793910793 / 500000000000000000) (12790589587821587 / 1000000000000000000) (√((2 / 12225) : ℝ)) := bsqrt (bpoint ((2 / 12225) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal36_hz5 : B (7230130686979 / 62500000000000000) (23136418198333 / 200000000000000000) (√((2 / 149450625) : ℝ)) := bsqrt (bpoint ((2 / 149450625) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal36_hz6 : B (2211334438749598093 / 20000000000000000) (110566721937479904651 / 1000000000000000000) (√(12225 : ℝ)) := bsqrt (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal36_hz7 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))) := bmul sGlobal36_hz3 sGlobal36_hz4 (by norm_num) (by norm_num)

theorem sGlobal36_hz8 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) ((√(12225 : ℝ)) + ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := badd sGlobal36_hz6 sGlobal36_hz7 (by norm_num) (by norm_num)

theorem sGlobal36_hz9 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) (s3ap 12225 46) := by
    convert sGlobal36_hz8 using 1 <;>
      norm_num [s3ap, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal36_hz10 : B (163599182004089 / 1000000000000000000) (16359918200409 / 100000000000000000) ((2 : ℝ) / (12225 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal36_hz11 : B (1222499983640081799591 / 100000000000000000) (12224999836400817995911 / 1000000000000000000) ((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ))) := bsub (bpoint (12225 : ℝ)) sGlobal36_hz10 (by norm_num) (by norm_num)

theorem sGlobal36_hz12 : B (110566721197658827907 / 1000000000000000000) (27641680299414706977 / 250000000000000000) (√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) := bsqrt sGlobal36_hz11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal36_hz13 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) ((√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) - ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bsub sGlobal36_hz12 sGlobal36_hz7 (by norm_num) (by norm_num)

theorem sGlobal36_hz14 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) (s3am 12225 46) := by
    convert sGlobal36_hz13 using 1 <;>
      norm_num [s3am, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal36_hz15 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√((2 / 12225) : ℝ)) * (√(92 : ℝ))) := bmul sGlobal36_hz4 sGlobal36_hz3 (by norm_num) (by norm_num)

theorem sGlobal36_hz16 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) (s3e0 12225 46) := by
    convert sGlobal36_hz15 using 1 <;>
      norm_num [s3e0, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal36_hz17 : B (250196148528560847 / 500000000000000000) (100078459411424339 / 200000000000000000) (((1 / 2) : ℝ) + maskSlack) := badd (bpoint ((1 / 2) : ℝ)) sGlobal36_hz2 (by norm_num) (by norm_num)

theorem sGlobal36_hz18 : B (59827153232297998295487 / 800000000000000) (23930861292919199366019 / 320000000000000) ((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack)) := bmul (bpoint (149450625 : ℝ)) sGlobal36_hz17 (by norm_num) (by norm_num)

theorem sGlobal36_hz19 : B (1729554180017180009583 / 200000000000000000) (8647770900085900056557 / 1000000000000000000) (√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) := bsqrt sGlobal36_hz18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal36_hz20 : B (4328681281566262743499 / 500000000000000000) (8657362563132525495641 / 1000000000000000000) ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))) := badd sGlobal36_hz19 sGlobal36_hz3 (by norm_num) (by norm_num)

theorem sGlobal36_hz21 : B (110732771457999278473 / 1000000000000000000) (55366385728999643621 / 500000000000000000) ((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ)))) := bmul sGlobal36_hz4 sGlobal36_hz20 (by norm_num) (by norm_num)

theorem sGlobal36_hz22 : B (209099159 / 15625000000000000) (13382346177 / 1000000000000000000) ((2 : ℝ) / (149450625 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (149450625 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal36_hz23 : B (2452349334953899930479 / 200000000000000000) (12261746674769501594427 / 1000000000000000000) (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2) := bsq sGlobal36_hz21 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal36_hz24 : B (82045469362091 / 500000000000000000) (32818187747289 / 200000000000000000) (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2)) := bmul sGlobal36_hz22 sGlobal36_hz23 (by norm_num) (by norm_num)

theorem sGlobal36_hz25 : B (82045469362091 / 250000000000000000) (32818187747289 / 100000000000000000) ((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) := bmul (bpoint (2 : ℝ)) sGlobal36_hz24 (by norm_num) (by norm_num)

theorem sGlobal36_hz26 : B (117258080744995992792057 / 1000000000000000000) (58629040372497996396029 / 500000000000000000) (√(13749457500 : ℝ)) := bsqrt (bpoint (13749457500 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal36_hz27 : B (117304080744995992792057 / 1000000000000000000) (58652040372497996396029 / 500000000000000000) ((√(13749457500 : ℝ)) + (46 : ℝ)) := badd sGlobal36_hz26 (bpoint (46 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal36_hz28 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal36_hz25 sGlobal36_hz27 (by norm_num) (by norm_num)

theorem sGlobal36_hz29 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (s3rs 12225 46 maskSlack) := by
    convert sGlobal36_hz28 using 1 <;>
      norm_num [s3rs, s3pp, s3K, mA, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal36_hz30 : B (490797546012267 / 1000000000000000000) (49079754601227 / 100000000000000000) ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (3 : ℝ)) sGlobal36_hz10 (by norm_num) (by norm_num)

theorem sGlobal36_hz31 : B (490797546012267 / 500000000000000000) (49079754601227 / 50000000000000000) ((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal36_hz30 (by norm_num) (by norm_num)

theorem sGlobal36_hz32 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal36_hz31 sGlobal36_hz27 (by norm_num) (by norm_num)

theorem sGlobal36_hz33 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (s3r1 12225 46) := by
    convert sGlobal36_hz32 using 1 <;>
      norm_num [s3r1, mA] <;> ring

theorem sGlobal36_hz34 : B (163599182004089 / 500000000000000000) (16359918200409 / 50000000000000000) ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (2 : ℝ)) sGlobal36_hz10 (by norm_num) (by norm_num)

theorem sGlobal36_hz35 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal36_hz34 (by norm_num) (by norm_num)

theorem sGlobal36_hz36 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal36_hz35 sGlobal36_hz27 (by norm_num) (by norm_num)

theorem sGlobal36_hz37 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (s3rpp 12225 46) := by
    convert sGlobal36_hz36 using 1 <;>
      norm_num [s3rpp, mA] <;> ring

theorem sGlobal36_hz38 {c : ℝ} (hc : B (21 / 40) (53 / 100) c) : B (21 / 40) (53 / 100) c := hc

theorem sGlobal36_hz39 : B (337967342370948439 / 500000000000000000) (168983671185476741 / 250000000000000000) (kdot ((21 / 40))) := by
    constructor
    · apply bkdot_lower (q := (279049910336872163 / 500000000000000000)) (a := (127260151712264637 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (22323992826949773 / 40000000000000000)) (a := (509040606849042707 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal36_hz40 : B (441 / 1600) (441 / 1600) (((21 / 40) : ℝ)^2) := bsq (bpoint ((21 / 40) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal36_hz41 : B (1159 / 1600) (1159 / 1600) ((1 : ℝ) - (((21 / 40) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal36_hz40 (by norm_num) (by norm_num)

theorem sGlobal36_hz42 : B (3324618072372891 / 3906250000000000) (851102226527460097 / 1000000000000000000) (√((1 : ℝ) - (((21 / 40) : ℝ)^2))) := bsqrt sGlobal36_hz41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal36_hz43 : B (33864281607090831 / 125000000000000000) (5418285057134533 / 20000000000000000) ((√((1 : ℝ) - (((21 / 40) : ℝ)^2))) / Real.pi) := bdiv sGlobal36_hz42 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal36_hz44 : B (17743285474474793 / 50000000000000000) (354865709489501157 / 1000000000000000000) (((21 / 40) : ℝ) * (kdot ((21 / 40)))) := bmul (bpoint ((21 / 40) : ℝ)) sGlobal36_hz39 (by norm_num) (by norm_num)

theorem sGlobal36_hz45 : B (156444990586555627 / 250000000000000000) (625779962346227807 / 1000000000000000000) (((√((1 : ℝ) - (((21 / 40) : ℝ)^2))) / Real.pi) + (((21 / 40) : ℝ) * (kdot ((21 / 40))))) := badd sGlobal36_hz43 sGlobal36_hz44 (by norm_num) (by norm_num)

theorem sGlobal36_hz46 : B (156444990586555627 / 250000000000000000) (625779962346227807 / 1000000000000000000) (kappa ((21 / 40))) := by rw [kappa_eq]; exact sGlobal36_hz45

theorem sGlobal36_hz47 : B (338904041188233601 / 500000000000000000) (42363005148529649 / 62500000000000000) (kdot ((53 / 100))) := by
    constructor
    · apply bkdot_lower (q := (554246824513826269 / 1000000000000000000)) (a := (126524470181512309 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (138561706128456567 / 250000000000000000)) (a := (101219576145207591 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal36_hz48 : B (2809 / 10000) (2809 / 10000) (((53 / 100) : ℝ)^2) := bsq (bpoint ((53 / 100) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal36_hz49 : B (7191 / 10000) (7191 / 10000) ((1 : ℝ) - (((53 / 100) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal36_hz48 (by norm_num) (by norm_num)

theorem sGlobal36_hz50 : B (84799764150615419 / 100000000000000000) (847997641506154191 / 1000000000000000000) (√((1 : ℝ) - (((53 / 100) : ℝ)^2))) := bsqrt sGlobal36_hz49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal36_hz51 : B (16870377046996679 / 62500000000000000) (53985206550389373 / 200000000000000000) ((√((1 : ℝ) - (((53 / 100) : ℝ)^2))) / Real.pi) := bdiv sGlobal36_hz50 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal36_hz52 : B (359238283659527617 / 1000000000000000000) (11226196364360357 / 31250000000000000) (((53 / 100) : ℝ) * (kdot ((53 / 100)))) := bmul (bpoint ((53 / 100) : ℝ)) sGlobal36_hz47 (by norm_num) (by norm_num)

theorem sGlobal36_hz53 : B (629164316411474481 / 1000000000000000000) (629164316411478289 / 1000000000000000000) (((√((1 : ℝ) - (((53 / 100) : ℝ)^2))) / Real.pi) + (((53 / 100) : ℝ) * (kdot ((53 / 100))))) := badd sGlobal36_hz51 sGlobal36_hz52 (by norm_num) (by norm_num)

theorem sGlobal36_hz54 : B (629164316411474481 / 1000000000000000000) (629164316411478289 / 1000000000000000000) (kappa ((53 / 100))) := by rw [kappa_eq]; exact sGlobal36_hz53

theorem sGlobal36_hz55 {c : ℝ} (hc : B (21 / 40) (53 / 100) c) : B (156444990586555627 / 250000000000000000) (629164316411478289 / 1000000000000000000) (kappa c) := bkappa (sGlobal36_hz38 hc) (by norm_num) (by norm_num) sGlobal36_hz46.1 sGlobal36_hz54.2

theorem sGlobal36_hz56 : B 24450 24450 ((2 : ℝ) * (12225 : ℝ)) := bmul (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal36_hz57 {c : ℝ} (hc : B (21 / 40) (53 / 100) c) : B (370835683588521711 / 1000000000000000000) (93555009413444373 / 250000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (sGlobal36_hz55 hc) (by norm_num) (by norm_num)

theorem sGlobal36_hz58 {c : ℝ} (hc : B (21 / 40) (53 / 100) c) : B (181338649274787116679 / 20000000000000000) (45748399603174298397 / 5000000000000000) (((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) := bmul sGlobal36_hz56 (sGlobal36_hz57 hc) (by norm_num) (by norm_num)

theorem sGlobal36_hz59 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (4 : ℝ)) sGlobal36_hz10 (by norm_num) (by norm_num)

theorem sGlobal36_hz60 {c : ℝ} (hc : B (21 / 40) (53 / 100) c) : B (906693180934262781759 / 100000000000000000) (2287419816559532915761 / 250000000000000000) ((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bsub (sGlobal36_hz58 hc) sGlobal36_hz59 (by norm_num) (by norm_num)

theorem sGlobal36_hz61 {c : ℝ} (hc : B (21 / 40) (53 / 100) c) : B (2380510949531453507 / 25000000000000000) (95653955831623250557 / 1000000000000000000) (√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) := bsqrt (sGlobal36_hz60 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal36_hz62 : B (30670756373515103 / 125000000000000000) (122683025494060423 / 500000000000000000) ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal36_hz7 (by norm_num) (by norm_num)

theorem sGlobal36_hz63 {c : ℝ} (hc : B (21 / 40) (53 / 100) c) : B (47487535965135009717 / 500000000000000000) (95408589780635129733 / 1000000000000000000) ((√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) - ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))))) := bsub (sGlobal36_hz61 hc) sGlobal36_hz62 (by norm_num) (by norm_num)

theorem sGlobal36_hz64 {c : ℝ} (hc : B (21 / 40) (53 / 100) c) : B (47487535965135009717 / 500000000000000000) (95408589780635129733 / 1000000000000000000) (s3dm 12225 46 c) := by
    convert (sGlobal36_hz63 hc) using 1 <;>
      norm_num [s3dm, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal36_hz65 : B (6126072185528622723889 / 500000000000000000) (2450428874211449090087 / 200000000000000000) ((s3ap 12225 46)^2) := bsq sGlobal36_hz9 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal36_hz66 : B (6126072185528622723889 / 250000000000000000) (2450428874211449090087 / 100000000000000000) ((2 : ℝ) * ((s3ap 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal36_hz65 (by norm_num) (by norm_num)

theorem sGlobal36_hz67 {c : ℝ} (hc : B (21 / 40) (53 / 100) c) : B (9020264288159964155233 / 1000000000000000000) (9102799003929514112707 / 1000000000000000000) ((s3dm 12225 46 c)^2) := bsq (sGlobal36_hz64 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal36_hz68 {c : ℝ} (hc : B (21 / 40) (53 / 100) c) : B (15401489738184976782849 / 1000000000000000000) (15484024453954526745637 / 1000000000000000000) (((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) := bsub sGlobal36_hz66 (sGlobal36_hz67 hc) (by norm_num) (by norm_num)

theorem sGlobal36_hz69 : B (1524735695971823534271 / 125000000000000000) (609894278388729413841 / 50000000000000000) ((s3am 12225 46)^2) := bsq sGlobal36_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal36_hz70 : B (1524735695971823534271 / 62500000000000000) (609894278388729413841 / 25000000000000000) ((2 : ℝ) * ((s3am 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal36_hz69 (by norm_num) (by norm_num)

theorem sGlobal36_hz71 {c : ℝ} (hc : B (21 / 40) (53 / 100) c) : B (631318012150972399 / 1000000000000000000) (317350584409103241 / 500000000000000000) ((((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) / ((2 : ℝ) * ((s3am 12225 46)^2))) := bdiv (sGlobal36_hz68 hc) sGlobal36_hz70 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal36_hz72 {c : ℝ} (hc : B (21 / 40) (53 / 100) c) : B (631318012150972399 / 1000000000000000000) (317350584409103241 / 500000000000000000) (s3c1 12225 46 c) := by
    convert (sGlobal36_hz71 hc) using 1 <;>
      norm_num [s3c1] <;> ring

theorem sGlobal36_hz73 {c : ℝ} (hc : B (21 / 40) (53 / 100) c) : B (337967342370948439 / 500000000000000000) (42363005148529649 / 62500000000000000) (kdot c) := bkdot (sGlobal36_hz38 hc) sGlobal36_hz39.1 sGlobal36_hz47.2

theorem sGlobal36_hz74 : B (5739885784898607 / 8000000000000000) (717485723112325881 / 1000000000000000000) (kdot ((631318012150972399 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (237698613684050467 / 500000000000000000)) (a := (443772388402274873 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (475397227368100933 / 1000000000000000000)) (a := (88754477680454973 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal36_hz75 : B (718876801330902839 / 1000000000000000000) (179719200332725711 / 250000000000000000) (kdot ((317350584409103241 / 500000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (472721064285863463 / 1000000000000000000)) (a := (441587287846249789 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (236360532142931731 / 500000000000000000)) (a := (441587287846249783 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal36_hz76 {c : ℝ} (hc : B (21 / 40) (53 / 100) c) : B (5739885784898607 / 8000000000000000) (179719200332725711 / 250000000000000000) (kdot (s3c1 12225 46 c)) := bkdot (sGlobal36_hz72 hc) sGlobal36_hz74.1 sGlobal36_hz75.2

theorem sGlobal36_hz77 {c : ℝ} (hc : B (21 / 40) (53 / 100) c) : B (441 / 1600) (2809 / 10000) (c^2) := bsq (sGlobal36_hz38 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal36_hz78 {c : ℝ} (hc : B (21 / 40) (53 / 100) c) : B (7191 / 10000) (1159 / 1600) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (sGlobal36_hz77 hc) (by norm_num) (by norm_num)

theorem sGlobal36_hz79 {c : ℝ} (hc : B (21 / 40) (53 / 100) c) : B (84799764150615419 / 100000000000000000) (851102226527460097 / 1000000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (sGlobal36_hz78 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal36_hz80 : B (39119999999999765769 / 1600000000000000) (3912000000000000489 / 160000000000000) ((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (149450625 : ℝ)) sGlobal36_hz10 (by norm_num) (by norm_num)

theorem sGlobal36_hz81 {c : ℝ} (hc : B (21 / 40) (53 / 100) c) : B (573191018473334419 / 1000000000000000000) (144220992017231359 / 250000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (sGlobal36_hz79 hc) (sGlobal36_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal36_hz82 {c : ℝ} (hc : B (21 / 40) (53 / 100) c) : B (14014520401672942632609 / 1000000000000000000) (7052406509642614336651 / 500000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) := bmul sGlobal36_hz80 (sGlobal36_hz81 hc) (by norm_num) (by norm_num)

theorem sGlobal36_hz83 {c : ℝ} (hc : B (21 / 40) (53 / 100) c) : B (437953762552279457269 / 62500000000000000) (7052406509642614336651 / 1000000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) / (2 : ℝ)) := bdiv (sGlobal36_hz82 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal36_hz84 {c : ℝ} (hc : B (21 / 40) (53 / 100) c) : B (437953762552279457269 / 62500000000000000) (7052406509642614336651 / 1000000000000000000) (s3Cpa 12225 c) := by
    convert (sGlobal36_hz83 hc) using 1 <;>
      norm_num [s3Cpa, mA] <;> ring

theorem sGlobal36_hz85 {c : ℝ} (hc : B (21 / 40) (53 / 100) c) : B (16870377046996679 / 62500000000000000) (5418285057134533 / 20000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (sGlobal36_hz79 hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal36_hz86 {c : ℝ} (hc : B (21 / 40) (53 / 100) c) : B (17743285474474793 / 50000000000000000) (11226196364360357 / 31250000000000000) (c * (kdot c)) := bmul (sGlobal36_hz38 hc) (sGlobal36_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal36_hz87 {c : ℝ} (hc : B (21 / 40) (53 / 100) c) : B (-1116403136344807 / 12500000000000000) (-8395145663276921 / 100000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (sGlobal36_hz85 hc) (sGlobal36_hz86 hc) (by norm_num) (by norm_num)

theorem sGlobal36_hz88 {c : ℝ} (hc : B (21 / 40) (53 / 100) c) : B (-2183684534690442764961 / 1000000000000000000) (-1026306557335597447239 / 500000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) := bmul sGlobal36_hz80 (sGlobal36_hz87 hc) (by norm_num) (by norm_num)

theorem sGlobal36_hz89 {c : ℝ} (hc : B (21 / 40) (53 / 100) c) : B (-1091842267345221382481 / 1000000000000000000) (-1026306557335597447239 / 1000000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) / (2 : ℝ)) := bdiv (sGlobal36_hz88 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal36_hz90 {c : ℝ} (hc : B (21 / 40) (53 / 100) c) : B (-1091842267345221382481 / 1000000000000000000) (-1026306557335597447239 / 1000000000000000000) (s3Cpp 12225 c) := by
    convert (sGlobal36_hz89 hc) using 1 <;>
      norm_num [s3Cpp, mA] <;> ring

theorem sGlobal36_hz91 {c : ℝ} (hc : B (21 / 40) (53 / 100) c) : B (1424481062154041804941 / 200000000000000000) (7167551619576352748877 / 1000000000000000000) ((s3Cpa 12225 c) + (s3r1 12225 46)) := badd (sGlobal36_hz84 hc) sGlobal36_hz33 (by norm_num) (by norm_num)

theorem sGlobal36_hz92 {c : ℝ} (hc : B (21 / 40) (53 / 100) c) : B (64488816496074753501 / 1000000000000000000) (64897587395376423169 / 1000000000000000000) (((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) := bdiv (sGlobal36_hz91 hc) sGlobal36_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal36_hz93 {c : ℝ} (hc : B (21 / 40) (53 / 100) c) : B (64611499521568813913 / 1000000000000000000) (8127533802608810449 / 125000000000000000) ((((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) + (s3e0 12225 46)) := badd (sGlobal36_hz92 hc) sGlobal36_hz16 (by norm_num) (by norm_num)

theorem sGlobal36_hz94 {c : ℝ} (hc : B (21 / 40) (53 / 100) c) : B (64611499521568813913 / 1000000000000000000) (8127533802608810449 / 125000000000000000) (s3Lam 12225 46 c) := by
    convert (sGlobal36_hz93 hc) using 1 <;>
      norm_num [s3Lam] <;> ring

theorem sGlobal36_hz95 {c : ℝ} (hc : B (21 / 40) (53 / 100) c) : B (-1015078860722729576881 / 1000000000000000000) (-949543150713105172421 / 1000000000000000000) ((s3Cpp 12225 c) + (s3rpp 12225 46)) := badd (sGlobal36_hz90 hc) sGlobal36_hz37 (by norm_num) (by norm_num)

theorem sGlobal36_hz96 {c : ℝ} (hc : B (21 / 40) (53 / 100) c) : B (-364858322247486434057 / 500000000000000000) (-47477157535655258621 / 100000000000000000) (if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) := bweaken (bfirst (sGlobal36_hz95 hc) (sGlobal36_hz76 hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem sGlobal36_hz97 {c : ℝ} (hc : B (21 / 40) (53 / 100) c) : B (166985834817027482767 / 40000000000000000) (4227635565603125133497 / 1000000000000000000) ((s3Lam 12225 46 c)^2) := bsq (sGlobal36_hz94 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal36_hz98 {c : ℝ} (hc : B (21 / 40) (53 / 100) c) : B (398562432466255333 / 1000000000000000000) (80569114739839489 / 200000000000000000) ((s3c1 12225 46 c)^2) := bsq (sGlobal36_hz72 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal36_hz99 {c : ℝ} (hc : B (21 / 40) (53 / 100) c) : B (119430885260160511 / 200000000000000000) (601437567533744667 / 1000000000000000000) ((1 : ℝ) - ((s3c1 12225 46 c)^2)) := bsub (bpoint (1 : ℝ)) (sGlobal36_hz98 hc) (by norm_num) (by norm_num)

theorem sGlobal36_hz100 {c : ℝ} (hc : B (21 / 40) (53 / 100) c) : B (386378838156543763 / 500000000000000000) (193881014983053567 / 250000000000000000) (√((1 : ℝ) - ((s3c1 12225 46 c)^2))) := bsqrt (sGlobal36_hz99 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal36_hz101 {c : ℝ} (hc : B (21 / 40) (53 / 100) c) : B (2427689838910315151 / 1000000000000000000) (243638068936517487 / 100000000000000000) (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))) := bmul pi_mem (sGlobal36_hz100 hc) (by norm_num) (by norm_num)

theorem sGlobal36_hz102 {c : ℝ} (hc : B (21 / 40) (53 / 100) c) : B (428365514536383458509 / 250000000000000000) (69656930598691761729 / 40000000000000000) (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2))))) := bdiv (sGlobal36_hz97 hc) (sGlobal36_hz101 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal36_hz103 {c : ℝ} (hc : B (21 / 40) (53 / 100) c) : B (491872706825280482961 / 500000000000000000) (253330337922148291403 / 200000000000000000) ((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) := badd (sGlobal36_hz96 hc) (sGlobal36_hz102 hc) (by norm_num) (by norm_num)

theorem sGlobal36_hz104 : B (3762781186094069 / 250000000000000000) (376278118609407 / 25000000000000000) ((s3e0 12225 46)^2) := bsq sGlobal36_hz16 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal36_hz105 {c : ℝ} (hc : B (21 / 40) (53 / 100) c) : B (491880232387652671099 / 500000000000000000) (253333348147097166659 / 200000000000000000) (((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) := badd (sGlobal36_hz103 hc) sGlobal36_hz104 (by norm_num) (by norm_num)

theorem sGlobal36_hz106 {c : ℝ} (hc : B (21 / 40) (53 / 100) c) : B (1022257538226552612329 / 1000000000000000000) (1305163814189610103311 / 1000000000000000000) ((((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) + (s3rs 12225 46 maskSlack)) := badd (sGlobal36_hz105 hc) sGlobal36_hz29 (by norm_num) (by norm_num)

theorem sGlobal36_hz107 {c : ℝ} (hc : B (21 / 40) (53 / 100) c) : B (1022257538226552612329 / 1000000000000000000) (1305163814189610103311 / 1000000000000000000) (s3U 12225 46 maskSlack c) := by
    convert (sGlobal36_hz106 hc) using 1 <;>
      norm_num [s3U] <;> ring

theorem sGlobal36_hz108 {c : ℝ} (hc : B (21 / 40) (53 / 100) c) : B (-1168605673967713657299 / 1000000000000000000) (-1103069963958089252839 / 1000000000000000000) ((s3Cpp 12225 c) - (s3rpp 12225 46)) := bsub (sGlobal36_hz90 hc) sGlobal36_hz37 (by norm_num) (by norm_num)

theorem sGlobal36_hz109 {c : ℝ} (hc : B (21 / 40) (53 / 100) c) : B (-1168605673967713657299 / 1000000000000000000) (-1103069963958089252839 / 1000000000000000000) (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ)) := bweaken (bmin (sGlobal36_hz108 hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem sGlobal36_hz110 {c : ℝ} (hc : B (21 / 40) (53 / 100) c) : B (-420041754459526956137 / 500000000000000000) (-791436950733956908159 / 1000000000000000000) ((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) := bmul (sGlobal36_hz76 hc) (sGlobal36_hz109 hc) (by norm_num) (by norm_num)

theorem sGlobal36_hz111 {c : ℝ} (hc : B (21 / 40) (53 / 100) c) : B (-420049280021899144277 / 500000000000000000) (-158290400371740256887 / 200000000000000000) (((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) := bsub (sGlobal36_hz110 hc) sGlobal36_hz104 (by norm_num) (by norm_num)

theorem sGlobal36_hz112 {c : ℝ} (hc : B (21 / 40) (53 / 100) c) : B (-87859563349792255857 / 100000000000000000) (-414974537654974277283 / 500000000000000000) ((((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) - (s3rs 12225 46 maskSlack)) := bsub (sGlobal36_hz111 hc) sGlobal36_hz29 (by norm_num) (by norm_num)

theorem sGlobal36_hz113 {c : ℝ} (hc : B (21 / 40) (53 / 100) c) : B (-87859563349792255857 / 100000000000000000) (-414974537654974277283 / 500000000000000000) (s3L 12225 46 maskSlack c) := by
    convert (sGlobal36_hz112 hc) using 1 <;>
      norm_num [s3L] <;> ring

theorem sGlobal36_hz114 {c : ℝ} (hc : B (21 / 40) (53 / 100) c) : B 0 (1305163814189610103311 / 1000000000000000000) |(s3U 12225 46 maskSlack c)| := bweaken (babs (sGlobal36_hz107 hc)) (by norm_num) (by norm_num)

theorem sGlobal36_hz115 {c : ℝ} (hc : B (21 / 40) (53 / 100) c) : B 0 (87859563349792255857 / 100000000000000000) |(s3L 12225 46 maskSlack c)| := bweaken (babs (sGlobal36_hz113 hc)) (by norm_num) (by norm_num)

theorem sGlobal36_hz116 {c : ℝ} (hc : B (21 / 40) (53 / 100) c) : B 0 (1305163814189610103311 / 1000000000000000000) (max |(s3U 12225 46 maskSlack c)| |(s3L 12225 46 maskSlack c)|) := bweaken (bmax (sGlobal36_hz114 hc) (sGlobal36_hz115 hc)) (by norm_num) (by norm_num)

theorem sGlobal36_hz117 {c : ℝ} (hc : B (21 / 40) (53 / 100) c) : B 0 (1305163814189610103311 / 1000000000000000000) (s3nks 12225 46 maskSlack c) := by
    convert (sGlobal36_hz116 hc) using 1 <;>
      norm_num [s3nks] <;> ring

theorem sGlobal36 {c : ℝ} (hc : B (21 / 40) (53 / 100) c) :
    0 < s3am 12225 46 ∧ 0 ≤ s3dm 12225 46 c ∧
    s3dm 12225 46 c ^ 2 ≤ 2 * s3ap 12225 46 ^ 2 ∧ s3c1 12225 46 c < 1 ∧
    0 ≤ s3Cpa 12225 c - s3r1 12225 46 ∧
    s3e0 12225 46 ≤ (s3Cpa 12225 c - s3r1 12225 46) / s3ap 12225 46 ∧
    s3nks 12225 46 maskSlack c ≤ 12225 * (53381 / 500000) := by

  refine ⟨lt_of_lt_of_le (by norm_num) sGlobal36_hz14.1,
    le_trans (by norm_num) (sGlobal36_hz64 hc).1, ?_,
    lt_of_le_of_lt (sGlobal36_hz72 hc).2 (by norm_num), ?_, ?_,
    le_trans (sGlobal36_hz117 hc).2 (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (sGlobal36_hz64 hc).1) (sGlobal36_hz64 hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) sGlobal36_hz9.1 2
    nlinarith only [h1, h2]
  · linarith only [(sGlobal36_hz84 hc).1, sGlobal36_hz33.2]
  · have hap : 0 < s3ap 12225 46 := lt_of_lt_of_le (by norm_num) sGlobal36_hz9.1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul sGlobal36_hz16.2 sGlobal36_hz9.2 (le_trans (by norm_num) sGlobal36_hz9.1) (by norm_num)
    linarith only [h, (sGlobal36_hz84 hc).1, sGlobal36_hz33.2]

end BstLean.Part255
