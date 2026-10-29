import BstLean.Part255SGlobal33
import BstLean.Part255Numeric10
namespace BstLean.Part255
open Real BstLean.Part130 BstLean.Part182 BstLean.Part197 BstLean.Part246
theorem sGlobal37_hz0 : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal37_hz1 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) ((√(23 : ℝ)) / (12225 : ℝ)) := bdiv sGlobal37_hz0 (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal37_hz2 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) maskSlack := by
    convert sGlobal37_hz1 using 1 <;>
      norm_num [maskSlack] <;> ring

theorem sGlobal37_hz3 : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal37_hz4 : B (6395294793910793 / 500000000000000000) (12790589587821587 / 1000000000000000000) (√((2 / 12225) : ℝ)) := bsqrt (bpoint ((2 / 12225) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal37_hz5 : B (7230130686979 / 62500000000000000) (23136418198333 / 200000000000000000) (√((2 / 149450625) : ℝ)) := bsqrt (bpoint ((2 / 149450625) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal37_hz6 : B (2211334438749598093 / 20000000000000000) (110566721937479904651 / 1000000000000000000) (√(12225 : ℝ)) := bsqrt (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal37_hz7 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))) := bmul sGlobal37_hz3 sGlobal37_hz4 (by norm_num) (by norm_num)

theorem sGlobal37_hz8 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) ((√(12225 : ℝ)) + ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := badd sGlobal37_hz6 sGlobal37_hz7 (by norm_num) (by norm_num)

theorem sGlobal37_hz9 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) (s3ap 12225 46) := by
    convert sGlobal37_hz8 using 1 <;>
      norm_num [s3ap, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal37_hz10 : B (163599182004089 / 1000000000000000000) (16359918200409 / 100000000000000000) ((2 : ℝ) / (12225 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal37_hz11 : B (1222499983640081799591 / 100000000000000000) (12224999836400817995911 / 1000000000000000000) ((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ))) := bsub (bpoint (12225 : ℝ)) sGlobal37_hz10 (by norm_num) (by norm_num)

theorem sGlobal37_hz12 : B (110566721197658827907 / 1000000000000000000) (27641680299414706977 / 250000000000000000) (√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) := bsqrt sGlobal37_hz11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal37_hz13 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) ((√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) - ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bsub sGlobal37_hz12 sGlobal37_hz7 (by norm_num) (by norm_num)

theorem sGlobal37_hz14 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) (s3am 12225 46) := by
    convert sGlobal37_hz13 using 1 <;>
      norm_num [s3am, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal37_hz15 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√((2 / 12225) : ℝ)) * (√(92 : ℝ))) := bmul sGlobal37_hz4 sGlobal37_hz3 (by norm_num) (by norm_num)

theorem sGlobal37_hz16 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) (s3e0 12225 46) := by
    convert sGlobal37_hz15 using 1 <;>
      norm_num [s3e0, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal37_hz17 : B (250196148528560847 / 500000000000000000) (100078459411424339 / 200000000000000000) (((1 / 2) : ℝ) + maskSlack) := badd (bpoint ((1 / 2) : ℝ)) sGlobal37_hz2 (by norm_num) (by norm_num)

theorem sGlobal37_hz18 : B (59827153232297998295487 / 800000000000000) (23930861292919199366019 / 320000000000000) ((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack)) := bmul (bpoint (149450625 : ℝ)) sGlobal37_hz17 (by norm_num) (by norm_num)

theorem sGlobal37_hz19 : B (1729554180017180009583 / 200000000000000000) (8647770900085900056557 / 1000000000000000000) (√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) := bsqrt sGlobal37_hz18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal37_hz20 : B (4328681281566262743499 / 500000000000000000) (8657362563132525495641 / 1000000000000000000) ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))) := badd sGlobal37_hz19 sGlobal37_hz3 (by norm_num) (by norm_num)

theorem sGlobal37_hz21 : B (110732771457999278473 / 1000000000000000000) (55366385728999643621 / 500000000000000000) ((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ)))) := bmul sGlobal37_hz4 sGlobal37_hz20 (by norm_num) (by norm_num)

theorem sGlobal37_hz22 : B (209099159 / 15625000000000000) (13382346177 / 1000000000000000000) ((2 : ℝ) / (149450625 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (149450625 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal37_hz23 : B (2452349334953899930479 / 200000000000000000) (12261746674769501594427 / 1000000000000000000) (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2) := bsq sGlobal37_hz21 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal37_hz24 : B (82045469362091 / 500000000000000000) (32818187747289 / 200000000000000000) (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2)) := bmul sGlobal37_hz22 sGlobal37_hz23 (by norm_num) (by norm_num)

theorem sGlobal37_hz25 : B (82045469362091 / 250000000000000000) (32818187747289 / 100000000000000000) ((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) := bmul (bpoint (2 : ℝ)) sGlobal37_hz24 (by norm_num) (by norm_num)

theorem sGlobal37_hz26 : B (117258080744995992792057 / 1000000000000000000) (58629040372497996396029 / 500000000000000000) (√(13749457500 : ℝ)) := bsqrt (bpoint (13749457500 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal37_hz27 : B (117304080744995992792057 / 1000000000000000000) (58652040372497996396029 / 500000000000000000) ((√(13749457500 : ℝ)) + (46 : ℝ)) := badd sGlobal37_hz26 (bpoint (46 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal37_hz28 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal37_hz25 sGlobal37_hz27 (by norm_num) (by norm_num)

theorem sGlobal37_hz29 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (s3rs 12225 46 maskSlack) := by
    convert sGlobal37_hz28 using 1 <;>
      norm_num [s3rs, s3pp, s3K, mA, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal37_hz30 : B (490797546012267 / 1000000000000000000) (49079754601227 / 100000000000000000) ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (3 : ℝ)) sGlobal37_hz10 (by norm_num) (by norm_num)

theorem sGlobal37_hz31 : B (490797546012267 / 500000000000000000) (49079754601227 / 50000000000000000) ((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal37_hz30 (by norm_num) (by norm_num)

theorem sGlobal37_hz32 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal37_hz31 sGlobal37_hz27 (by norm_num) (by norm_num)

theorem sGlobal37_hz33 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (s3r1 12225 46) := by
    convert sGlobal37_hz32 using 1 <;>
      norm_num [s3r1, mA] <;> ring

theorem sGlobal37_hz34 : B (163599182004089 / 500000000000000000) (16359918200409 / 50000000000000000) ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (2 : ℝ)) sGlobal37_hz10 (by norm_num) (by norm_num)

theorem sGlobal37_hz35 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal37_hz34 (by norm_num) (by norm_num)

theorem sGlobal37_hz36 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal37_hz35 sGlobal37_hz27 (by norm_num) (by norm_num)

theorem sGlobal37_hz37 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (s3rpp 12225 46) := by
    convert sGlobal37_hz36 using 1 <;>
      norm_num [s3rpp, mA] <;> ring

theorem sGlobal37_hz38 {c : ℝ} (hc : B (53 / 100) (107 / 200) c) : B (53 / 100) (107 / 200) c := hc

theorem sGlobal37_hz39 : B (338904041188233601 / 500000000000000000) (42363005148529649 / 62500000000000000) (kdot ((53 / 100))) := by
    constructor
    · apply bkdot_lower (q := (554246824513826269 / 1000000000000000000)) (a := (126524470181512309 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (138561706128456567 / 250000000000000000)) (a := (101219576145207591 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal37_hz40 : B (2809 / 10000) (2809 / 10000) (((53 / 100) : ℝ)^2) := bsq (bpoint ((53 / 100) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal37_hz41 : B (7191 / 10000) (7191 / 10000) ((1 : ℝ) - (((53 / 100) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal37_hz40 (by norm_num) (by norm_num)

theorem sGlobal37_hz42 : B (84799764150615419 / 100000000000000000) (847997641506154191 / 1000000000000000000) (√((1 : ℝ) - (((53 / 100) : ℝ)^2))) := bsqrt sGlobal37_hz41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal37_hz43 : B (16870377046996679 / 62500000000000000) (53985206550389373 / 200000000000000000) ((√((1 : ℝ) - (((53 / 100) : ℝ)^2))) / Real.pi) := bdiv sGlobal37_hz42 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal37_hz44 : B (359238283659527617 / 1000000000000000000) (11226196364360357 / 31250000000000000) (((53 / 100) : ℝ) * (kdot ((53 / 100)))) := bmul (bpoint ((53 / 100) : ℝ)) sGlobal37_hz39 (by norm_num) (by norm_num)

theorem sGlobal37_hz45 : B (629164316411474481 / 1000000000000000000) (629164316411478289 / 1000000000000000000) (((√((1 : ℝ) - (((53 / 100) : ℝ)^2))) / Real.pi) + (((53 / 100) : ℝ) * (kdot ((53 / 100))))) := badd sGlobal37_hz43 sGlobal37_hz44 (by norm_num) (by norm_num)

theorem sGlobal37_hz46 : B (629164316411474481 / 1000000000000000000) (629164316411478289 / 1000000000000000000) (kappa ((53 / 100))) := by rw [kappa_eq]; exact sGlobal37_hz45

theorem sGlobal37_hz47 : B (679688396740185101 / 1000000000000000000) (169922099185047551 / 250000000000000000) (kdot ((107 / 200))) := by
    constructor
    · apply bkdot_lower (q := (275196110115679693 / 500000000000000000)) (a := (125786072457575369 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (110078444046271877 / 200000000000000000)) (a := (251572144915146731 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal37_hz48 : B (11449 / 40000) (11449 / 40000) (((107 / 200) : ℝ)^2) := bsq (bpoint ((107 / 200) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal37_hz49 : B (28551 / 40000) (28551 / 40000) ((1 : ℝ) - (((107 / 200) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal37_hz48 (by norm_num) (by norm_num)

theorem sGlobal37_hz50 : B (52803253628446041 / 62500000000000000) (844852058055136657 / 1000000000000000000) (√((1 : ℝ) - (((107 / 200) : ℝ)^2))) := bsqrt sGlobal37_hz49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal37_hz51 : B (268924762441671857 / 1000000000000000000) (268924762441671859 / 1000000000000000000) ((√((1 : ℝ) - (((107 / 200) : ℝ)^2))) / Real.pi) := bdiv sGlobal37_hz50 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal37_hz52 : B (363633292255999029 / 1000000000000000000) (2272708076600011 / 6250000000000000) (((107 / 200) : ℝ) * (kdot ((107 / 200)))) := bmul (bpoint ((107 / 200) : ℝ)) sGlobal37_hz47 (by norm_num) (by norm_num)

theorem sGlobal37_hz53 : B (316279027348835443 / 500000000000000000) (632558054697673619 / 1000000000000000000) (((√((1 : ℝ) - (((107 / 200) : ℝ)^2))) / Real.pi) + (((107 / 200) : ℝ) * (kdot ((107 / 200))))) := badd sGlobal37_hz51 sGlobal37_hz52 (by norm_num) (by norm_num)

theorem sGlobal37_hz54 : B (316279027348835443 / 500000000000000000) (632558054697673619 / 1000000000000000000) (kappa ((107 / 200))) := by rw [kappa_eq]; exact sGlobal37_hz53

theorem sGlobal37_hz55 {c : ℝ} (hc : B (53 / 100) (107 / 200) c) : B (629164316411474481 / 1000000000000000000) (632558054697673619 / 1000000000000000000) (kappa c) := bkappa (sGlobal37_hz38 hc) (by norm_num) (by norm_num) sGlobal37_hz46.1 sGlobal37_hz54.2

theorem sGlobal37_hz56 : B 24450 24450 ((2 : ℝ) * (12225 : ℝ)) := bmul (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal37_hz57 {c : ℝ} (hc : B (53 / 100) (107 / 200) c) : B (367441945302326381 / 1000000000000000000) (370835683588525519 / 1000000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (sGlobal37_hz55 hc) (by norm_num) (by norm_num)

theorem sGlobal37_hz58 {c : ℝ} (hc : B (53 / 100) (107 / 200) c) : B (179679111252837600309 / 20000000000000000) (181338649274788978791 / 20000000000000000) (((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) := bmul sGlobal37_hz56 (sGlobal37_hz57 hc) (by norm_num) (by norm_num)

theorem sGlobal37_hz59 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (4 : ℝ)) sGlobal37_hz10 (by norm_num) (by norm_num)

theorem sGlobal37_hz60 {c : ℝ} (hc : B (53 / 100) (107 / 200) c) : B (898395490824515199909 / 100000000000000000) (4533465904671360461597 / 500000000000000000) ((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bsub (sGlobal37_hz58 hc) sGlobal37_hz59 (by norm_num) (by norm_num)

theorem sGlobal37_hz61 {c : ℝ} (hc : B (53 / 100) (107 / 200) c) : B (94783727022338343999 / 1000000000000000000) (95220437981258629177 / 1000000000000000000) (√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) := bsqrt (sGlobal37_hz60 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal37_hz62 : B (30670756373515103 / 125000000000000000) (122683025494060423 / 500000000000000000) ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal37_hz7 (by norm_num) (by norm_num)

theorem sGlobal37_hz63 {c : ℝ} (hc : B (53 / 100) (107 / 200) c) : B (94538360971350223153 / 1000000000000000000) (94975071930270508353 / 1000000000000000000) ((√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) - ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))))) := bsub (sGlobal37_hz61 hc) sGlobal37_hz62 (by norm_num) (by norm_num)

theorem sGlobal37_hz64 {c : ℝ} (hc : B (53 / 100) (107 / 200) c) : B (94538360971350223153 / 1000000000000000000) (94975071930270508353 / 1000000000000000000) (s3dm 12225 46 c) := by
    convert (sGlobal37_hz63 hc) using 1 <;>
      norm_num [s3dm, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal37_hz65 : B (6126072185528622723889 / 500000000000000000) (2450428874211449090087 / 200000000000000000) ((s3ap 12225 46)^2) := bsq sGlobal37_hz9 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal37_hz66 : B (6126072185528622723889 / 250000000000000000) (2450428874211449090087 / 100000000000000000) ((2 : ℝ) * ((s3ap 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal37_hz65 (by norm_num) (by norm_num)

theorem sGlobal37_hz67 {c : ℝ} (hc : B (53 / 100) (107 / 200) c) : B (4468750847574657554279 / 500000000000000000) (2255066072040014256367 / 250000000000000000) ((s3dm 12225 46 c)^2) := bsq (sGlobal37_hz64 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal37_hz68 {c : ℝ} (hc : B (53 / 100) (107 / 200) c) : B (1935503056744304233761 / 125000000000000000) (1945848380870646974039 / 125000000000000000) (((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) := bsub sGlobal37_hz66 (sGlobal37_hz67 hc) (by norm_num) (by norm_num)

theorem sGlobal37_hz69 : B (1524735695971823534271 / 125000000000000000) (609894278388729413841 / 50000000000000000) ((s3am 12225 46)^2) := bsq sGlobal37_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal37_hz70 : B (1524735695971823534271 / 62500000000000000) (609894278388729413841 / 25000000000000000) ((2 : ℝ) * ((s3am 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal37_hz69 (by norm_num) (by norm_num)

theorem sGlobal37_hz71 {c : ℝ} (hc : B (53 / 100) (107 / 200) c) : B (317350584409101337 / 500000000000000000) (319046833167767167 / 500000000000000000) ((((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) / ((2 : ℝ) * ((s3am 12225 46)^2))) := bdiv (sGlobal37_hz68 hc) sGlobal37_hz70 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal37_hz72 {c : ℝ} (hc : B (53 / 100) (107 / 200) c) : B (317350584409101337 / 500000000000000000) (319046833167767167 / 500000000000000000) (s3c1 12225 46 c) := by
    convert (sGlobal37_hz71 hc) using 1 <;>
      norm_num [s3c1] <;> ring

theorem sGlobal37_hz73 {c : ℝ} (hc : B (53 / 100) (107 / 200) c) : B (338904041188233601 / 500000000000000000) (169922099185047551 / 250000000000000000) (kdot c) := bkdot (sGlobal37_hz38 hc) sGlobal37_hz39.1 sGlobal37_hz47.2

theorem sGlobal37_hz74 : B (71887680133090127 / 100000000000000000) (179719200332725319 / 250000000000000000) (kdot ((317350584409101337 / 500000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (236360532142933239 / 500000000000000000)) (a := (220793643923126127 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (472721064285866477 / 1000000000000000000)) (a := (441587287846252247 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal37_hz75 : B (360138376202906741 / 500000000000000000) (360138376202906743 / 500000000000000000) (kdot ((319046833167767167 / 500000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (235016703686822903 / 500000000000000000)) (a := (13730882807502737 / 31250000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (94006681474729161 / 200000000000000000)) (a := (439388249840087579 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal37_hz76 {c : ℝ} (hc : B (53 / 100) (107 / 200) c) : B (71887680133090127 / 100000000000000000) (360138376202906743 / 500000000000000000) (kdot (s3c1 12225 46 c)) := bkdot (sGlobal37_hz72 hc) sGlobal37_hz74.1 sGlobal37_hz75.2

theorem sGlobal37_hz77 {c : ℝ} (hc : B (53 / 100) (107 / 200) c) : B (2809 / 10000) (11449 / 40000) (c^2) := bsq (sGlobal37_hz38 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal37_hz78 {c : ℝ} (hc : B (53 / 100) (107 / 200) c) : B (28551 / 40000) (7191 / 10000) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (sGlobal37_hz77 hc) (by norm_num) (by norm_num)

theorem sGlobal37_hz79 {c : ℝ} (hc : B (53 / 100) (107 / 200) c) : B (52803253628446041 / 62500000000000000) (847997641506154191 / 1000000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (sGlobal37_hz78 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal37_hz80 : B (39119999999999765769 / 1600000000000000) (3912000000000000489 / 160000000000000) ((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (149450625 : ℝ)) sGlobal37_hz10 (by norm_num) (by norm_num)

theorem sGlobal37_hz81 {c : ℝ} (hc : B (53 / 100) (107 / 200) c) : B (572647553362163917 / 1000000000000000000) (288187078697390257 / 500000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (sGlobal37_hz79 hc) (sGlobal37_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal37_hz82 {c : ℝ} (hc : B (53 / 100) (107 / 200) c) : B (14001232679704823938269 / 1000000000000000000) (3523087037075596332211 / 250000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) := bmul sGlobal37_hz80 (sGlobal37_hz81 hc) (by norm_num) (by norm_num)

theorem sGlobal37_hz83 {c : ℝ} (hc : B (53 / 100) (107 / 200) c) : B (3500308169926205984567 / 500000000000000000) (3523087037075596332211 / 500000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) / (2 : ℝ)) := bdiv (sGlobal37_hz82 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal37_hz84 {c : ℝ} (hc : B (53 / 100) (107 / 200) c) : B (3500308169926205984567 / 500000000000000000) (3523087037075596332211 / 500000000000000000) (s3Cpa 12225 c) := by
    convert (sGlobal37_hz83 hc) using 1 <;>
      norm_num [s3Cpa, mA] <;> ring

theorem sGlobal37_hz85 {c : ℝ} (hc : B (53 / 100) (107 / 200) c) : B (268924762441671857 / 1000000000000000000) (53985206550389373 / 200000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (sGlobal37_hz79 hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal37_hz86 {c : ℝ} (hc : B (53 / 100) (107 / 200) c) : B (359238283659527617 / 1000000000000000000) (2272708076600011 / 6250000000000000) (c * (kdot c)) := bmul (sGlobal37_hz38 hc) (sGlobal37_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal37_hz87 {c : ℝ} (hc : B (53 / 100) (107 / 200) c) : B (-94708529814329903 / 1000000000000000000) (-5582015681723797 / 62500000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (sGlobal37_hz85 hc) (sGlobal37_hz86 hc) (by norm_num) (by norm_num)

theorem sGlobal37_hz88 {c : ℝ} (hc : B (53 / 100) (107 / 200) c) : B (-2315623553960366417803 / 1000000000000000000) (-545921133672584077897 / 250000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) := bmul sGlobal37_hz80 (sGlobal37_hz87 hc) (by norm_num) (by norm_num)

theorem sGlobal37_hz89 {c : ℝ} (hc : B (53 / 100) (107 / 200) c) : B (-578905888490091604451 / 500000000000000000) (-545921133672584077897 / 500000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) / (2 : ℝ)) := bdiv (sGlobal37_hz88 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal37_hz90 {c : ℝ} (hc : B (53 / 100) (107 / 200) c) : B (-578905888490091604451 / 500000000000000000) (-545921133672584077897 / 500000000000000000) (s3Cpp 12225 c) := by
    convert (sGlobal37_hz89 hc) using 1 <;>
      norm_num [s3Cpp, mA] <;> ring

theorem sGlobal37_hz91 {c : ℝ} (hc : B (53 / 100) (107 / 200) c) : B (1423152289957229935507 / 200000000000000000) (895164898010616384581 / 125000000000000000) ((s3Cpa 12225 c) + (s3r1 12225 46)) := badd (sGlobal37_hz84 hc) sGlobal37_hz33 (by norm_num) (by norm_num)

theorem sGlobal37_hz92 {c : ℝ} (hc : B (53 / 100) (107 / 200) c) : B (32214330295917848941 / 500000000000000000) (32420578342678707621 / 500000000000000000) (((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) := bdiv (sGlobal37_hz91 hc) sGlobal37_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal37_hz93 {c : ℝ} (hc : B (53 / 100) (107 / 200) c) : B (32275671808664879147 / 500000000000000000) (12992767942170295133 / 200000000000000000) ((((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) + (s3e0 12225 46)) := badd (sGlobal37_hz92 hc) sGlobal37_hz16 (by norm_num) (by norm_num)

theorem sGlobal37_hz94 {c : ℝ} (hc : B (53 / 100) (107 / 200) c) : B (32275671808664879147 / 500000000000000000) (12992767942170295133 / 200000000000000000) (s3Lam 12225 46 c) := by
    convert (sGlobal37_hz93 hc) using 1 <;>
      norm_num [s3Lam] <;> ring

theorem sGlobal37_hz95 {c : ℝ} (hc : B (53 / 100) (107 / 200) c) : B (-540524185178845701651 / 500000000000000000) (-63442428795167242561 / 62500000000000000) ((s3Cpp 12225 c) + (s3rpp 12225 46)) := badd (sGlobal37_hz90 hc) sGlobal37_hz37 (by norm_num) (by norm_num)

theorem sGlobal37_hz96 {c : ℝ} (hc : B (53 / 100) (107 / 200) c) : B (-778654009394835049899 / 1000000000000000000) (-63442428795167242561 / 125000000000000000) (if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) := bweaken (bfirst (sGlobal37_hz95 hc) (sGlobal37_hz76 hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem sGlobal37_hz97 {c : ℝ} (hc : B (53 / 100) (107 / 200) c) : B (2083437981401289662291 / 500000000000000000) (4220300469977203141337 / 1000000000000000000) ((s3Lam 12225 46 c)^2) := bsq (sGlobal37_hz94 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal37_hz98 {c : ℝ} (hc : B (53 / 100) (107 / 200) c) : B (40284557369919261 / 100000000000000000) (407163527017524223 / 1000000000000000000) ((s3c1 12225 46 c)^2) := bsq (sGlobal37_hz72 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal37_hz99 {c : ℝ} (hc : B (53 / 100) (107 / 200) c) : B (592836472982475777 / 1000000000000000000) (59715442630080739 / 100000000000000000) ((1 : ℝ) - ((s3c1 12225 46 c)^2)) := bsub (bpoint (1 : ℝ)) (sGlobal37_hz98 hc) (by norm_num) (by norm_num)

theorem sGlobal37_hz100 {c : ℝ} (hc : B (53 / 100) (107 / 200) c) : B (192489686896219809 / 250000000000000000) (24148677384784083 / 31250000000000000) (√((1 : ℝ) - ((s3c1 12225 46 c)^2))) := bsqrt (sGlobal37_hz99 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal37_hz101 {c : ℝ} (hc : B (53 / 100) (107 / 200) c) : B (604724186244963641 / 250000000000000000) (1213844919455162493 / 500000000000000000) (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))) := bmul pi_mem (sGlobal37_hz100 hc) (by norm_num) (by norm_num)

theorem sGlobal37_hz102 {c : ℝ} (hc : B (53 / 100) (107 / 200) c) : B (26818679995799606529 / 15625000000000000) (6815317249511511211 / 3906250000000000) (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2))))) := bdiv (sGlobal37_hz97 hc) (sGlobal37_hz101 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal37_hz103 {c : ℝ} (hc : B (53 / 100) (107 / 200) c) : B (937741510336339767957 / 1000000000000000000) (154647723189201116191 / 125000000000000000) ((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) := badd (sGlobal37_hz96 hc) (sGlobal37_hz102 hc) (by norm_num) (by norm_num)

theorem sGlobal37_hz104 : B (3762781186094069 / 250000000000000000) (376278118609407 / 25000000000000000) ((s3e0 12225 46)^2) := bsq sGlobal37_hz16 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal37_hz105 {c : ℝ} (hc : B (53 / 100) (107 / 200) c) : B (937756561461084144233 / 1000000000000000000) (77324802289897081613 / 62500000000000000) (((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) := badd (sGlobal37_hz103 hc) sGlobal37_hz104 (by norm_num) (by norm_num)

theorem sGlobal37_hz106 {c : ℝ} (hc : B (53 / 100) (107 / 200) c) : B (244063408728082853591 / 250000000000000000) (79730869380779848489 / 62500000000000000) ((((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) + (s3rs 12225 46 maskSlack)) := badd (sGlobal37_hz105 hc) sGlobal37_hz29 (by norm_num) (by norm_num)

theorem sGlobal37_hz107 {c : ℝ} (hc : B (53 / 100) (107 / 200) c) : B (244063408728082853591 / 250000000000000000) (79730869380779848489 / 62500000000000000) (s3U 12225 46 maskSlack c) := by
    convert (sGlobal37_hz106 hc) using 1 <;>
      norm_num [s3U] <;> ring

theorem sGlobal37_hz108 {c : ℝ} (hc : B (53 / 100) (107 / 200) c) : B (-30864379590066887093 / 25000000000000000) (-584302836983829980697 / 500000000000000000) ((s3Cpp 12225 c) - (s3rpp 12225 46)) := bsub (sGlobal37_hz90 hc) sGlobal37_hz37 (by norm_num) (by norm_num)

theorem sGlobal37_hz109 {c : ℝ} (hc : B (53 / 100) (107 / 200) c) : B (-30864379590066887093 / 25000000000000000) (-584302836983829980697 / 500000000000000000) (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ)) := bweaken (bmin (sGlobal37_hz108 hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem sGlobal37_hz110 {c : ℝ} (hc : B (53 / 100) (107 / 200) c) : B (-889235803846146014911 / 1000000000000000000) (-840083508919013472147 / 1000000000000000000) ((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) := bmul (sGlobal37_hz76 hc) (sGlobal37_hz109 hc) (by norm_num) (by norm_num)

theorem sGlobal37_hz111 {c : ℝ} (hc : B (53 / 100) (107 / 200) c) : B (-889250854970890391191 / 1000000000000000000) (-840098560043757848423 / 1000000000000000000) (((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) := bsub (sGlobal37_hz110 hc) sGlobal37_hz104 (by norm_num) (by norm_num)

theorem sGlobal37_hz112 {c : ℝ} (hc : B (53 / 100) (107 / 200) c) : B (-927747928425014661207 / 1000000000000000000) (-439297816747502559277 / 500000000000000000) ((((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) - (s3rs 12225 46 maskSlack)) := bsub (sGlobal37_hz111 hc) sGlobal37_hz29 (by norm_num) (by norm_num)

theorem sGlobal37_hz113 {c : ℝ} (hc : B (53 / 100) (107 / 200) c) : B (-927747928425014661207 / 1000000000000000000) (-439297816747502559277 / 500000000000000000) (s3L 12225 46 maskSlack c) := by
    convert (sGlobal37_hz112 hc) using 1 <;>
      norm_num [s3L] <;> ring

theorem sGlobal37_hz114 {c : ℝ} (hc : B (53 / 100) (107 / 200) c) : B 0 (79730869380779848489 / 62500000000000000) |(s3U 12225 46 maskSlack c)| := bweaken (babs (sGlobal37_hz107 hc)) (by norm_num) (by norm_num)

theorem sGlobal37_hz115 {c : ℝ} (hc : B (53 / 100) (107 / 200) c) : B 0 (927747928425014661207 / 1000000000000000000) |(s3L 12225 46 maskSlack c)| := bweaken (babs (sGlobal37_hz113 hc)) (by norm_num) (by norm_num)

theorem sGlobal37_hz116 {c : ℝ} (hc : B (53 / 100) (107 / 200) c) : B 0 (79730869380779848489 / 62500000000000000) (max |(s3U 12225 46 maskSlack c)| |(s3L 12225 46 maskSlack c)|) := bweaken (bmax (sGlobal37_hz114 hc) (sGlobal37_hz115 hc)) (by norm_num) (by norm_num)

theorem sGlobal37_hz117 {c : ℝ} (hc : B (53 / 100) (107 / 200) c) : B 0 (79730869380779848489 / 62500000000000000) (s3nks 12225 46 maskSlack c) := by
    convert (sGlobal37_hz116 hc) using 1 <;>
      norm_num [s3nks] <;> ring

theorem sGlobal37 {c : ℝ} (hc : B (53 / 100) (107 / 200) c) :
    0 < s3am 12225 46 ∧ 0 ≤ s3dm 12225 46 c ∧
    s3dm 12225 46 c ^ 2 ≤ 2 * s3ap 12225 46 ^ 2 ∧ s3c1 12225 46 c < 1 ∧
    0 ≤ s3Cpa 12225 c - s3r1 12225 46 ∧
    s3e0 12225 46 ≤ (s3Cpa 12225 c - s3r1 12225 46) / s3ap 12225 46 ∧
    s3nks 12225 46 maskSlack c ≤ 12225 * (3261 / 31250) := by

  refine ⟨lt_of_lt_of_le (by norm_num) sGlobal37_hz14.1,
    le_trans (by norm_num) (sGlobal37_hz64 hc).1, ?_,
    lt_of_le_of_lt (sGlobal37_hz72 hc).2 (by norm_num), ?_, ?_,
    le_trans (sGlobal37_hz117 hc).2 (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (sGlobal37_hz64 hc).1) (sGlobal37_hz64 hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) sGlobal37_hz9.1 2
    nlinarith only [h1, h2]
  · linarith only [(sGlobal37_hz84 hc).1, sGlobal37_hz33.2]
  · have hap : 0 < s3ap 12225 46 := lt_of_lt_of_le (by norm_num) sGlobal37_hz9.1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul sGlobal37_hz16.2 sGlobal37_hz9.2 (le_trans (by norm_num) sGlobal37_hz9.1) (by norm_num)
    linarith only [h, (sGlobal37_hz84 hc).1, sGlobal37_hz33.2]

end BstLean.Part255
