import BstLean.Part255SGlobal11
import BstLean.Part255Numeric10
namespace BstLean.Part255
open Real BstLean.Part130 BstLean.Part182 BstLean.Part197 BstLean.Part246
theorem sGlobal15_hz0 : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal15_hz1 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) ((√(23 : ℝ)) / (12225 : ℝ)) := bdiv sGlobal15_hz0 (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal15_hz2 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) maskSlack := by
    convert sGlobal15_hz1 using 1 <;>
      norm_num [maskSlack] <;> ring

theorem sGlobal15_hz3 : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal15_hz4 : B (6395294793910793 / 500000000000000000) (12790589587821587 / 1000000000000000000) (√((2 / 12225) : ℝ)) := bsqrt (bpoint ((2 / 12225) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal15_hz5 : B (7230130686979 / 62500000000000000) (23136418198333 / 200000000000000000) (√((2 / 149450625) : ℝ)) := bsqrt (bpoint ((2 / 149450625) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal15_hz6 : B (2211334438749598093 / 20000000000000000) (110566721937479904651 / 1000000000000000000) (√(12225 : ℝ)) := bsqrt (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal15_hz7 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))) := bmul sGlobal15_hz3 sGlobal15_hz4 (by norm_num) (by norm_num)

theorem sGlobal15_hz8 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) ((√(12225 : ℝ)) + ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := badd sGlobal15_hz6 sGlobal15_hz7 (by norm_num) (by norm_num)

theorem sGlobal15_hz9 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) (s3ap 12225 46) := by
    convert sGlobal15_hz8 using 1 <;>
      norm_num [s3ap, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal15_hz10 : B (163599182004089 / 1000000000000000000) (16359918200409 / 100000000000000000) ((2 : ℝ) / (12225 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal15_hz11 : B (1222499983640081799591 / 100000000000000000) (12224999836400817995911 / 1000000000000000000) ((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ))) := bsub (bpoint (12225 : ℝ)) sGlobal15_hz10 (by norm_num) (by norm_num)

theorem sGlobal15_hz12 : B (110566721197658827907 / 1000000000000000000) (27641680299414706977 / 250000000000000000) (√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) := bsqrt sGlobal15_hz11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal15_hz13 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) ((√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) - ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bsub sGlobal15_hz12 sGlobal15_hz7 (by norm_num) (by norm_num)

theorem sGlobal15_hz14 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) (s3am 12225 46) := by
    convert sGlobal15_hz13 using 1 <;>
      norm_num [s3am, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal15_hz15 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√((2 / 12225) : ℝ)) * (√(92 : ℝ))) := bmul sGlobal15_hz4 sGlobal15_hz3 (by norm_num) (by norm_num)

theorem sGlobal15_hz16 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) (s3e0 12225 46) := by
    convert sGlobal15_hz15 using 1 <;>
      norm_num [s3e0, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal15_hz17 : B (250196148528560847 / 500000000000000000) (100078459411424339 / 200000000000000000) (((1 / 2) : ℝ) + maskSlack) := badd (bpoint ((1 / 2) : ℝ)) sGlobal15_hz2 (by norm_num) (by norm_num)

theorem sGlobal15_hz18 : B (59827153232297998295487 / 800000000000000) (23930861292919199366019 / 320000000000000) ((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack)) := bmul (bpoint (149450625 : ℝ)) sGlobal15_hz17 (by norm_num) (by norm_num)

theorem sGlobal15_hz19 : B (1729554180017180009583 / 200000000000000000) (8647770900085900056557 / 1000000000000000000) (√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) := bsqrt sGlobal15_hz18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal15_hz20 : B (4328681281566262743499 / 500000000000000000) (8657362563132525495641 / 1000000000000000000) ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))) := badd sGlobal15_hz19 sGlobal15_hz3 (by norm_num) (by norm_num)

theorem sGlobal15_hz21 : B (110732771457999278473 / 1000000000000000000) (55366385728999643621 / 500000000000000000) ((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ)))) := bmul sGlobal15_hz4 sGlobal15_hz20 (by norm_num) (by norm_num)

theorem sGlobal15_hz22 : B (209099159 / 15625000000000000) (13382346177 / 1000000000000000000) ((2 : ℝ) / (149450625 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (149450625 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal15_hz23 : B (2452349334953899930479 / 200000000000000000) (12261746674769501594427 / 1000000000000000000) (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2) := bsq sGlobal15_hz21 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal15_hz24 : B (82045469362091 / 500000000000000000) (32818187747289 / 200000000000000000) (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2)) := bmul sGlobal15_hz22 sGlobal15_hz23 (by norm_num) (by norm_num)

theorem sGlobal15_hz25 : B (82045469362091 / 250000000000000000) (32818187747289 / 100000000000000000) ((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) := bmul (bpoint (2 : ℝ)) sGlobal15_hz24 (by norm_num) (by norm_num)

theorem sGlobal15_hz26 : B (117258080744995992792057 / 1000000000000000000) (58629040372497996396029 / 500000000000000000) (√(13749457500 : ℝ)) := bsqrt (bpoint (13749457500 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal15_hz27 : B (117304080744995992792057 / 1000000000000000000) (58652040372497996396029 / 500000000000000000) ((√(13749457500 : ℝ)) + (46 : ℝ)) := badd sGlobal15_hz26 (bpoint (46 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal15_hz28 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal15_hz25 sGlobal15_hz27 (by norm_num) (by norm_num)

theorem sGlobal15_hz29 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (s3rs 12225 46 maskSlack) := by
    convert sGlobal15_hz28 using 1 <;>
      norm_num [s3rs, s3pp, s3K, mA, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal15_hz30 : B (490797546012267 / 1000000000000000000) (49079754601227 / 100000000000000000) ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (3 : ℝ)) sGlobal15_hz10 (by norm_num) (by norm_num)

theorem sGlobal15_hz31 : B (490797546012267 / 500000000000000000) (49079754601227 / 50000000000000000) ((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal15_hz30 (by norm_num) (by norm_num)

theorem sGlobal15_hz32 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal15_hz31 sGlobal15_hz27 (by norm_num) (by norm_num)

theorem sGlobal15_hz33 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (s3r1 12225 46) := by
    convert sGlobal15_hz32 using 1 <;>
      norm_num [s3r1, mA] <;> ring

theorem sGlobal15_hz34 : B (163599182004089 / 500000000000000000) (16359918200409 / 50000000000000000) ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (2 : ℝ)) sGlobal15_hz10 (by norm_num) (by norm_num)

theorem sGlobal15_hz35 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal15_hz34 (by norm_num) (by norm_num)

theorem sGlobal15_hz36 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal15_hz35 sGlobal15_hz27 (by norm_num) (by norm_num)

theorem sGlobal15_hz37 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (s3rpp 12225 46) := by
    convert sGlobal15_hz36 using 1 <;>
      norm_num [s3rpp, mA] <;> ring

theorem sGlobal15_hz38 {c : ℝ} (hc : B (21 / 50) (17 / 40) c) : B (21 / 50) (17 / 40) c := hc

theorem sGlobal15_hz39 : B (12759398609945091 / 20000000000000000) (318984965252487437 / 500000000000000000) (kdot ((21 / 50))) := by
    constructor
    · apply bkdot_lower (q := (127820296389165381 / 200000000000000000)) (a := (284337751682106839 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (79887685243228363 / 125000000000000000)) (a := (284337751676043311 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal15_hz40 : B (441 / 2500) (441 / 2500) (((21 / 50) : ℝ)^2) := bsq (bpoint ((21 / 50) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal15_hz41 : B (2059 / 2500) (2059 / 2500) ((1 : ℝ) - (((21 / 50) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal15_hz40 (by norm_num) (by norm_num)

theorem sGlobal15_hz42 : B (226881026090768551 / 250000000000000000) (181504820872614841 / 200000000000000000) (√((1 : ℝ) - (((21 / 50) : ℝ)^2))) := bsqrt sGlobal15_hz41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal15_hz43 : B (288873894368856717 / 1000000000000000000) (144436947184428359 / 500000000000000000) ((√((1 : ℝ) - (((21 / 50) : ℝ)^2))) / Real.pi) := bdiv sGlobal15_hz42 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal15_hz44 : B (267947370808846911 / 1000000000000000000) (33493421351511181 / 125000000000000000) (((21 / 50) : ℝ) * (kdot ((21 / 50)))) := bmul (bpoint ((21 / 50) : ℝ)) sGlobal15_hz39 (by norm_num) (by norm_num)

theorem sGlobal15_hz45 : B (139205316294425907 / 250000000000000000) (278410632590473083 / 500000000000000000) (((√((1 : ℝ) - (((21 / 50) : ℝ)^2))) / Real.pi) + (((21 / 50) : ℝ) * (kdot ((21 / 50))))) := badd sGlobal15_hz43 sGlobal15_hz44 (by norm_num) (by norm_num)

theorem sGlobal15_hz46 : B (139205316294425907 / 250000000000000000) (278410632590473083 / 500000000000000000) (kappa ((21 / 50))) := by rw [kappa_eq]; exact sGlobal15_hz45

theorem sGlobal15_hz47 : B (639725907846664981 / 1000000000000000000) (319862953926197211 / 500000000000000000) (kdot ((17 / 40))) := by
    constructor
    · apply bkdot_lower (q := (635223403166023601 / 1000000000000000000)) (a := (282958610296912367 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (1588058507915059 / 2500000000000000)) (a := (565917220584824951 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal15_hz48 : B (289 / 1600) (289 / 1600) (((17 / 40) : ℝ)^2) := bsq (bpoint ((17 / 40) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal15_hz49 : B (1311 / 1600) (1311 / 1600) ((1 : ℝ) - (((17 / 40) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal15_hz48 (by norm_num) (by norm_num)

theorem sGlobal15_hz50 : B (90519334951158363 / 100000000000000000) (905193349511583631 / 1000000000000000000) (√((1 : ℝ) - (((17 / 40) : ℝ)^2))) := bsqrt sGlobal15_hz49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal15_hz51 : B (144065996028678217 / 500000000000000000) (57626398411471287 / 200000000000000000) ((√((1 : ℝ) - (((17 / 40) : ℝ)^2))) / Real.pi) := bdiv sGlobal15_hz50 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal15_hz52 : B (33985438854354077 / 125000000000000000) (27188351083726763 / 100000000000000000) (((17 / 40) : ℝ) * (kdot ((17 / 40)))) := bmul (bpoint ((17 / 40) : ℝ)) sGlobal15_hz47 (by norm_num) (by norm_num)

theorem sGlobal15_hz53 : B (11200310057843781 / 20000000000000000) (112003100578924813 / 200000000000000000) (((√((1 : ℝ) - (((17 / 40) : ℝ)^2))) / Real.pi) + (((17 / 40) : ℝ) * (kdot ((17 / 40))))) := badd sGlobal15_hz51 sGlobal15_hz52 (by norm_num) (by norm_num)

theorem sGlobal15_hz54 : B (11200310057843781 / 20000000000000000) (112003100578924813 / 200000000000000000) (kappa ((17 / 40))) := by rw [kappa_eq]; exact sGlobal15_hz53

theorem sGlobal15_hz55 {c : ℝ} (hc : B (21 / 50) (17 / 40) c) : B (139205316294425907 / 250000000000000000) (112003100578924813 / 200000000000000000) (kappa c) := bkappa (sGlobal15_hz38 hc) (by norm_num) (by norm_num) sGlobal15_hz46.1 sGlobal15_hz54.2

theorem sGlobal15_hz56 : B 24450 24450 ((2 : ℝ) * (12225 : ℝ)) := bmul (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal15_hz57 {c : ℝ} (hc : B (21 / 50) (17 / 40) c) : B (87996899421075187 / 200000000000000000) (110794683705574093 / 250000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (sGlobal15_hz55 hc) (by norm_num) (by norm_num)

theorem sGlobal15_hz58 {c : ℝ} (hc : B (21 / 50) (17 / 40) c) : B (43030483816905766443 / 4000000000000000) (54178600332025731477 / 5000000000000000) (((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) := bmul sGlobal15_hz56 (sGlobal15_hz57 hc) (by norm_num) (by norm_num)

theorem sGlobal15_hz59 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (4 : ℝ)) sGlobal15_hz10 (by norm_num) (by norm_num)

theorem sGlobal15_hz60 {c : ℝ} (hc : B (21 / 50) (17 / 40) c) : B (1075762029982971359439 / 100000000000000000) (2708929853002104569761 / 250000000000000000) ((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bsub (sGlobal15_hz58 hc) sGlobal15_hz59 (by norm_num) (by norm_num)

theorem sGlobal15_hz61 {c : ℝ} (hc : B (21 / 50) (17 / 40) c) : B (25929737151374232541 / 250000000000000000) (52047380846706441831 / 500000000000000000) (√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) := bsqrt (sGlobal15_hz60 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal15_hz62 : B (30670756373515103 / 125000000000000000) (122683025494060423 / 500000000000000000) ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal15_hz7 (by norm_num) (by norm_num)

theorem sGlobal15_hz63 {c : ℝ} (hc : B (21 / 50) (17 / 40) c) : B (51736791277254404659 / 500000000000000000) (51924697821212381419 / 500000000000000000) ((√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) - ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))))) := bsub (sGlobal15_hz61 hc) sGlobal15_hz62 (by norm_num) (by norm_num)

theorem sGlobal15_hz64 {c : ℝ} (hc : B (21 / 50) (17 / 40) c) : B (51736791277254404659 / 500000000000000000) (51924697821212381419 / 500000000000000000) (s3dm 12225 46 c) := by
    convert (sGlobal15_hz63 hc) using 1 <;>
      norm_num [s3dm, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal15_hz65 : B (6126072185528622723889 / 500000000000000000) (2450428874211449090087 / 200000000000000000) ((s3ap 12225 46)^2) := bsq sGlobal15_hz9 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal15_hz66 : B (6126072185528622723889 / 250000000000000000) (2450428874211449090087 / 100000000000000000) ((2 : ℝ) * ((s3ap 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal15_hz65 (by norm_num) (by norm_num)

theorem sGlobal15_hz67 {c : ℝ} (hc : B (21 / 50) (17 / 40) c) : B (1338347785833093726107 / 125000000000000000) (53923484876484356601 / 5000000000000000) ((s3dm 12225 46 c)^2) := bsq (sGlobal15_hz64 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal15_hz68 {c : ℝ} (hc : B (21 / 50) (17 / 40) c) : B (3429897941704404893839 / 250000000000000000) (6898753227724870546007 / 500000000000000000) (((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) := bsub sGlobal15_hz66 (sGlobal15_hz67 hc) (by norm_num) (by norm_num)

theorem sGlobal15_hz69 : B (1524735695971823534271 / 125000000000000000) (609894278388729413841 / 50000000000000000) ((s3am 12225 46)^2) := bsq sGlobal15_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal15_hz70 : B (1524735695971823534271 / 62500000000000000) (609894278388729413841 / 25000000000000000) ((2 : ℝ) * ((s3am 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal15_hz69 (by norm_num) (by norm_num)

theorem sGlobal15_hz71 {c : ℝ} (hc : B (21 / 50) (17 / 40) c) : B (140593954691860737 / 250000000000000000) (565569597238277401 / 1000000000000000000) ((((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) / ((2 : ℝ) * ((s3am 12225 46)^2))) := bdiv (sGlobal15_hz68 hc) sGlobal15_hz70 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal15_hz72 {c : ℝ} (hc : B (21 / 50) (17 / 40) c) : B (140593954691860737 / 250000000000000000) (565569597238277401 / 1000000000000000000) (s3c1 12225 46 c) := by
    convert (sGlobal15_hz71 hc) using 1 <;>
      norm_num [s3c1] <;> ring

theorem sGlobal15_hz73 {c : ℝ} (hc : B (21 / 50) (17 / 40) c) : B (12759398609945091 / 20000000000000000) (319862953926197211 / 500000000000000000) (kdot c) := bkdot (sGlobal15_hz38 hc) sGlobal15_hz39.1 sGlobal15_hz47.2

theorem sGlobal15_hz74 : B (690112562217158779 / 1000000000000000000) (69011256221715953 / 100000000000000000) (kdot ((140593954691860737 / 250000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (529246386243106379 / 1000000000000000000)) (a := (486770048989169051 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (264623193121553189 / 500000000000000000)) (a := (243385024494583937 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal15_hz75 : B (691343636173493227 / 1000000000000000000) (10802244315210841 / 15625000000000000) (kdot ((565569597238277401 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (263386748111013947 / 500000000000000000)) (a := (484836282540546039 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (526773496222027893 / 1000000000000000000)) (a := (484836282540545103 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal15_hz76 {c : ℝ} (hc : B (21 / 50) (17 / 40) c) : B (690112562217158779 / 1000000000000000000) (10802244315210841 / 15625000000000000) (kdot (s3c1 12225 46 c)) := bkdot (sGlobal15_hz72 hc) sGlobal15_hz74.1 sGlobal15_hz75.2

theorem sGlobal15_hz77 {c : ℝ} (hc : B (21 / 50) (17 / 40) c) : B (441 / 2500) (289 / 1600) (c^2) := bsq (sGlobal15_hz38 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal15_hz78 {c : ℝ} (hc : B (21 / 50) (17 / 40) c) : B (1311 / 1600) (2059 / 2500) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (sGlobal15_hz77 hc) (by norm_num) (by norm_num)

theorem sGlobal15_hz79 {c : ℝ} (hc : B (21 / 50) (17 / 40) c) : B (90519334951158363 / 100000000000000000) (181504820872614841 / 200000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (sGlobal15_hz78 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal15_hz80 : B (39119999999999765769 / 1600000000000000) (3912000000000000489 / 160000000000000) ((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (149450625 : ℝ)) sGlobal15_hz10 (by norm_num) (by norm_num)

theorem sGlobal15_hz81 {c : ℝ} (hc : B (21 / 50) (17 / 40) c) : B (288743069137241027 / 500000000000000000) (145141670390399697 / 250000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (sGlobal15_hz79 hc) (sGlobal15_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal15_hz82 {c : ℝ} (hc : B (21 / 50) (17 / 40) c) : B (14119536080811001679577 / 1000000000000000000) (14194855364181092140957 / 1000000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) := bmul sGlobal15_hz80 (sGlobal15_hz81 hc) (by norm_num) (by norm_num)

theorem sGlobal15_hz83 {c : ℝ} (hc : B (21 / 50) (17 / 40) c) : B (1764942010101375209947 / 250000000000000000) (7097427682090546070479 / 1000000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) / (2 : ℝ)) := bdiv (sGlobal15_hz82 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal15_hz84 {c : ℝ} (hc : B (21 / 50) (17 / 40) c) : B (1764942010101375209947 / 250000000000000000) (7097427682090546070479 / 1000000000000000000) (s3Cpa 12225 c) := by
    convert (sGlobal15_hz83 hc) using 1 <;>
      norm_num [s3Cpa, mA] <;> ring

theorem sGlobal15_hz85 {c : ℝ} (hc : B (21 / 50) (17 / 40) c) : B (144065996028678217 / 500000000000000000) (144436947184428359 / 500000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (sGlobal15_hz79 hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal15_hz86 {c : ℝ} (hc : B (21 / 50) (17 / 40) c) : B (267947370808846911 / 1000000000000000000) (27188351083726763 / 100000000000000000) (c * (kdot c)) := bmul (sGlobal15_hz38 hc) (sGlobal15_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal15_hz87 {c : ℝ} (hc : B (21 / 50) (17 / 40) c) : B (4062120305022201 / 250000000000000000) (20926523560009807 / 1000000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (sGlobal15_hz85 hc) (sGlobal15_hz86 hc) (by norm_num) (by norm_num)

theorem sGlobal15_hz88 {c : ℝ} (hc : B (21 / 50) (17 / 40) c) : B (397275365831168879113 / 1000000000000000000) (511653501042239845107 / 1000000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) := bmul sGlobal15_hz80 (sGlobal15_hz87 hc) (by norm_num) (by norm_num)

theorem sGlobal15_hz89 {c : ℝ} (hc : B (21 / 50) (17 / 40) c) : B (49659420728896109889 / 250000000000000000) (127913375260559961277 / 500000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) / (2 : ℝ)) := bdiv (sGlobal15_hz88 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal15_hz90 {c : ℝ} (hc : B (21 / 50) (17 / 40) c) : B (49659420728896109889 / 250000000000000000) (127913375260559961277 / 500000000000000000) (s3Cpp 12225 c) := by
    convert (sGlobal15_hz89 hc) using 1 <;>
      norm_num [s3Cpp, mA] <;> ring

theorem sGlobal15_hz91 {c : ℝ} (hc : B (21 / 50) (17 / 40) c) : B (7174913150339238548189 / 1000000000000000000) (1442514558404856896541 / 200000000000000000) ((s3Cpa 12225 c) + (s3r1 12225 46)) := badd (sGlobal15_hz84 hc) sGlobal15_hz33 (by norm_num) (by norm_num)

theorem sGlobal15_hz92 {c : ℝ} (hc : B (21 / 50) (17 / 40) c) : B (64964241339624734133 / 1000000000000000000) (65305225265134054221 / 1000000000000000000) (((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) := bdiv (sGlobal15_hz91 hc) sGlobal15_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal15_hz93 {c : ℝ} (hc : B (21 / 50) (17 / 40) c) : B (13017384873023758909 / 200000000000000000) (16356977072657028661 / 250000000000000000) ((((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) + (s3e0 12225 46)) := badd (sGlobal15_hz92 hc) sGlobal15_hz16 (by norm_num) (by norm_num)

theorem sGlobal15_hz94 {c : ℝ} (hc : B (21 / 50) (17 / 40) c) : B (13017384873023758909 / 200000000000000000) (16356977072657028661 / 250000000000000000) (s3Lam 12225 46 c) := by
    convert (sGlobal15_hz93 hc) using 1 <;>
      norm_num [s3Lam] <;> ring

theorem sGlobal15_hz95 {c : ℝ} (hc : B (21 / 50) (17 / 40) c) : B (68850272384519061289 / 250000000000000000) (83147539285903049343 / 250000000000000000) ((s3Cpp 12225 c) + (s3rpp 12225 46)) := badd (sGlobal15_hz90 hc) sGlobal15_hz37 (by norm_num) (by norm_num)

theorem sGlobal15_hz96 {c : ℝ} (hc : B (21 / 50) (17 / 40) c) : B (68850272384519061289 / 500000000000000000) (229934088595178568893 / 1000000000000000000) (if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) := bweaken (bfirst (sGlobal15_hz95 hc) (sGlobal15_hz76 hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem sGlobal15_hz97 {c : ℝ} (hc : B (21 / 50) (17 / 40) c) : B (847261544662138919271 / 200000000000000000) (4280811183286843178747 / 1000000000000000000) ((s3Lam 12225 46 c)^2) := bsq (sGlobal15_hz94 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal15_hz98 {c : ℝ} (hc : B (21 / 50) (17 / 40) c) : B (63253312306870367 / 200000000000000000) (319868969320267317 / 1000000000000000000) ((s3c1 12225 46 c)^2) := bsq (sGlobal15_hz72 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal15_hz99 {c : ℝ} (hc : B (21 / 50) (17 / 40) c) : B (680131030679732683 / 1000000000000000000) (136746687693129633 / 200000000000000000) ((1 : ℝ) - ((s3c1 12225 46 c)^2)) := bsub (bpoint (1 : ℝ)) (sGlobal15_hz98 hc) (by norm_num) (by norm_num)

theorem sGlobal15_hz100 {c : ℝ} (hc : B (21 / 50) (17 / 40) c) : B (824700570316119451 / 1000000000000000000) (413440878018141841 / 500000000000000000) (√((1 : ℝ) - ((s3c1 12225 46 c)^2))) := bsqrt (sGlobal15_hz99 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal15_hz101 {c : ℝ} (hc : B (21 / 50) (17 / 40) c) : B (1295436626558216787 / 500000000000000000) (1298862825075508243 / 500000000000000000) (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))) := bmul pi_mem (sGlobal15_hz100 hc) (by norm_num) (by norm_num)

theorem sGlobal15_hz102 {c : ℝ} (hc : B (21 / 50) (17 / 40) c) : B (407693911312807473429 / 250000000000000000) (330453153440653005211 / 200000000000000000) (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2))))) := bdiv (sGlobal15_hz97 hc) (sGlobal15_hz101 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal15_hz103 {c : ℝ} (hc : B (21 / 50) (17 / 40) c) : B (884238095010134008147 / 500000000000000000) (470549963949610898737 / 250000000000000000) ((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) := badd (sGlobal15_hz96 hc) (sGlobal15_hz102 hc) (by norm_num) (by norm_num)

theorem sGlobal15_hz104 : B (3762781186094069 / 250000000000000000) (376278118609407 / 25000000000000000) ((s3e0 12225 46)^2) := bsq sGlobal15_hz16 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal15_hz105 {c : ℝ} (hc : B (21 / 50) (17 / 40) c) : B (176849124114501239257 / 100000000000000000) (470553726730796992807 / 250000000000000000) (((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) := badd (sGlobal15_hz103 hc) sGlobal15_hz104 (by norm_num) (by norm_num)

theorem sGlobal15_hz106 {c : ℝ} (hc : B (21 / 50) (17 / 40) c) : B (1806988314596259662701 / 1000000000000000000) (480177995094328060311 / 250000000000000000) ((((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) + (s3rs 12225 46 maskSlack)) := badd (sGlobal15_hz105 hc) sGlobal15_hz29 (by norm_num) (by norm_num)

theorem sGlobal15_hz107 {c : ℝ} (hc : B (21 / 50) (17 / 40) c) : B (1806988314596259662701 / 1000000000000000000) (480177995094328060311 / 250000000000000000) (s3U 12225 46 maskSlack c) := by
    convert (sGlobal15_hz106 hc) using 1 <;>
      norm_num [s3U] <;> ring

theorem sGlobal15_hz108 {c : ℝ} (hc : B (21 / 50) (17 / 40) c) : B (60937138146546082369 / 500000000000000000) (89531671949314058477 / 500000000000000000) ((s3Cpp 12225 c) - (s3rpp 12225 46)) := bsub (sGlobal15_hz90 hc) sGlobal15_hz37 (by norm_num) (by norm_num)

theorem sGlobal15_hz109 {c : ℝ} (hc : B (21 / 50) (17 / 40) c) : B 0 0 (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ)) := bweaken (bmin (sGlobal15_hz108 hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem sGlobal15_hz110 {c : ℝ} (hc : B (21 / 50) (17 / 40) c) : B 0 0 ((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) := bmul (sGlobal15_hz76 hc) (sGlobal15_hz109 hc) (by norm_num) (by norm_num)

theorem sGlobal15_hz111 {c : ℝ} (hc : B (21 / 50) (17 / 40) c) : B (-376278118609407 / 25000000000000000) (-3762781186094069 / 250000000000000000) (((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) := bsub (sGlobal15_hz110 hc) sGlobal15_hz104 (by norm_num) (by norm_num)

theorem sGlobal15_hz112 {c : ℝ} (hc : B (21 / 50) (17 / 40) c) : B (-4814015572358580787 / 125000000000000000) (-38512124575991646407 / 1000000000000000000) ((((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) - (s3rs 12225 46 maskSlack)) := bsub (sGlobal15_hz111 hc) sGlobal15_hz29 (by norm_num) (by norm_num)

theorem sGlobal15_hz113 {c : ℝ} (hc : B (21 / 50) (17 / 40) c) : B (-4814015572358580787 / 125000000000000000) (-38512124575991646407 / 1000000000000000000) (s3L 12225 46 maskSlack c) := by
    convert (sGlobal15_hz112 hc) using 1 <;>
      norm_num [s3L] <;> ring

theorem sGlobal15_hz114 {c : ℝ} (hc : B (21 / 50) (17 / 40) c) : B 0 (480177995094328060311 / 250000000000000000) |(s3U 12225 46 maskSlack c)| := bweaken (babs (sGlobal15_hz107 hc)) (by norm_num) (by norm_num)

theorem sGlobal15_hz115 {c : ℝ} (hc : B (21 / 50) (17 / 40) c) : B 0 (4814015572358580787 / 125000000000000000) |(s3L 12225 46 maskSlack c)| := bweaken (babs (sGlobal15_hz113 hc)) (by norm_num) (by norm_num)

theorem sGlobal15_hz116 {c : ℝ} (hc : B (21 / 50) (17 / 40) c) : B 0 (480177995094328060311 / 250000000000000000) (max |(s3U 12225 46 maskSlack c)| |(s3L 12225 46 maskSlack c)|) := bweaken (bmax (sGlobal15_hz114 hc) (sGlobal15_hz115 hc)) (by norm_num) (by norm_num)

theorem sGlobal15_hz117 {c : ℝ} (hc : B (21 / 50) (17 / 40) c) : B 0 (480177995094328060311 / 250000000000000000) (s3nks 12225 46 maskSlack c) := by
    convert (sGlobal15_hz116 hc) using 1 <;>
      norm_num [s3nks] <;> ring

theorem sGlobal15 {c : ℝ} (hc : B (21 / 50) (17 / 40) c) :
    0 < s3am 12225 46 ∧ 0 ≤ s3dm 12225 46 c ∧
    s3dm 12225 46 c ^ 2 ≤ 2 * s3ap 12225 46 ^ 2 ∧ s3c1 12225 46 c < 1 ∧
    0 ≤ s3Cpa 12225 c - s3r1 12225 46 ∧
    s3e0 12225 46 ≤ (s3Cpa 12225 c - s3r1 12225 46) / s3ap 12225 46 ∧
    s3nks 12225 46 maskSlack c ≤ 12225 * (78557 / 500000) := by

  refine ⟨lt_of_lt_of_le (by norm_num) sGlobal15_hz14.1,
    le_trans (by norm_num) (sGlobal15_hz64 hc).1, ?_,
    lt_of_le_of_lt (sGlobal15_hz72 hc).2 (by norm_num), ?_, ?_,
    le_trans (sGlobal15_hz117 hc).2 (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (sGlobal15_hz64 hc).1) (sGlobal15_hz64 hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) sGlobal15_hz9.1 2
    nlinarith only [h1, h2]
  · linarith only [(sGlobal15_hz84 hc).1, sGlobal15_hz33.2]
  · have hap : 0 < s3ap 12225 46 := lt_of_lt_of_le (by norm_num) sGlobal15_hz9.1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul sGlobal15_hz16.2 sGlobal15_hz9.2 (le_trans (by norm_num) sGlobal15_hz9.1) (by norm_num)
    linarith only [h, (sGlobal15_hz84 hc).1, sGlobal15_hz33.2]

end BstLean.Part255
