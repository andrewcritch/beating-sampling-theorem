import BstLean.Part255SGlobal12
import BstLean.Part255Numeric10
namespace BstLean.Part255
open Real BstLean.Part130 BstLean.Part182 BstLean.Part197 BstLean.Part246
theorem sGlobal16_hz0 : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal16_hz1 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) ((√(23 : ℝ)) / (12225 : ℝ)) := bdiv sGlobal16_hz0 (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal16_hz2 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) maskSlack := by
    convert sGlobal16_hz1 using 1 <;>
      norm_num [maskSlack] <;> ring

theorem sGlobal16_hz3 : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal16_hz4 : B (6395294793910793 / 500000000000000000) (12790589587821587 / 1000000000000000000) (√((2 / 12225) : ℝ)) := bsqrt (bpoint ((2 / 12225) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal16_hz5 : B (7230130686979 / 62500000000000000) (23136418198333 / 200000000000000000) (√((2 / 149450625) : ℝ)) := bsqrt (bpoint ((2 / 149450625) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal16_hz6 : B (2211334438749598093 / 20000000000000000) (110566721937479904651 / 1000000000000000000) (√(12225 : ℝ)) := bsqrt (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal16_hz7 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))) := bmul sGlobal16_hz3 sGlobal16_hz4 (by norm_num) (by norm_num)

theorem sGlobal16_hz8 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) ((√(12225 : ℝ)) + ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := badd sGlobal16_hz6 sGlobal16_hz7 (by norm_num) (by norm_num)

theorem sGlobal16_hz9 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) (s3ap 12225 46) := by
    convert sGlobal16_hz8 using 1 <;>
      norm_num [s3ap, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal16_hz10 : B (163599182004089 / 1000000000000000000) (16359918200409 / 100000000000000000) ((2 : ℝ) / (12225 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal16_hz11 : B (1222499983640081799591 / 100000000000000000) (12224999836400817995911 / 1000000000000000000) ((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ))) := bsub (bpoint (12225 : ℝ)) sGlobal16_hz10 (by norm_num) (by norm_num)

theorem sGlobal16_hz12 : B (110566721197658827907 / 1000000000000000000) (27641680299414706977 / 250000000000000000) (√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) := bsqrt sGlobal16_hz11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal16_hz13 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) ((√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) - ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bsub sGlobal16_hz12 sGlobal16_hz7 (by norm_num) (by norm_num)

theorem sGlobal16_hz14 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) (s3am 12225 46) := by
    convert sGlobal16_hz13 using 1 <;>
      norm_num [s3am, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal16_hz15 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√((2 / 12225) : ℝ)) * (√(92 : ℝ))) := bmul sGlobal16_hz4 sGlobal16_hz3 (by norm_num) (by norm_num)

theorem sGlobal16_hz16 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) (s3e0 12225 46) := by
    convert sGlobal16_hz15 using 1 <;>
      norm_num [s3e0, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal16_hz17 : B (250196148528560847 / 500000000000000000) (100078459411424339 / 200000000000000000) (((1 / 2) : ℝ) + maskSlack) := badd (bpoint ((1 / 2) : ℝ)) sGlobal16_hz2 (by norm_num) (by norm_num)

theorem sGlobal16_hz18 : B (59827153232297998295487 / 800000000000000) (23930861292919199366019 / 320000000000000) ((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack)) := bmul (bpoint (149450625 : ℝ)) sGlobal16_hz17 (by norm_num) (by norm_num)

theorem sGlobal16_hz19 : B (1729554180017180009583 / 200000000000000000) (8647770900085900056557 / 1000000000000000000) (√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) := bsqrt sGlobal16_hz18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal16_hz20 : B (4328681281566262743499 / 500000000000000000) (8657362563132525495641 / 1000000000000000000) ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))) := badd sGlobal16_hz19 sGlobal16_hz3 (by norm_num) (by norm_num)

theorem sGlobal16_hz21 : B (110732771457999278473 / 1000000000000000000) (55366385728999643621 / 500000000000000000) ((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ)))) := bmul sGlobal16_hz4 sGlobal16_hz20 (by norm_num) (by norm_num)

theorem sGlobal16_hz22 : B (209099159 / 15625000000000000) (13382346177 / 1000000000000000000) ((2 : ℝ) / (149450625 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (149450625 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal16_hz23 : B (2452349334953899930479 / 200000000000000000) (12261746674769501594427 / 1000000000000000000) (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2) := bsq sGlobal16_hz21 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal16_hz24 : B (82045469362091 / 500000000000000000) (32818187747289 / 200000000000000000) (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2)) := bmul sGlobal16_hz22 sGlobal16_hz23 (by norm_num) (by norm_num)

theorem sGlobal16_hz25 : B (82045469362091 / 250000000000000000) (32818187747289 / 100000000000000000) ((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) := bmul (bpoint (2 : ℝ)) sGlobal16_hz24 (by norm_num) (by norm_num)

theorem sGlobal16_hz26 : B (117258080744995992792057 / 1000000000000000000) (58629040372497996396029 / 500000000000000000) (√(13749457500 : ℝ)) := bsqrt (bpoint (13749457500 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal16_hz27 : B (117304080744995992792057 / 1000000000000000000) (58652040372497996396029 / 500000000000000000) ((√(13749457500 : ℝ)) + (46 : ℝ)) := badd sGlobal16_hz26 (bpoint (46 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal16_hz28 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal16_hz25 sGlobal16_hz27 (by norm_num) (by norm_num)

theorem sGlobal16_hz29 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (s3rs 12225 46 maskSlack) := by
    convert sGlobal16_hz28 using 1 <;>
      norm_num [s3rs, s3pp, s3K, mA, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal16_hz30 : B (490797546012267 / 1000000000000000000) (49079754601227 / 100000000000000000) ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (3 : ℝ)) sGlobal16_hz10 (by norm_num) (by norm_num)

theorem sGlobal16_hz31 : B (490797546012267 / 500000000000000000) (49079754601227 / 50000000000000000) ((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal16_hz30 (by norm_num) (by norm_num)

theorem sGlobal16_hz32 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal16_hz31 sGlobal16_hz27 (by norm_num) (by norm_num)

theorem sGlobal16_hz33 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (s3r1 12225 46) := by
    convert sGlobal16_hz32 using 1 <;>
      norm_num [s3r1, mA] <;> ring

theorem sGlobal16_hz34 : B (163599182004089 / 500000000000000000) (16359918200409 / 50000000000000000) ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (2 : ℝ)) sGlobal16_hz10 (by norm_num) (by norm_num)

theorem sGlobal16_hz35 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal16_hz34 (by norm_num) (by norm_num)

theorem sGlobal16_hz36 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal16_hz35 sGlobal16_hz27 (by norm_num) (by norm_num)

theorem sGlobal16_hz37 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (s3rpp 12225 46) := by
    convert sGlobal16_hz36 using 1 <;>
      norm_num [s3rpp, mA] <;> ring

theorem sGlobal16_hz38 {c : ℝ} (hc : B (17 / 40) (43 / 100) c) : B (17 / 40) (43 / 100) c := hc

theorem sGlobal16_hz39 : B (639725907846664981 / 1000000000000000000) (319862953926197211 / 500000000000000000) (kdot ((17 / 40))) := by
    constructor
    · apply bkdot_lower (q := (635223403166023601 / 1000000000000000000)) (a := (282958610296912367 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (1588058507915059 / 2500000000000000)) (a := (565917220584824951 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal16_hz40 : B (289 / 1600) (289 / 1600) (((17 / 40) : ℝ)^2) := bsq (bpoint ((17 / 40) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal16_hz41 : B (1311 / 1600) (1311 / 1600) ((1 : ℝ) - (((17 / 40) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal16_hz40 (by norm_num) (by norm_num)

theorem sGlobal16_hz42 : B (90519334951158363 / 100000000000000000) (905193349511583631 / 1000000000000000000) (√((1 : ℝ) - (((17 / 40) : ℝ)^2))) := bsqrt sGlobal16_hz41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal16_hz43 : B (144065996028678217 / 500000000000000000) (57626398411471287 / 200000000000000000) ((√((1 : ℝ) - (((17 / 40) : ℝ)^2))) / Real.pi) := bdiv sGlobal16_hz42 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal16_hz44 : B (33985438854354077 / 125000000000000000) (27188351083726763 / 100000000000000000) (((17 / 40) : ℝ) * (kdot ((17 / 40)))) := bmul (bpoint ((17 / 40) : ℝ)) sGlobal16_hz39 (by norm_num) (by norm_num)

theorem sGlobal16_hz45 : B (11200310057843781 / 20000000000000000) (112003100578924813 / 200000000000000000) (((√((1 : ℝ) - (((17 / 40) : ℝ)^2))) / Real.pi) + (((17 / 40) : ℝ) * (kdot ((17 / 40))))) := badd sGlobal16_hz43 sGlobal16_hz44 (by norm_num) (by norm_num)

theorem sGlobal16_hz46 : B (11200310057843781 / 20000000000000000) (112003100578924813 / 200000000000000000) (kappa ((17 / 40))) := by rw [kappa_eq]; exact sGlobal16_hz45

theorem sGlobal16_hz47 : B (160371611308842497 / 250000000000000000) (128297289047923071 / 200000000000000000) (kdot ((43 / 100))) := by
    constructor
    · apply bkdot_lower (q := (631348872337156077 / 1000000000000000000)) (a := (56315177493046183 / 100000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (157837218084289019 / 250000000000000000)) (a := (70393971865474153 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal16_hz48 : B (1849 / 10000) (1849 / 10000) (((43 / 100) : ℝ)^2) := bsq (bpoint ((43 / 100) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal16_hz49 : B (8151 / 10000) (8151 / 10000) ((1 : ℝ) - (((43 / 100) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal16_hz48 (by norm_num) (by norm_num)

theorem sGlobal16_hz50 : B (902828887442133189 / 1000000000000000000) (90282888744213319 / 100000000000000000) (√((1 : ℝ) - (((43 / 100) : ℝ)^2))) := bsqrt sGlobal16_hz49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal16_hz51 : B (143689680202571887 / 500000000000000000) (11495174416205751 / 40000000000000000) ((√((1 : ℝ) - (((43 / 100) : ℝ)^2))) / Real.pi) := bdiv sGlobal16_hz50 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal16_hz52 : B (137919585725604547 / 500000000000000000) (275839171453034603 / 1000000000000000000) (((43 / 100) : ℝ) * (kdot ((43 / 100)))) := bmul (bpoint ((43 / 100) : ℝ)) sGlobal16_hz47 (by norm_num) (by norm_num)

theorem sGlobal16_hz53 : B (140804632964088217 / 250000000000000000) (281609265929089189 / 500000000000000000) (((√((1 : ℝ) - (((43 / 100) : ℝ)^2))) / Real.pi) + (((43 / 100) : ℝ) * (kdot ((43 / 100))))) := badd sGlobal16_hz51 sGlobal16_hz52 (by norm_num) (by norm_num)

theorem sGlobal16_hz54 : B (140804632964088217 / 250000000000000000) (281609265929089189 / 500000000000000000) (kappa ((43 / 100))) := by rw [kappa_eq]; exact sGlobal16_hz53

theorem sGlobal16_hz55 {c : ℝ} (hc : B (17 / 40) (43 / 100) c) : B (11200310057843781 / 20000000000000000) (281609265929089189 / 500000000000000000) (kappa c) := bkappa (sGlobal16_hz38 hc) (by norm_num) (by norm_num) sGlobal16_hz46.1 sGlobal16_hz54.2

theorem sGlobal16_hz56 : B 24450 24450 ((2 : ℝ) * (12225 : ℝ)) := bmul (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal16_hz57 {c : ℝ} (hc : B (17 / 40) (43 / 100) c) : B (218390734070910811 / 500000000000000000) (8799689942156219 / 20000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (sGlobal16_hz55 hc) (by norm_num) (by norm_num)

theorem sGlobal16_hz58 {c : ℝ} (hc : B (17 / 40) (43 / 100) c) : B (106793068960675386579 / 10000000000000000) (4303048381714391091 / 400000000000000) (((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) := bmul sGlobal16_hz56 (sGlobal16_hz57 hc) (by norm_num) (by norm_num)

theorem sGlobal16_hz59 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (4 : ℝ)) sGlobal16_hz10 (by norm_num) (by norm_num)

theorem sGlobal16_hz60 {c : ℝ} (hc : B (17 / 40) (43 / 100) c) : B (533965312083540532077 / 50000000000000000) (1344702537486156213893 / 125000000000000000) ((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bsub (sGlobal16_hz58 hc) sGlobal16_hz59 (by norm_num) (by norm_num)

theorem sGlobal16_hz61 {c : ℝ} (hc : B (17 / 40) (43 / 100) c) : B (103340728861716524287 / 1000000000000000000) (25929737151445984277 / 250000000000000000) (√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) := bsqrt (sGlobal16_hz60 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal16_hz62 : B (30670756373515103 / 125000000000000000) (122683025494060423 / 500000000000000000) ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal16_hz7 (by norm_num) (by norm_num)

theorem sGlobal16_hz63 {c : ℝ} (hc : B (17 / 40) (43 / 100) c) : B (103095362810728403441 / 1000000000000000000) (25868395638698954071 / 250000000000000000) ((√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) - ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))))) := bsub (sGlobal16_hz61 hc) sGlobal16_hz62 (by norm_num) (by norm_num)

theorem sGlobal16_hz64 {c : ℝ} (hc : B (17 / 40) (43 / 100) c) : B (103095362810728403441 / 1000000000000000000) (25868395638698954071 / 250000000000000000) (s3dm 12225 46 c) := by
    convert (sGlobal16_hz63 hc) using 1 <;>
      norm_num [s3dm, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal16_hz65 : B (6126072185528622723889 / 500000000000000000) (2450428874211449090087 / 200000000000000000) ((s3ap 12225 46)^2) := bsq sGlobal16_hz9 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal16_hz66 : B (6126072185528622723889 / 250000000000000000) (2450428874211449090087 / 100000000000000000) ((2 : ℝ) * ((s3ap 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal16_hz65 (by norm_num) (by norm_num)

theorem sGlobal16_hz67 {c : ℝ} (hc : B (17 / 40) (43 / 100) c) : B (332145432283616285317 / 31250000000000000) (5353391143362072543419 / 500000000000000000) ((s3dm 12225 46 c)^2) := bsq (sGlobal16_hz64 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal16_hz68 {c : ℝ} (hc : B (17 / 40) (43 / 100) c) : B (6898753227695172904359 / 500000000000000000) (6937817454519384885363 / 500000000000000000) (((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) := bsub sGlobal16_hz66 (sGlobal16_hz67 hc) (by norm_num) (by norm_num)

theorem sGlobal16_hz69 : B (1524735695971823534271 / 125000000000000000) (609894278388729413841 / 50000000000000000) ((s3am 12225 46)^2) := bsq sGlobal16_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal16_hz70 : B (1524735695971823534271 / 62500000000000000) (609894278388729413841 / 25000000000000000) ((2 : ℝ) * ((s3am 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal16_hz69 (by norm_num) (by norm_num)

theorem sGlobal16_hz71 {c : ℝ} (hc : B (17 / 40) (43 / 100) c) : B (113113919447168549 / 200000000000000000) (113754427617329043 / 200000000000000000) ((((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) / ((2 : ℝ) * ((s3am 12225 46)^2))) := bdiv (sGlobal16_hz68 hc) sGlobal16_hz70 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal16_hz72 {c : ℝ} (hc : B (17 / 40) (43 / 100) c) : B (113113919447168549 / 200000000000000000) (113754427617329043 / 200000000000000000) (s3c1 12225 46 c) := by
    convert (sGlobal16_hz71 hc) using 1 <;>
      norm_num [s3c1] <;> ring

theorem sGlobal16_hz73 {c : ℝ} (hc : B (17 / 40) (43 / 100) c) : B (639725907846664981 / 1000000000000000000) (128297289047923071 / 200000000000000000) (kdot c) := bkdot (sGlobal16_hz38 hc) sGlobal16_hz39.1 sGlobal16_hz47.2

theorem sGlobal16_hz74 : B (691343636172553523 / 1000000000000000000) (691343636172554119 / 1000000000000000000) (kdot ((113113919447168549 / 200000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (263386748111956789 / 500000000000000000)) (a := (121209070635505531 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (526773496223913577 / 1000000000000000000)) (a := (121209070635505297 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal16_hz75 : B (34629068755213043 / 50000000000000000) (346290687552130667 / 500000000000000000) (kdot ((113754427617329043 / 200000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (262146145955820967 / 500000000000000000)) (a := (482892046774565199 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (524292291911641933 / 1000000000000000000)) (a := (60361505846820557 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal16_hz76 {c : ℝ} (hc : B (17 / 40) (43 / 100) c) : B (691343636172553523 / 1000000000000000000) (346290687552130667 / 500000000000000000) (kdot (s3c1 12225 46 c)) := bkdot (sGlobal16_hz72 hc) sGlobal16_hz74.1 sGlobal16_hz75.2

theorem sGlobal16_hz77 {c : ℝ} (hc : B (17 / 40) (43 / 100) c) : B (289 / 1600) (1849 / 10000) (c^2) := bsq (sGlobal16_hz38 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal16_hz78 {c : ℝ} (hc : B (17 / 40) (43 / 100) c) : B (8151 / 10000) (1311 / 1600) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (sGlobal16_hz77 hc) (by norm_num) (by norm_num)

theorem sGlobal16_hz79 {c : ℝ} (hc : B (17 / 40) (43 / 100) c) : B (902828887442133189 / 1000000000000000000) (905193349511583631 / 1000000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (sGlobal16_hz78 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal16_hz80 : B (39119999999999765769 / 1600000000000000) (3912000000000000489 / 160000000000000) ((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (149450625 : ℝ)) sGlobal16_hz10 (by norm_num) (by norm_num)

theorem sGlobal16_hz81 {c : ℝ} (hc : B (17 / 40) (43 / 100) c) : B (577563029649113167 / 1000000000000000000) (18145914501022703 / 31250000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (sGlobal16_hz79 hc) (sGlobal16_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal16_hz82 {c : ℝ} (hc : B (17 / 40) (43 / 100) c) : B (14121416074920732381171 / 1000000000000000000) (14197363505600164601871 / 1000000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) := bmul sGlobal16_hz80 (sGlobal16_hz81 hc) (by norm_num) (by norm_num)

theorem sGlobal16_hz83 {c : ℝ} (hc : B (17 / 40) (43 / 100) c) : B (1412141607492073238117 / 200000000000000000) (887335219100010287617 / 125000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) / (2 : ℝ)) := bdiv (sGlobal16_hz82 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal16_hz84 {c : ℝ} (hc : B (17 / 40) (43 / 100) c) : B (1412141607492073238117 / 200000000000000000) (887335219100010287617 / 125000000000000000) (s3Cpa 12225 c) := by
    convert (sGlobal16_hz83 hc) using 1 <;>
      norm_num [s3Cpa, mA] <;> ring

theorem sGlobal16_hz85 {c : ℝ} (hc : B (17 / 40) (43 / 100) c) : B (143689680202571887 / 500000000000000000) (57626398411471287 / 200000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (sGlobal16_hz79 hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal16_hz86 {c : ℝ} (hc : B (17 / 40) (43 / 100) c) : B (33985438854354077 / 125000000000000000) (275839171453034603 / 1000000000000000000) (c * (kdot c)) := bmul (sGlobal16_hz38 hc) (sGlobal16_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal16_hz87 {c : ℝ} (hc : B (17 / 40) (43 / 100) c) : B (11540188952109171 / 1000000000000000000) (16248481222523819 / 1000000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (sGlobal16_hz85 hc) (sGlobal16_hz86 hc) (by norm_num) (by norm_num)

theorem sGlobal16_hz88 {c : ℝ} (hc : B (17 / 40) (43 / 100) c) : B (282157619879067541531 / 1000000000000000000) (39727536589070742421 / 100000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) := bmul sGlobal16_hz80 (sGlobal16_hz87 hc) (by norm_num) (by norm_num)

theorem sGlobal16_hz89 {c : ℝ} (hc : B (17 / 40) (43 / 100) c) : B (28215761987906754153 / 200000000000000000) (39727536589070742421 / 200000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) / (2 : ℝ)) := bdiv (sGlobal16_hz88 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal16_hz90 {c : ℝ} (hc : B (17 / 40) (43 / 100) c) : B (28215761987906754153 / 200000000000000000) (39727536589070742421 / 200000000000000000) (s3Cpp 12225 c) := by
    convert (sGlobal16_hz89 hc) using 1 <;>
      norm_num [s3Cpp, mA] <;> ring

theorem sGlobal16_hz91 {c : ℝ} (hc : B (17 / 40) (43 / 100) c) : B (3587926573697051949493 / 500000000000000000) (3606913431366910356581 / 500000000000000000) ((s3Cpa 12225 c) + (s3r1 12225 46)) := badd (sGlobal16_hz84 hc) sGlobal16_hz33 (by norm_num) (by norm_num)

theorem sGlobal16_hz92 {c : ℝ} (hc : B (17 / 40) (43 / 100) c) : B (64972752410665074439 / 1000000000000000000) (65316580071878636783 / 1000000000000000000) (((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) := bdiv (sGlobal16_hz91 hc) sGlobal16_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal16_hz93 {c : ℝ} (hc : B (17 / 40) (43 / 100) c) : B (65095435436159134851 / 1000000000000000000) (32719631548686348603 / 500000000000000000) ((((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) + (s3e0 12225 46)) := badd (sGlobal16_hz92 hc) sGlobal16_hz16 (by norm_num) (by norm_num)

theorem sGlobal16_hz94 {c : ℝ} (hc : B (17 / 40) (43 / 100) c) : B (65095435436159134851 / 1000000000000000000) (32719631548686348603 / 500000000000000000) (s3Lam 12225 46 c) := by
    convert (sGlobal16_hz93 hc) using 1 <;>
      norm_num [s3Lam] <;> ring

theorem sGlobal16_hz95 {c : ℝ} (hc : B (17 / 40) (43 / 100) c) : B (43568443312405115273 / 200000000000000000) (275401089567845986923 / 1000000000000000000) ((s3Cpp 12225 c) + (s3rpp 12225 46)) := badd (sGlobal16_hz90 hc) sGlobal16_hz37 (by norm_num) (by norm_num)

theorem sGlobal16_hz96 {c : ℝ} (hc : B (17 / 40) (43 / 100) c) : B (54460554140506394091 / 500000000000000000) (38147533063622122879 / 200000000000000000) (if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) := bweaken (bfirst (sGlobal16_hz95 hc) (sGlobal16_hz76 hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem sGlobal16_hz97 {c : ℝ} (hc : B (17 / 40) (43 / 100) c) : B (4237415714623162414933 / 1000000000000000000) (133821786085223877889 / 31250000000000000) ((s3Lam 12225 46 c)^2) := bsq (sGlobal16_hz94 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal16_hz98 {c : ℝ} (hc : B (17 / 40) (43 / 100) c) : B (319868969317513381 / 1000000000000000000) (323501745063653813 / 1000000000000000000) ((s3c1 12225 46 c)^2) := bsq (sGlobal16_hz72 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal16_hz99 {c : ℝ} (hc : B (17 / 40) (43 / 100) c) : B (676498254936346187 / 1000000000000000000) (680131030682486619 / 1000000000000000000) ((1 : ℝ) - ((s3c1 12225 46 c)^2)) := bsub (bpoint (1 : ℝ)) (sGlobal16_hz98 hc) (by norm_num) (by norm_num)

theorem sGlobal16_hz100 {c : ℝ} (hc : B (17 / 40) (43 / 100) c) : B (822495139764574041 / 1000000000000000000) (82470057031778911 / 100000000000000000) (√((1 : ℝ) - ((s3c1 12225 46 c)^2))) := bsqrt (sGlobal16_hz99 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal16_hz101 {c : ℝ} (hc : B (17 / 40) (43 / 100) c) : B (645986172174424007 / 250000000000000000) (647718313280419741 / 250000000000000000) (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))) := bmul pi_mem (sGlobal16_hz100 hc) (by norm_num) (by norm_num)

theorem sGlobal16_hz102 {c : ℝ} (hc : B (17 / 40) (43 / 100) c) : B (1635516407264463921999 / 1000000000000000000) (1657271215385587444183 / 1000000000000000000) (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2))))) := bdiv (sGlobal16_hz97 hc) (sGlobal16_hz101 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal16_hz103 {c : ℝ} (hc : B (17 / 40) (43 / 100) c) : B (1744437515545476710181 / 1000000000000000000) (924004440351849029289 / 500000000000000000) ((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) := badd (sGlobal16_hz96 hc) (sGlobal16_hz102 hc) (by norm_num) (by norm_num)

theorem sGlobal16_hz104 : B (3762781186094069 / 250000000000000000) (376278118609407 / 25000000000000000) ((s3e0 12225 46)^2) := bsq sGlobal16_hz16 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal16_hz105 {c : ℝ} (hc : B (17 / 40) (43 / 100) c) : B (1744452566670221086457 / 1000000000000000000) (924011965914221217429 / 500000000000000000) (((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) := badd (sGlobal16_hz103 hc) sGlobal16_hz104 (by norm_num) (by norm_num)

theorem sGlobal16_hz106 {c : ℝ} (hc : B (17 / 40) (43 / 100) c) : B (445737410030367089147 / 250000000000000000) (943260502641283352437 / 500000000000000000) ((((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) + (s3rs 12225 46 maskSlack)) := badd (sGlobal16_hz105 hc) sGlobal16_hz29 (by norm_num) (by norm_num)

theorem sGlobal16_hz107 {c : ℝ} (hc : B (17 / 40) (43 / 100) c) : B (445737410030367089147 / 250000000000000000) (943260502641283352437 / 500000000000000000) (s3U 12225 46 maskSlack c) := by
    convert (sGlobal16_hz106 hc) using 1 <;>
      norm_num [s3U] <;> ring

theorem sGlobal16_hz108 {c : ℝ} (hc : B (17 / 40) (43 / 100) c) : B (64315403317041495947 / 1000000000000000000) (24374855264572381301 / 200000000000000000) ((s3Cpp 12225 c) - (s3rpp 12225 46)) := bsub (sGlobal16_hz90 hc) sGlobal16_hz37 (by norm_num) (by norm_num)

theorem sGlobal16_hz109 {c : ℝ} (hc : B (17 / 40) (43 / 100) c) : B 0 0 (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ)) := bweaken (bmin (sGlobal16_hz108 hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem sGlobal16_hz110 {c : ℝ} (hc : B (17 / 40) (43 / 100) c) : B 0 0 ((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) := bmul (sGlobal16_hz76 hc) (sGlobal16_hz109 hc) (by norm_num) (by norm_num)

theorem sGlobal16_hz111 {c : ℝ} (hc : B (17 / 40) (43 / 100) c) : B (-376278118609407 / 25000000000000000) (-3762781186094069 / 250000000000000000) (((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) := bsub (sGlobal16_hz110 hc) sGlobal16_hz104 (by norm_num) (by norm_num)

theorem sGlobal16_hz112 {c : ℝ} (hc : B (17 / 40) (43 / 100) c) : B (-4814015572358580787 / 125000000000000000) (-38512124575991646407 / 1000000000000000000) ((((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) - (s3rs 12225 46 maskSlack)) := bsub (sGlobal16_hz111 hc) sGlobal16_hz29 (by norm_num) (by norm_num)

theorem sGlobal16_hz113 {c : ℝ} (hc : B (17 / 40) (43 / 100) c) : B (-4814015572358580787 / 125000000000000000) (-38512124575991646407 / 1000000000000000000) (s3L 12225 46 maskSlack c) := by
    convert (sGlobal16_hz112 hc) using 1 <;>
      norm_num [s3L] <;> ring

theorem sGlobal16_hz114 {c : ℝ} (hc : B (17 / 40) (43 / 100) c) : B 0 (943260502641283352437 / 500000000000000000) |(s3U 12225 46 maskSlack c)| := bweaken (babs (sGlobal16_hz107 hc)) (by norm_num) (by norm_num)

theorem sGlobal16_hz115 {c : ℝ} (hc : B (17 / 40) (43 / 100) c) : B 0 (4814015572358580787 / 125000000000000000) |(s3L 12225 46 maskSlack c)| := bweaken (babs (sGlobal16_hz113 hc)) (by norm_num) (by norm_num)

theorem sGlobal16_hz116 {c : ℝ} (hc : B (17 / 40) (43 / 100) c) : B 0 (943260502641283352437 / 500000000000000000) (max |(s3U 12225 46 maskSlack c)| |(s3L 12225 46 maskSlack c)|) := bweaken (bmax (sGlobal16_hz114 hc) (sGlobal16_hz115 hc)) (by norm_num) (by norm_num)

theorem sGlobal16_hz117 {c : ℝ} (hc : B (17 / 40) (43 / 100) c) : B 0 (943260502641283352437 / 500000000000000000) (s3nks 12225 46 maskSlack c) := by
    convert (sGlobal16_hz116 hc) using 1 <;>
      norm_num [s3nks] <;> ring

theorem sGlobal16 {c : ℝ} (hc : B (17 / 40) (43 / 100) c) :
    0 < s3am 12225 46 ∧ 0 ≤ s3dm 12225 46 c ∧
    s3dm 12225 46 c ^ 2 ≤ 2 * s3ap 12225 46 ^ 2 ∧ s3c1 12225 46 c < 1 ∧
    0 ≤ s3Cpa 12225 c - s3r1 12225 46 ∧
    s3e0 12225 46 ≤ (s3Cpa 12225 c - s3r1 12225 46) / s3ap 12225 46 ∧
    s3nks 12225 46 maskSlack c ≤ 12225 * (154317 / 1000000) := by

  refine ⟨lt_of_lt_of_le (by norm_num) sGlobal16_hz14.1,
    le_trans (by norm_num) (sGlobal16_hz64 hc).1, ?_,
    lt_of_le_of_lt (sGlobal16_hz72 hc).2 (by norm_num), ?_, ?_,
    le_trans (sGlobal16_hz117 hc).2 (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (sGlobal16_hz64 hc).1) (sGlobal16_hz64 hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) sGlobal16_hz9.1 2
    nlinarith only [h1, h2]
  · linarith only [(sGlobal16_hz84 hc).1, sGlobal16_hz33.2]
  · have hap : 0 < s3ap 12225 46 := lt_of_lt_of_le (by norm_num) sGlobal16_hz9.1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul sGlobal16_hz16.2 sGlobal16_hz9.2 (le_trans (by norm_num) sGlobal16_hz9.1) (by norm_num)
    linarith only [h, (sGlobal16_hz84 hc).1, sGlobal16_hz33.2]

end BstLean.Part255
