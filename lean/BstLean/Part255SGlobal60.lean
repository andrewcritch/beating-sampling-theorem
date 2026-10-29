import BstLean.Part255SGlobal56
import BstLean.Part255Numeric10
namespace BstLean.Part255
open Real BstLean.Part130 BstLean.Part182 BstLean.Part197 BstLean.Part246
theorem sGlobal60_hz0 : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal60_hz1 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) ((√(23 : ℝ)) / (12225 : ℝ)) := bdiv sGlobal60_hz0 (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal60_hz2 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) maskSlack := by
    convert sGlobal60_hz1 using 1 <;>
      norm_num [maskSlack] <;> ring

theorem sGlobal60_hz3 : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal60_hz4 : B (6395294793910793 / 500000000000000000) (12790589587821587 / 1000000000000000000) (√((2 / 12225) : ℝ)) := bsqrt (bpoint ((2 / 12225) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal60_hz5 : B (7230130686979 / 62500000000000000) (23136418198333 / 200000000000000000) (√((2 / 149450625) : ℝ)) := bsqrt (bpoint ((2 / 149450625) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal60_hz6 : B (2211334438749598093 / 20000000000000000) (110566721937479904651 / 1000000000000000000) (√(12225 : ℝ)) := bsqrt (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal60_hz7 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))) := bmul sGlobal60_hz3 sGlobal60_hz4 (by norm_num) (by norm_num)

theorem sGlobal60_hz8 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) ((√(12225 : ℝ)) + ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := badd sGlobal60_hz6 sGlobal60_hz7 (by norm_num) (by norm_num)

theorem sGlobal60_hz9 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) (s3ap 12225 46) := by
    convert sGlobal60_hz8 using 1 <;>
      norm_num [s3ap, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal60_hz10 : B (163599182004089 / 1000000000000000000) (16359918200409 / 100000000000000000) ((2 : ℝ) / (12225 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal60_hz11 : B (1222499983640081799591 / 100000000000000000) (12224999836400817995911 / 1000000000000000000) ((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ))) := bsub (bpoint (12225 : ℝ)) sGlobal60_hz10 (by norm_num) (by norm_num)

theorem sGlobal60_hz12 : B (110566721197658827907 / 1000000000000000000) (27641680299414706977 / 250000000000000000) (√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) := bsqrt sGlobal60_hz11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal60_hz13 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) ((√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) - ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bsub sGlobal60_hz12 sGlobal60_hz7 (by norm_num) (by norm_num)

theorem sGlobal60_hz14 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) (s3am 12225 46) := by
    convert sGlobal60_hz13 using 1 <;>
      norm_num [s3am, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal60_hz15 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√((2 / 12225) : ℝ)) * (√(92 : ℝ))) := bmul sGlobal60_hz4 sGlobal60_hz3 (by norm_num) (by norm_num)

theorem sGlobal60_hz16 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) (s3e0 12225 46) := by
    convert sGlobal60_hz15 using 1 <;>
      norm_num [s3e0, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal60_hz17 : B (250196148528560847 / 500000000000000000) (100078459411424339 / 200000000000000000) (((1 / 2) : ℝ) + maskSlack) := badd (bpoint ((1 / 2) : ℝ)) sGlobal60_hz2 (by norm_num) (by norm_num)

theorem sGlobal60_hz18 : B (59827153232297998295487 / 800000000000000) (23930861292919199366019 / 320000000000000) ((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack)) := bmul (bpoint (149450625 : ℝ)) sGlobal60_hz17 (by norm_num) (by norm_num)

theorem sGlobal60_hz19 : B (1729554180017180009583 / 200000000000000000) (8647770900085900056557 / 1000000000000000000) (√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) := bsqrt sGlobal60_hz18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal60_hz20 : B (4328681281566262743499 / 500000000000000000) (8657362563132525495641 / 1000000000000000000) ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))) := badd sGlobal60_hz19 sGlobal60_hz3 (by norm_num) (by norm_num)

theorem sGlobal60_hz21 : B (110732771457999278473 / 1000000000000000000) (55366385728999643621 / 500000000000000000) ((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ)))) := bmul sGlobal60_hz4 sGlobal60_hz20 (by norm_num) (by norm_num)

theorem sGlobal60_hz22 : B (209099159 / 15625000000000000) (13382346177 / 1000000000000000000) ((2 : ℝ) / (149450625 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (149450625 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal60_hz23 : B (2452349334953899930479 / 200000000000000000) (12261746674769501594427 / 1000000000000000000) (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2) := bsq sGlobal60_hz21 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal60_hz24 : B (82045469362091 / 500000000000000000) (32818187747289 / 200000000000000000) (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2)) := bmul sGlobal60_hz22 sGlobal60_hz23 (by norm_num) (by norm_num)

theorem sGlobal60_hz25 : B (82045469362091 / 250000000000000000) (32818187747289 / 100000000000000000) ((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) := bmul (bpoint (2 : ℝ)) sGlobal60_hz24 (by norm_num) (by norm_num)

theorem sGlobal60_hz26 : B (117258080744995992792057 / 1000000000000000000) (58629040372497996396029 / 500000000000000000) (√(13749457500 : ℝ)) := bsqrt (bpoint (13749457500 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal60_hz27 : B (117304080744995992792057 / 1000000000000000000) (58652040372497996396029 / 500000000000000000) ((√(13749457500 : ℝ)) + (46 : ℝ)) := badd sGlobal60_hz26 (bpoint (46 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal60_hz28 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal60_hz25 sGlobal60_hz27 (by norm_num) (by norm_num)

theorem sGlobal60_hz29 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (s3rs 12225 46 maskSlack) := by
    convert sGlobal60_hz28 using 1 <;>
      norm_num [s3rs, s3pp, s3K, mA, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal60_hz30 : B (490797546012267 / 1000000000000000000) (49079754601227 / 100000000000000000) ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (3 : ℝ)) sGlobal60_hz10 (by norm_num) (by norm_num)

theorem sGlobal60_hz31 : B (490797546012267 / 500000000000000000) (49079754601227 / 50000000000000000) ((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal60_hz30 (by norm_num) (by norm_num)

theorem sGlobal60_hz32 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal60_hz31 sGlobal60_hz27 (by norm_num) (by norm_num)

theorem sGlobal60_hz33 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (s3r1 12225 46) := by
    convert sGlobal60_hz32 using 1 <;>
      norm_num [s3r1, mA] <;> ring

theorem sGlobal60_hz34 : B (163599182004089 / 500000000000000000) (16359918200409 / 50000000000000000) ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (2 : ℝ)) sGlobal60_hz10 (by norm_num) (by norm_num)

theorem sGlobal60_hz35 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal60_hz34 (by norm_num) (by norm_num)

theorem sGlobal60_hz36 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal60_hz35 sGlobal60_hz27 (by norm_num) (by norm_num)

theorem sGlobal60_hz37 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (s3rpp 12225 46) := by
    convert sGlobal60_hz36 using 1 <;>
      norm_num [s3rpp, mA] <;> ring

theorem sGlobal60_hz38 {c : ℝ} (hc : B (129 / 200) (13 / 20) c) : B (129 / 200) (13 / 20) c := hc

theorem sGlobal60_hz39 : B (72314264149627533 / 100000000000000000) (723142641496275333 / 1000000000000000000) (kdot ((129 / 200))) := by
    constructor
    · apply bkdot_lower (q := (92909734931194387 / 200000000000000000)) (a := (434886521783788547 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (232274337327985967 / 500000000000000000)) (a := (434886521783788543 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal60_hz40 : B (16641 / 40000) (16641 / 40000) (((129 / 200) : ℝ)^2) := bsq (bpoint ((129 / 200) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal60_hz41 : B (23359 / 40000) (23359 / 40000) ((1 : ℝ) - (((129 / 200) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal60_hz40 (by norm_num) (by norm_num)

theorem sGlobal60_hz42 : B (764182569809073831 / 1000000000000000000) (95522821226134229 / 125000000000000000) (√((1 : ℝ) - (((129 / 200) : ℝ)^2))) := bsqrt sGlobal60_hz41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal60_hz43 : B (3040585835244537 / 12500000000000000) (243246866819562961 / 1000000000000000000) ((√((1 : ℝ) - (((129 / 200) : ℝ)^2))) / Real.pi) := bdiv sGlobal60_hz42 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal60_hz44 : B (466427003765097587 / 1000000000000000000) (46642700376509759 / 100000000000000000) (((129 / 200) : ℝ) * (kdot ((129 / 200)))) := bmul (bpoint ((129 / 200) : ℝ)) sGlobal60_hz39 (by norm_num) (by norm_num)

theorem sGlobal60_hz45 : B (709673870584660547 / 1000000000000000000) (709673870584660551 / 1000000000000000000) (((√((1 : ℝ) - (((129 / 200) : ℝ)^2))) / Real.pi) + (((129 / 200) : ℝ) * (kdot ((129 / 200))))) := badd sGlobal60_hz43 sGlobal60_hz44 (by norm_num) (by norm_num)

theorem sGlobal60_hz46 : B (709673870584660547 / 1000000000000000000) (709673870584660551 / 1000000000000000000) (kappa ((129 / 200))) := by rw [kappa_eq]; exact sGlobal60_hz45

theorem sGlobal60_hz47 : B (181307780379867391 / 250000000000000000) (708233517108857 / 976562500000000) (kdot ((13 / 20))) := by
    constructor
    · apply bkdot_lower (q := (115141546617959573 / 250000000000000000)) (a := (431605945034770523 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (460566186471838291 / 1000000000000000000)) (a := (431605945034770519 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal60_hz48 : B (169 / 400) (169 / 400) (((13 / 20) : ℝ)^2) := bsq (bpoint ((13 / 20) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal60_hz49 : B (231 / 400) (231 / 400) ((1 : ℝ) - (((13 / 20) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal60_hz48 (by norm_num) (by norm_num)

theorem sGlobal60_hz50 : B (759934207678533181 / 1000000000000000000) (379967103839266591 / 500000000000000000) (√((1 : ℝ) - (((13 / 20) : ℝ)^2))) := bsqrt sGlobal60_hz49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal60_hz51 : B (241894571153323039 / 1000000000000000000) (241894571153323041 / 1000000000000000000) ((√((1 : ℝ) - (((13 / 20) : ℝ)^2))) / Real.pi) := bdiv sGlobal60_hz50 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal60_hz52 : B (29462514311728451 / 62500000000000000) (23570011449382761 / 50000000000000000) (((13 / 20) : ℝ) * (kdot ((13 / 20)))) := bmul (bpoint ((13 / 20) : ℝ)) sGlobal60_hz47 (by norm_num) (by norm_num)

theorem sGlobal60_hz53 : B (142658960028195651 / 200000000000000000) (713294800140978261 / 1000000000000000000) (((√((1 : ℝ) - (((13 / 20) : ℝ)^2))) / Real.pi) + (((13 / 20) : ℝ) * (kdot ((13 / 20))))) := badd sGlobal60_hz51 sGlobal60_hz52 (by norm_num) (by norm_num)

theorem sGlobal60_hz54 : B (142658960028195651 / 200000000000000000) (713294800140978261 / 1000000000000000000) (kappa ((13 / 20))) := by rw [kappa_eq]; exact sGlobal60_hz53

theorem sGlobal60_hz55 {c : ℝ} (hc : B (129 / 200) (13 / 20) c) : B (709673870584660547 / 1000000000000000000) (713294800140978261 / 1000000000000000000) (kappa c) := bkappa (sGlobal60_hz38 hc) (by norm_num) (by norm_num) sGlobal60_hz46.1 sGlobal60_hz54.2

theorem sGlobal60_hz56 : B 24450 24450 ((2 : ℝ) * (12225 : ℝ)) := bmul (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal60_hz57 {c : ℝ} (hc : B (129 / 200) (13 / 20) c) : B (286705199859021739 / 1000000000000000000) (290326129415339453 / 1000000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (sGlobal60_hz55 hc) (by norm_num) (by norm_num)

theorem sGlobal60_hz58 {c : ℝ} (hc : B (129 / 200) (13 / 20) c) : B (140198842731061630371 / 20000000000000000) (141969477284100992517 / 20000000000000000) (((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) := bmul sGlobal60_hz56 (sGlobal60_hz57 hc) (by norm_num) (by norm_num)

theorem sGlobal60_hz59 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (4 : ℝ)) sGlobal60_hz10 (by norm_num) (by norm_num)

theorem sGlobal60_hz60 {c : ℝ} (hc : B (129 / 200) (13 / 20) c) : B (700994148215635350219 / 100000000000000000) (3549236604904160804747 / 500000000000000000) ((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bsub (sGlobal60_hz58 hc) sGlobal60_hz59 (by norm_num) (by norm_num)

theorem sGlobal60_hz61 {c : ℝ} (hc : B (129 / 200) (13 / 20) c) : B (16745078658706089819 / 200000000000000000) (84252437411675643519 / 1000000000000000000) (√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) := bsqrt (sGlobal60_hz60 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal60_hz62 : B (30670756373515103 / 125000000000000000) (122683025494060423 / 500000000000000000) ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal60_hz7 (by norm_num) (by norm_num)

theorem sGlobal60_hz63 {c : ℝ} (hc : B (129 / 200) (13 / 20) c) : B (83480027242542328249 / 1000000000000000000) (16801414272137504539 / 200000000000000000) ((√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) - ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))))) := bsub (sGlobal60_hz61 hc) sGlobal60_hz62 (by norm_num) (by norm_num)

theorem sGlobal60_hz64 {c : ℝ} (hc : B (129 / 200) (13 / 20) c) : B (83480027242542328249 / 1000000000000000000) (16801414272137504539 / 200000000000000000) (s3dm 12225 46 c) := by
    convert (sGlobal60_hz63 hc) using 1 <;>
      norm_num [s3dm, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal60_hz65 : B (6126072185528622723889 / 500000000000000000) (2450428874211449090087 / 200000000000000000) ((s3ap 12225 46)^2) := bsq sGlobal60_hz9 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal60_hz66 : B (6126072185528622723889 / 250000000000000000) (2450428874211449090087 / 100000000000000000) ((2 : ℝ) * ((s3ap 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal60_hz65 (by norm_num) (by norm_num)

theorem sGlobal60_hz67 {c : ℝ} (hc : B (129 / 200) (13 / 20) c) : B (1393782989683121856113 / 200000000000000000) (3528594019299822892901 / 500000000000000000) ((s3dm 12225 46 c)^2) := bsq (sGlobal60_hz64 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal60_hz68 {c : ℝ} (hc : B (129 / 200) (13 / 20) c) : B (8723550351757422554877 / 500000000000000000) (3507074758739776324061 / 200000000000000000) (((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) := bsub sGlobal60_hz66 (sGlobal60_hz67 hc) (by norm_num) (by norm_num)

theorem sGlobal60_hz69 : B (1524735695971823534271 / 125000000000000000) (609894278388729413841 / 50000000000000000) ((s3am 12225 46)^2) := bsq sGlobal60_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal60_hz70 : B (1524735695971823534271 / 62500000000000000) (609894278388729413841 / 25000000000000000) ((2 : ℝ) * ((s3am 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal60_hz69 (by norm_num) (by norm_num)

theorem sGlobal60_hz71 {c : ℝ} (hc : B (129 / 200) (13 / 20) c) : B (178792264923439681 / 250000000000000000) (359393718203614809 / 500000000000000000) ((((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) / ((2 : ℝ) * ((s3am 12225 46)^2))) := bdiv (sGlobal60_hz68 hc) sGlobal60_hz70 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal60_hz72 {c : ℝ} (hc : B (129 / 200) (13 / 20) c) : B (178792264923439681 / 250000000000000000) (359393718203614809 / 500000000000000000) (s3c1 12225 46 c) := by
    convert (sGlobal60_hz71 hc) using 1 <;>
      norm_num [s3c1] <;> ring

theorem sGlobal60_hz73 {c : ℝ} (hc : B (129 / 200) (13 / 20) c) : B (72314264149627533 / 100000000000000000) (708233517108857 / 976562500000000) (kdot c) := bkdot (sGlobal60_hz38 hc) sGlobal60_hz39.1 sGlobal60_hz47.2

theorem sGlobal60_hz74 : B (18841257767970763 / 25000000000000000) (376825155359415261 / 500000000000000000) (kdot ((178792264923439681 / 250000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (101877932673656941 / 250000000000000000)) (a := (77393037405985027 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (407511730694627763 / 1000000000000000000)) (a := (386965187029925133 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal60_hz75 : B (188825638160773087 / 250000000000000000) (15106051052861847 / 20000000000000000) (kdot ((359393718203614809 / 500000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (2528053682650867 / 6250000000000000)) (a := (384369851484318123 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (404488589224138719 / 1000000000000000000)) (a := (384369851484318121 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal60_hz76 {c : ℝ} (hc : B (129 / 200) (13 / 20) c) : B (18841257767970763 / 25000000000000000) (15106051052861847 / 20000000000000000) (kdot (s3c1 12225 46 c)) := bkdot (sGlobal60_hz72 hc) sGlobal60_hz74.1 sGlobal60_hz75.2

theorem sGlobal60_hz77 {c : ℝ} (hc : B (129 / 200) (13 / 20) c) : B (16641 / 40000) (169 / 400) (c^2) := bsq (sGlobal60_hz38 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal60_hz78 {c : ℝ} (hc : B (129 / 200) (13 / 20) c) : B (231 / 400) (23359 / 40000) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (sGlobal60_hz77 hc) (by norm_num) (by norm_num)

theorem sGlobal60_hz79 {c : ℝ} (hc : B (129 / 200) (13 / 20) c) : B (759934207678533181 / 1000000000000000000) (95522821226134229 / 125000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (sGlobal60_hz78 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal60_hz80 : B (39119999999999765769 / 1600000000000000) (3912000000000000489 / 160000000000000) ((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (149450625 : ℝ)) sGlobal60_hz10 (by norm_num) (by norm_num)

theorem sGlobal60_hz81 {c : ℝ} (hc : B (129 / 200) (13 / 20) c) : B (549540830304033563 / 1000000000000000000) (554208982148264961 / 1000000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (sGlobal60_hz79 hc) (sGlobal60_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal60_hz82 {c : ℝ} (hc : B (129 / 200) (13 / 20) c) : B (13436273300933540165663 / 1000000000000000000) (3387602403381269997563 / 250000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) := bmul sGlobal60_hz80 (sGlobal60_hz81 hc) (by norm_num) (by norm_num)

theorem sGlobal60_hz83 {c : ℝ} (hc : B (129 / 200) (13 / 20) c) : B (6718136650466770082831 / 1000000000000000000) (3387602403381269997563 / 500000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) / (2 : ℝ)) := bdiv (sGlobal60_hz82 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal60_hz84 {c : ℝ} (hc : B (129 / 200) (13 / 20) c) : B (6718136650466770082831 / 1000000000000000000) (3387602403381269997563 / 500000000000000000) (s3Cpa 12225 c) := by
    convert (sGlobal60_hz83 hc) using 1 <;>
      norm_num [s3Cpa, mA] <;> ring

theorem sGlobal60_hz85 {c : ℝ} (hc : B (129 / 200) (13 / 20) c) : B (241894571153323039 / 1000000000000000000) (243246866819562961 / 1000000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (sGlobal60_hz79 hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal60_hz86 {c : ℝ} (hc : B (129 / 200) (13 / 20) c) : B (466427003765097587 / 1000000000000000000) (23570011449382761 / 50000000000000000) (c * (kdot c)) := bmul (sGlobal60_hz38 hc) (sGlobal60_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal60_hz87 {c : ℝ} (hc : B (129 / 200) (13 / 20) c) : B (-229505657834332181 / 1000000000000000000) (-111590068472767313 / 500000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (sGlobal60_hz85 hc) (sGlobal60_hz86 hc) (by norm_num) (by norm_num)

theorem sGlobal60_hz88 {c : ℝ} (hc : B (129 / 200) (13 / 20) c) : B (-5611413334049422526877 / 1000000000000000000) (-5456754348318288933383 / 1000000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) := bmul sGlobal60_hz80 (sGlobal60_hz87 hc) (by norm_num) (by norm_num)

theorem sGlobal60_hz89 {c : ℝ} (hc : B (129 / 200) (13 / 20) c) : B (-2805706667024711263439 / 1000000000000000000) (-2728377174159144466691 / 1000000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) / (2 : ℝ)) := bdiv (sGlobal60_hz88 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal60_hz90 {c : ℝ} (hc : B (129 / 200) (13 / 20) c) : B (-2805706667024711263439 / 1000000000000000000) (-2728377174159144466691 / 1000000000000000000) (s3Cpp 12225 c) := by
    convert (sGlobal60_hz89 hc) using 1 <;>
      norm_num [s3Cpp, mA] <;> ring

theorem sGlobal60_hz91 {c : ℝ} (hc : B (129 / 200) (13 / 20) c) : B (53385013753128967119 / 7812500000000000) (861293739587034800919 / 125000000000000000) ((s3Cpa 12225 c) + (s3r1 12225 46)) := badd (sGlobal60_hz84 hc) sGlobal60_hz33 (by norm_num) (by norm_num)

theorem sGlobal60_hz92 {c : ℝ} (hc : B (129 / 200) (13 / 20) c) : B (30935493999904746001 / 500000000000000000) (12477540717870735449 / 200000000000000000) (((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) := bdiv (sGlobal60_hz91 hc) sGlobal60_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal60_hz93 {c : ℝ} (hc : B (129 / 200) (13 / 20) c) : B (30996835512651776207 / 500000000000000000) (15627596653711934417 / 250000000000000000) ((((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) + (s3e0 12225 46)) := badd (sGlobal60_hz92 hc) sGlobal60_hz16 (by norm_num) (by norm_num)

theorem sGlobal60_hz94 {c : ℝ} (hc : B (129 / 200) (13 / 20) c) : B (30996835512651776207 / 500000000000000000) (15627596653711934417 / 250000000000000000) (s3Lam 12225 46 c) := by
    convert (sGlobal60_hz93 hc) using 1 <;>
      norm_num [s3Lam] <;> ring

theorem sGlobal60_hz95 {c : ℝ} (hc : B (129 / 200) (13 / 20) c) : B (-2728943260402219457839 / 1000000000000000000) (-2651613767536652191873 / 1000000000000000000) ((s3Cpp 12225 c) + (s3rpp 12225 46)) := badd (sGlobal60_hz90 hc) sGlobal60_hz37 (by norm_num) (by norm_num)

theorem sGlobal60_hz96 {c : ℝ} (hc : B (129 / 200) (13 / 20) c) : B (-2061177810599959437319 / 1000000000000000000) (-20715732558880095249 / 15625000000000000) (if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) := bweaken (bfirst (sGlobal60_hz95 hc) (sGlobal60_hz76 hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem sGlobal60_hz97 {c : ℝ} (hc : B (129 / 200) (13 / 20) c) : B (3843215247193561207609 / 1000000000000000000) (781509686947547040749 / 200000000000000000) ((s3Lam 12225 46 c)^2) := bsq (sGlobal60_hz94 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal60_hz98 {c : ℝ} (hc : B (129 / 200) (13 / 20) c) : B (511466783943255029 / 1000000000000000000) (516655378736877163 / 1000000000000000000) ((s3c1 12225 46 c)^2) := bsq (sGlobal60_hz72 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal60_hz99 {c : ℝ} (hc : B (129 / 200) (13 / 20) c) : B (483344621263122837 / 1000000000000000000) (488533216056744971 / 1000000000000000000) ((1 : ℝ) - ((s3c1 12225 46 c)^2)) := bsub (bpoint (1 : ℝ)) (sGlobal60_hz98 hc) (by norm_num) (by norm_num)

theorem sGlobal60_hz100 {c : ℝ} (hc : B (129 / 200) (13 / 20) c) : B (695229905328534351 / 1000000000000000000) (87368938993710117 / 125000000000000000) (√((1 : ℝ) - ((s3c1 12225 46 c)^2))) := bsqrt (sGlobal60_hz99 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal60_hz101 {c : ℝ} (hc : B (129 / 200) (13 / 20) c) : B (436825832627210193 / 200000000000000000) (219582093515659621 / 100000000000000000) (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))) := bmul pi_mem (sGlobal60_hz100 hc) (by norm_num) (by norm_num)

theorem sGlobal60_hz102 {c : ℝ} (hc : B (129 / 200) (13 / 20) c) : B (437560183717744742007 / 250000000000000000) (1789064722311173692171 / 1000000000000000000) (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2))))) := bdiv (sGlobal60_hz97 hc) (sGlobal60_hz101 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal60_hz103 {c : ℝ} (hc : B (129 / 200) (13 / 20) c) : B (-310937075728980469291 / 1000000000000000000) (92651567708569519247 / 200000000000000000) ((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) := badd (sGlobal60_hz96 hc) (sGlobal60_hz102 hc) (by norm_num) (by norm_num)

theorem sGlobal60_hz104 : B (3762781186094069 / 250000000000000000) (376278118609407 / 25000000000000000) ((s3e0 12225 46)^2) := bsq sGlobal60_hz16 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal60_hz105 {c : ℝ} (hc : B (129 / 200) (13 / 20) c) : B (-62184404920847218603 / 200000000000000000) (92654577933518394503 / 200000000000000000) (((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) := badd (sGlobal60_hz103 hc) sGlobal60_hz104 (by norm_num) (by norm_num)

theorem sGlobal60_hz106 {c : ℝ} (hc : B (129 / 200) (13 / 20) c) : B (-68106237788247205721 / 250000000000000000) (501769963121716242531 / 1000000000000000000) ((((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) + (s3rs 12225 46 maskSlack)) := badd (sGlobal60_hz105 hc) sGlobal60_hz29 (by norm_num) (by norm_num)

theorem sGlobal60_hz107 {c : ℝ} (hc : B (129 / 200) (13 / 20) c) : B (-68106237788247205721 / 250000000000000000) (501769963121716242531 / 1000000000000000000) (s3U 12225 46 maskSlack c) := by
    convert (sGlobal60_hz106 hc) using 1 <;>
      norm_num [s3U] <;> ring

theorem sGlobal60_hz108 {c : ℝ} (hc : B (129 / 200) (13 / 20) c) : B (-2882470073647203538257 / 1000000000000000000) (-2805140580781636272291 / 1000000000000000000) ((s3Cpp 12225 c) - (s3rpp 12225 46)) := bsub (sGlobal60_hz90 hc) sGlobal60_hz37 (by norm_num) (by norm_num)

theorem sGlobal60_hz109 {c : ℝ} (hc : B (129 / 200) (13 / 20) c) : B (-2882470073647203538257 / 1000000000000000000) (-2805140580781636272291 / 1000000000000000000) (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ)) := bweaken (bmin (sGlobal60_hz108 hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem sGlobal60_hz110 {c : ℝ} (hc : B (129 / 200) (13 / 20) c) : B (-272142125567881904197 / 125000000000000000) (-84563802812643235251 / 40000000000000000) ((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) := bmul (sGlobal60_hz76 hc) (sGlobal60_hz109 hc) (by norm_num) (by norm_num)

theorem sGlobal60_hz111 {c : ℝ} (hc : B (129 / 200) (13 / 20) c) : B (-4252250108726171113 / 1953125000000000) (-2114110121440825257551 / 1000000000000000000) (((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) := bsub (sGlobal60_hz110 hc) sGlobal60_hz104 (by norm_num) (by norm_num)

theorem sGlobal60_hz112 {c : ℝ} (hc : B (129 / 200) (13 / 20) c) : B (-34619517642530060623 / 15625000000000000) (-1076303597446036263841 / 500000000000000000) ((((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) - (s3rs 12225 46 maskSlack)) := bsub (sGlobal60_hz111 hc) sGlobal60_hz29 (by norm_num) (by norm_num)

theorem sGlobal60_hz113 {c : ℝ} (hc : B (129 / 200) (13 / 20) c) : B (-34619517642530060623 / 15625000000000000) (-1076303597446036263841 / 500000000000000000) (s3L 12225 46 maskSlack c) := by
    convert (sGlobal60_hz112 hc) using 1 <;>
      norm_num [s3L] <;> ring

theorem sGlobal60_hz114 {c : ℝ} (hc : B (129 / 200) (13 / 20) c) : B 0 (501769963121716242531 / 1000000000000000000) |(s3U 12225 46 maskSlack c)| := bweaken (babs (sGlobal60_hz107 hc)) (by norm_num) (by norm_num)

theorem sGlobal60_hz115 {c : ℝ} (hc : B (129 / 200) (13 / 20) c) : B 0 (34619517642530060623 / 15625000000000000) |(s3L 12225 46 maskSlack c)| := bweaken (babs (sGlobal60_hz113 hc)) (by norm_num) (by norm_num)

theorem sGlobal60_hz116 {c : ℝ} (hc : B (129 / 200) (13 / 20) c) : B 0 (34619517642530060623 / 15625000000000000) (max |(s3U 12225 46 maskSlack c)| |(s3L 12225 46 maskSlack c)|) := bweaken (bmax (sGlobal60_hz114 hc) (sGlobal60_hz115 hc)) (by norm_num) (by norm_num)

theorem sGlobal60_hz117 {c : ℝ} (hc : B (129 / 200) (13 / 20) c) : B 0 (34619517642530060623 / 15625000000000000) (s3nks 12225 46 maskSlack c) := by
    convert (sGlobal60_hz116 hc) using 1 <;>
      norm_num [s3nks] <;> ring

theorem sGlobal60 {c : ℝ} (hc : B (129 / 200) (13 / 20) c) :
    0 < s3am 12225 46 ∧ 0 ≤ s3dm 12225 46 c ∧
    s3dm 12225 46 c ^ 2 ≤ 2 * s3ap 12225 46 ^ 2 ∧ s3c1 12225 46 c < 1 ∧
    0 ≤ s3Cpa 12225 c - s3r1 12225 46 ∧
    s3e0 12225 46 ≤ (s3Cpa 12225 c - s3r1 12225 46) / s3ap 12225 46 ∧
    s3nks 12225 46 maskSlack c ≤ 12225 * (4531 / 25000) := by

  refine ⟨lt_of_lt_of_le (by norm_num) sGlobal60_hz14.1,
    le_trans (by norm_num) (sGlobal60_hz64 hc).1, ?_,
    lt_of_le_of_lt (sGlobal60_hz72 hc).2 (by norm_num), ?_, ?_,
    le_trans (sGlobal60_hz117 hc).2 (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (sGlobal60_hz64 hc).1) (sGlobal60_hz64 hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) sGlobal60_hz9.1 2
    nlinarith only [h1, h2]
  · linarith only [(sGlobal60_hz84 hc).1, sGlobal60_hz33.2]
  · have hap : 0 < s3ap 12225 46 := lt_of_lt_of_le (by norm_num) sGlobal60_hz9.1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul sGlobal60_hz16.2 sGlobal60_hz9.2 (le_trans (by norm_num) sGlobal60_hz9.1) (by norm_num)
    linarith only [h, (sGlobal60_hz84 hc).1, sGlobal60_hz33.2]

end BstLean.Part255
