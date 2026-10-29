import BstLean.Part255SGlobal57
import BstLean.Part255Numeric10
namespace BstLean.Part255
open Real BstLean.Part130 BstLean.Part182 BstLean.Part197 BstLean.Part246
theorem sGlobal61_hz0 : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal61_hz1 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) ((√(23 : ℝ)) / (12225 : ℝ)) := bdiv sGlobal61_hz0 (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal61_hz2 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) maskSlack := by
    convert sGlobal61_hz1 using 1 <;>
      norm_num [maskSlack] <;> ring

theorem sGlobal61_hz3 : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal61_hz4 : B (6395294793910793 / 500000000000000000) (12790589587821587 / 1000000000000000000) (√((2 / 12225) : ℝ)) := bsqrt (bpoint ((2 / 12225) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal61_hz5 : B (7230130686979 / 62500000000000000) (23136418198333 / 200000000000000000) (√((2 / 149450625) : ℝ)) := bsqrt (bpoint ((2 / 149450625) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal61_hz6 : B (2211334438749598093 / 20000000000000000) (110566721937479904651 / 1000000000000000000) (√(12225 : ℝ)) := bsqrt (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal61_hz7 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))) := bmul sGlobal61_hz3 sGlobal61_hz4 (by norm_num) (by norm_num)

theorem sGlobal61_hz8 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) ((√(12225 : ℝ)) + ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := badd sGlobal61_hz6 sGlobal61_hz7 (by norm_num) (by norm_num)

theorem sGlobal61_hz9 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) (s3ap 12225 46) := by
    convert sGlobal61_hz8 using 1 <;>
      norm_num [s3ap, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal61_hz10 : B (163599182004089 / 1000000000000000000) (16359918200409 / 100000000000000000) ((2 : ℝ) / (12225 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal61_hz11 : B (1222499983640081799591 / 100000000000000000) (12224999836400817995911 / 1000000000000000000) ((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ))) := bsub (bpoint (12225 : ℝ)) sGlobal61_hz10 (by norm_num) (by norm_num)

theorem sGlobal61_hz12 : B (110566721197658827907 / 1000000000000000000) (27641680299414706977 / 250000000000000000) (√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) := bsqrt sGlobal61_hz11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal61_hz13 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) ((√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) - ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bsub sGlobal61_hz12 sGlobal61_hz7 (by norm_num) (by norm_num)

theorem sGlobal61_hz14 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) (s3am 12225 46) := by
    convert sGlobal61_hz13 using 1 <;>
      norm_num [s3am, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal61_hz15 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√((2 / 12225) : ℝ)) * (√(92 : ℝ))) := bmul sGlobal61_hz4 sGlobal61_hz3 (by norm_num) (by norm_num)

theorem sGlobal61_hz16 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) (s3e0 12225 46) := by
    convert sGlobal61_hz15 using 1 <;>
      norm_num [s3e0, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal61_hz17 : B (250196148528560847 / 500000000000000000) (100078459411424339 / 200000000000000000) (((1 / 2) : ℝ) + maskSlack) := badd (bpoint ((1 / 2) : ℝ)) sGlobal61_hz2 (by norm_num) (by norm_num)

theorem sGlobal61_hz18 : B (59827153232297998295487 / 800000000000000) (23930861292919199366019 / 320000000000000) ((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack)) := bmul (bpoint (149450625 : ℝ)) sGlobal61_hz17 (by norm_num) (by norm_num)

theorem sGlobal61_hz19 : B (1729554180017180009583 / 200000000000000000) (8647770900085900056557 / 1000000000000000000) (√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) := bsqrt sGlobal61_hz18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal61_hz20 : B (4328681281566262743499 / 500000000000000000) (8657362563132525495641 / 1000000000000000000) ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))) := badd sGlobal61_hz19 sGlobal61_hz3 (by norm_num) (by norm_num)

theorem sGlobal61_hz21 : B (110732771457999278473 / 1000000000000000000) (55366385728999643621 / 500000000000000000) ((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ)))) := bmul sGlobal61_hz4 sGlobal61_hz20 (by norm_num) (by norm_num)

theorem sGlobal61_hz22 : B (209099159 / 15625000000000000) (13382346177 / 1000000000000000000) ((2 : ℝ) / (149450625 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (149450625 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal61_hz23 : B (2452349334953899930479 / 200000000000000000) (12261746674769501594427 / 1000000000000000000) (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2) := bsq sGlobal61_hz21 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal61_hz24 : B (82045469362091 / 500000000000000000) (32818187747289 / 200000000000000000) (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2)) := bmul sGlobal61_hz22 sGlobal61_hz23 (by norm_num) (by norm_num)

theorem sGlobal61_hz25 : B (82045469362091 / 250000000000000000) (32818187747289 / 100000000000000000) ((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) := bmul (bpoint (2 : ℝ)) sGlobal61_hz24 (by norm_num) (by norm_num)

theorem sGlobal61_hz26 : B (117258080744995992792057 / 1000000000000000000) (58629040372497996396029 / 500000000000000000) (√(13749457500 : ℝ)) := bsqrt (bpoint (13749457500 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal61_hz27 : B (117304080744995992792057 / 1000000000000000000) (58652040372497996396029 / 500000000000000000) ((√(13749457500 : ℝ)) + (46 : ℝ)) := badd sGlobal61_hz26 (bpoint (46 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal61_hz28 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal61_hz25 sGlobal61_hz27 (by norm_num) (by norm_num)

theorem sGlobal61_hz29 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (s3rs 12225 46 maskSlack) := by
    convert sGlobal61_hz28 using 1 <;>
      norm_num [s3rs, s3pp, s3K, mA, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal61_hz30 : B (490797546012267 / 1000000000000000000) (49079754601227 / 100000000000000000) ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (3 : ℝ)) sGlobal61_hz10 (by norm_num) (by norm_num)

theorem sGlobal61_hz31 : B (490797546012267 / 500000000000000000) (49079754601227 / 50000000000000000) ((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal61_hz30 (by norm_num) (by norm_num)

theorem sGlobal61_hz32 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal61_hz31 sGlobal61_hz27 (by norm_num) (by norm_num)

theorem sGlobal61_hz33 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (s3r1 12225 46) := by
    convert sGlobal61_hz32 using 1 <;>
      norm_num [s3r1, mA] <;> ring

theorem sGlobal61_hz34 : B (163599182004089 / 500000000000000000) (16359918200409 / 50000000000000000) ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (2 : ℝ)) sGlobal61_hz10 (by norm_num) (by norm_num)

theorem sGlobal61_hz35 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal61_hz34 (by norm_num) (by norm_num)

theorem sGlobal61_hz36 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal61_hz35 sGlobal61_hz27 (by norm_num) (by norm_num)

theorem sGlobal61_hz37 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (s3rpp 12225 46) := by
    convert sGlobal61_hz36 using 1 <;>
      norm_num [s3rpp, mA] <;> ring

theorem sGlobal61_hz38 {c : ℝ} (hc : B (13 / 20) (131 / 200) c) : B (13 / 20) (131 / 200) c := hc

theorem sGlobal61_hz39 : B (181307780379867391 / 250000000000000000) (708233517108857 / 976562500000000) (kdot ((13 / 20))) := by
    constructor
    · apply bkdot_lower (q := (115141546617959573 / 250000000000000000)) (a := (431605945034770523 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (460566186471838291 / 1000000000000000000)) (a := (431605945034770519 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal61_hz40 : B (169 / 400) (169 / 400) (((13 / 20) : ℝ)^2) := bsq (bpoint ((13 / 20) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal61_hz41 : B (231 / 400) (231 / 400) ((1 : ℝ) - (((13 / 20) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal61_hz40 (by norm_num) (by norm_num)

theorem sGlobal61_hz42 : B (759934207678533181 / 1000000000000000000) (379967103839266591 / 500000000000000000) (√((1 : ℝ) - (((13 / 20) : ℝ)^2))) := bsqrt sGlobal61_hz41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal61_hz43 : B (241894571153323039 / 1000000000000000000) (241894571153323041 / 1000000000000000000) ((√((1 : ℝ) - (((13 / 20) : ℝ)^2))) / Real.pi) := bdiv sGlobal61_hz42 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal61_hz44 : B (29462514311728451 / 62500000000000000) (23570011449382761 / 50000000000000000) (((13 / 20) : ℝ) * (kdot ((13 / 20)))) := bmul (bpoint ((13 / 20) : ℝ)) sGlobal61_hz39 (by norm_num) (by norm_num)

theorem sGlobal61_hz45 : B (142658960028195651 / 200000000000000000) (713294800140978261 / 1000000000000000000) (((√((1 : ℝ) - (((13 / 20) : ℝ)^2))) / Real.pi) + (((13 / 20) : ℝ) * (kdot ((13 / 20))))) := badd sGlobal61_hz43 sGlobal61_hz44 (by norm_num) (by norm_num)

theorem sGlobal61_hz46 : B (142658960028195651 / 200000000000000000) (713294800140978261 / 1000000000000000000) (kappa ((13 / 20))) := by rw [kappa_eq]; exact sGlobal61_hz45

theorem sGlobal61_hz47 : B (363665694319129201 / 500000000000000000) (145466277727651681 / 200000000000000000) (kdot ((131 / 200))) := by
    constructor
    · apply bkdot_lower (q := (228286669837241359 / 500000000000000000)) (a := (107076713289822229 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (456573339674482717 / 1000000000000000000)) (a := (428306853159288913 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal61_hz48 : B (17161 / 40000) (17161 / 40000) (((131 / 200) : ℝ)^2) := bsq (bpoint ((131 / 200) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal61_hz49 : B (22839 / 40000) (22839 / 40000) ((1 : ℝ) - (((131 / 200) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal61_hz48 (by norm_num) (by norm_num)

theorem sGlobal61_hz50 : B (23613402411289653 / 31250000000000000) (755628877161268897 / 1000000000000000000) (√((1 : ℝ) - (((131 / 200) : ℝ)^2))) := bsqrt sGlobal61_hz49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal61_hz51 : B (60131035471597261 / 250000000000000000) (48104828377277809 / 200000000000000000) ((√((1 : ℝ) - (((131 / 200) : ℝ)^2))) / Real.pi) := bdiv sGlobal61_hz50 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal61_hz52 : B (476402059558059253 / 1000000000000000000) (59550257444757407 / 125000000000000000) (((131 / 200) : ℝ) * (kdot ((131 / 200)))) := bmul (bpoint ((131 / 200) : ℝ)) sGlobal61_hz47 (by norm_num) (by norm_num)

theorem sGlobal61_hz53 : B (716926201444448297 / 1000000000000000000) (716926201444448301 / 1000000000000000000) (((√((1 : ℝ) - (((131 / 200) : ℝ)^2))) / Real.pi) + (((131 / 200) : ℝ) * (kdot ((131 / 200))))) := badd sGlobal61_hz51 sGlobal61_hz52 (by norm_num) (by norm_num)

theorem sGlobal61_hz54 : B (716926201444448297 / 1000000000000000000) (716926201444448301 / 1000000000000000000) (kappa ((131 / 200))) := by rw [kappa_eq]; exact sGlobal61_hz53

theorem sGlobal61_hz55 {c : ℝ} (hc : B (13 / 20) (131 / 200) c) : B (142658960028195651 / 200000000000000000) (716926201444448301 / 1000000000000000000) (kappa c) := bkappa (sGlobal61_hz38 hc) (by norm_num) (by norm_num) sGlobal61_hz46.1 sGlobal61_hz54.2

theorem sGlobal61_hz56 : B 24450 24450 ((2 : ℝ) * (12225 : ℝ)) := bmul (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal61_hz57 {c : ℝ} (hc : B (13 / 20) (131 / 200) c) : B (283073798555551699 / 1000000000000000000) (57341039971804349 / 200000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (sGlobal61_hz55 hc) (by norm_num) (by norm_num)

theorem sGlobal61_hz58 {c : ℝ} (hc : B (13 / 20) (131 / 200) c) : B (138423087493664780811 / 20000000000000000) (28039768546212326661 / 4000000000000000) (((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) := bmul sGlobal61_hz56 (sGlobal61_hz57 hc) (by norm_num) (by norm_num)

theorem sGlobal61_hz59 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (4 : ℝ)) sGlobal61_hz10 (by norm_num) (by norm_num)

theorem sGlobal61_hz60 {c : ℝ} (hc : B (13 / 20) (131 / 200) c) : B (692115372028651102419 / 100000000000000000) (3504970741078176824447 / 500000000000000000) ((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bsub (sGlobal61_hz58 hc) sGlobal61_hz59 (by norm_num) (by norm_num)

theorem sGlobal61_hz61 {c : ℝ} (hc : B (13 / 20) (131 / 200) c) : B (20798367905148397461 / 250000000000000000) (20931348323382612493 / 250000000000000000) (√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) := bsqrt (sGlobal61_hz60 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal61_hz62 : B (30670756373515103 / 125000000000000000) (122683025494060423 / 500000000000000000) ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal61_hz7 (by norm_num) (by norm_num)

theorem sGlobal61_hz63 {c : ℝ} (hc : B (13 / 20) (131 / 200) c) : B (41474052784802734499 / 500000000000000000) (20870006810635582287 / 250000000000000000) ((√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) - ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))))) := bsub (sGlobal61_hz61 hc) sGlobal61_hz62 (by norm_num) (by norm_num)

theorem sGlobal61_hz64 {c : ℝ} (hc : B (13 / 20) (131 / 200) c) : B (41474052784802734499 / 500000000000000000) (20870006810635582287 / 250000000000000000) (s3dm 12225 46 c) := by
    convert (sGlobal61_hz63 hc) using 1 <;>
      norm_num [s3dm, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal61_hz65 : B (6126072185528622723889 / 500000000000000000) (2450428874211449090087 / 200000000000000000) ((s3ap 12225 46)^2) := bsq sGlobal61_hz9 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal61_hz66 : B (6126072185528622723889 / 250000000000000000) (2450428874211449090087 / 100000000000000000) ((2 : ℝ) * ((s3ap 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal61_hz65 (by norm_num) (by norm_num)

theorem sGlobal61_hz67 {c : ℝ} (hc : B (13 / 20) (131 / 200) c) : B (6880388217586413826491 / 1000000000000000000) (6968914948415609430663 / 1000000000000000000) ((s3dm 12225 46 c)^2) := bsq (sGlobal61_hz64 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal61_hz68 {c : ℝ} (hc : B (13 / 20) (131 / 200) c) : B (17535373793698881464893 / 1000000000000000000) (17623900524528077074379 / 1000000000000000000) (((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) := bsub sGlobal61_hz66 (sGlobal61_hz67 hc) (by norm_num) (by norm_num)

theorem sGlobal61_hz69 : B (1524735695971823534271 / 125000000000000000) (609894278388729413841 / 50000000000000000) ((s3am 12225 46)^2) := bsq sGlobal61_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal61_hz70 : B (1524735695971823534271 / 62500000000000000) (609894278388729413841 / 25000000000000000) ((2 : ℝ) * ((s3am 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal61_hz69 (by norm_num) (by norm_num)

theorem sGlobal61_hz71 {c : ℝ} (hc : B (13 / 20) (131 / 200) c) : B (718787436407229611 / 1000000000000000000) (361208105015519999 / 500000000000000000) ((((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) / ((2 : ℝ) * ((s3am 12225 46)^2))) := bdiv (sGlobal61_hz68 hc) sGlobal61_hz70 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal61_hz72 {c : ℝ} (hc : B (13 / 20) (131 / 200) c) : B (718787436407229611 / 1000000000000000000) (361208105015519999 / 500000000000000000) (s3c1 12225 46 c) := by
    convert (sGlobal61_hz71 hc) using 1 <;>
      norm_num [s3c1] <;> ring

theorem sGlobal61_hz73 {c : ℝ} (hc : B (13 / 20) (131 / 200) c) : B (181307780379867391 / 250000000000000000) (145466277727651681 / 200000000000000000) (kdot c) := bkdot (sGlobal61_hz38 hc) sGlobal61_hz39.1 sGlobal61_hz47.2

theorem sGlobal61_hz74 : B (151060510528618469 / 200000000000000000) (755302552643092347 / 1000000000000000000) (kdot ((718787436407229611 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (202244294612069363 / 500000000000000000)) (a := (24023115717769883 / 62500000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (16179543568965549 / 40000000000000000)) (a := (192184925742159063 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal61_hz75 : B (756968495620397543 / 1000000000000000000) (151393699124079509 / 200000000000000000) (kdot ((361208105015519999 / 500000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (401446798215481103 / 1000000000000000000)) (a := (381752994374917369 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (200723399107740551 / 500000000000000000)) (a := (381752994374917367 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal61_hz76 {c : ℝ} (hc : B (13 / 20) (131 / 200) c) : B (151060510528618469 / 200000000000000000) (151393699124079509 / 200000000000000000) (kdot (s3c1 12225 46 c)) := bkdot (sGlobal61_hz72 hc) sGlobal61_hz74.1 sGlobal61_hz75.2

theorem sGlobal61_hz77 {c : ℝ} (hc : B (13 / 20) (131 / 200) c) : B (169 / 400) (17161 / 40000) (c^2) := bsq (sGlobal61_hz38 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal61_hz78 {c : ℝ} (hc : B (13 / 20) (131 / 200) c) : B (22839 / 40000) (231 / 400) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (sGlobal61_hz77 hc) (by norm_num) (by norm_num)

theorem sGlobal61_hz79 {c : ℝ} (hc : B (13 / 20) (131 / 200) c) : B (23613402411289653 / 31250000000000000) (379967103839266591 / 500000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (sGlobal61_hz78 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal61_hz80 : B (39119999999999765769 / 1600000000000000) (3912000000000000489 / 160000000000000) ((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (149450625 : ℝ)) sGlobal61_hz10 (by norm_num) (by norm_num)

theorem sGlobal61_hz81 {c : ℝ} (hc : B (13 / 20) (131 / 200) c) : B (274002789018082271 / 500000000000000000) (552724002544542193 / 1000000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (sGlobal61_hz79 hc) (sGlobal61_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal61_hz82 {c : ℝ} (hc : B (13 / 20) (131 / 200) c) : B (2679747276596828565393 / 200000000000000000) (13514101862214058308113 / 1000000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) := bmul sGlobal61_hz80 (sGlobal61_hz81 hc) (by norm_num) (by norm_num)

theorem sGlobal61_hz83 {c : ℝ} (hc : B (13 / 20) (131 / 200) c) : B (3349684095746035706741 / 500000000000000000) (6757050931107029154057 / 1000000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) / (2 : ℝ)) := bdiv (sGlobal61_hz82 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal61_hz84 {c : ℝ} (hc : B (13 / 20) (131 / 200) c) : B (3349684095746035706741 / 500000000000000000) (6757050931107029154057 / 1000000000000000000) (s3Cpa 12225 c) := by
    convert (sGlobal61_hz83 hc) using 1 <;>
      norm_num [s3Cpa, mA] <;> ring

theorem sGlobal61_hz85 {c : ℝ} (hc : B (13 / 20) (131 / 200) c) : B (60131035471597261 / 250000000000000000) (241894571153323041 / 1000000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (sGlobal61_hz79 hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal61_hz86 {c : ℝ} (hc : B (13 / 20) (131 / 200) c) : B (29462514311728451 / 62500000000000000) (59550257444757407 / 125000000000000000) (c * (kdot c)) := bmul (sGlobal61_hz38 hc) (sGlobal61_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal61_hz87 {c : ℝ} (hc : B (13 / 20) (131 / 200) c) : B (-58969479417917553 / 250000000000000000) (-9180226313373287 / 40000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (sGlobal61_hz85 hc) (sGlobal61_hz86 hc) (by norm_num) (by norm_num)

theorem sGlobal61_hz88 {c : ℝ} (hc : B (13 / 20) (131 / 200) c) : B (-2883607543536168702151 / 500000000000000000) (-1402853333512347020103 / 250000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) := bmul sGlobal61_hz80 (sGlobal61_hz87 hc) (by norm_num) (by norm_num)

theorem sGlobal61_hz89 {c : ℝ} (hc : B (13 / 20) (131 / 200) c) : B (-2883607543536168702151 / 1000000000000000000) (-1402853333512347020103 / 500000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) / (2 : ℝ)) := bdiv (sGlobal61_hz88 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal61_hz90 {c : ℝ} (hc : B (13 / 20) (131 / 200) c) : B (-2883607543536168702151 / 1000000000000000000) (-1402853333512347020103 / 500000000000000000) (s3Cpp 12225 c) := by
    convert (sGlobal61_hz89 hc) using 1 <;>
      norm_num [s3Cpp, mA] <;> ring

theorem sGlobal61_hz91 {c : ℝ} (hc : B (13 / 20) (131 / 200) c) : B (6814513301425809121883 / 1000000000000000000) (6872196041040767566283 / 1000000000000000000) ((s3Cpa 12225 c) + (s3r1 12225 46)) := badd (sGlobal61_hz84 hc) sGlobal61_hz33 (by norm_num) (by norm_num)

theorem sGlobal61_hz92 {c : ℝ} (hc : B (13 / 20) (131 / 200) c) : B (61701051629451124503 / 1000000000000000000) (31111665938581954517 / 500000000000000000) (((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) := bdiv (sGlobal61_hz91 hc) sGlobal61_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal61_hz93 {c : ℝ} (hc : B (13 / 20) (131 / 200) c) : B (12364746930989036983 / 200000000000000000) (62346014902657969457 / 1000000000000000000) ((((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) + (s3e0 12225 46)) := badd (sGlobal61_hz92 hc) sGlobal61_hz16 (by norm_num) (by norm_num)

theorem sGlobal61_hz94 {c : ℝ} (hc : B (13 / 20) (131 / 200) c) : B (12364746930989036983 / 200000000000000000) (62346014902657969457 / 1000000000000000000) (s3Lam 12225 46 c) := by
    convert (sGlobal61_hz93 hc) using 1 <;>
      norm_num [s3Lam] <;> ring

theorem sGlobal61_hz95 {c : ℝ} (hc : B (13 / 20) (131 / 200) c) : B (-2806844136913676896551 / 1000000000000000000) (-682235815100550441347 / 250000000000000000) ((s3Cpp 12225 c) + (s3rpp 12225 46)) := badd (sGlobal61_hz90 hc) sGlobal61_hz37 (by norm_num) (by norm_num)

theorem sGlobal61_hz96 {c : ℝ} (hc : B (13 / 20) (131 / 200) c) : B (-1062346291880239578519 / 500000000000000000) (-682235815100550441347 / 500000000000000000) (if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) := bweaken (bfirst (sGlobal61_hz95 hc) (sGlobal61_hz76 hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem sGlobal61_hz97 {c : ℝ} (hc : B (13 / 20) (131 / 200) c) : B (955543541671267555621 / 250000000000000000) (3887025574242449616747 / 1000000000000000000) ((s3Lam 12225 46 c)^2) := bsq (sGlobal61_hz94 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal61_hz98 {c : ℝ} (hc : B (13 / 20) (131 / 200) c) : B (16145480585527411 / 31250000000000000) (32617823782225731 / 62500000000000000) ((s3c1 12225 46 c)^2) := bsq (sGlobal61_hz72 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal61_hz99 {c : ℝ} (hc : B (13 / 20) (131 / 200) c) : B (29882176217774269 / 62500000000000000) (15104519414472589 / 31250000000000000) ((1 : ℝ) - ((s3c1 12225 46 c)^2)) := bsub (bpoint (1 : ℝ)) (sGlobal61_hz98 hc) (by norm_num) (by norm_num)

theorem sGlobal61_hz100 {c : ℝ} (hc : B (13 / 20) (131 / 200) c) : B (691458472711404631 / 1000000000000000000) (17380747633213359 / 25000000000000000) (√((1 : ℝ) - ((s3c1 12225 46 c)^2))) := bsqrt (sGlobal61_hz99 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal61_hz101 {c : ℝ} (hc : B (13 / 20) (131 / 200) c) : B (2172280858132567309 / 1000000000000000000) (1092064581568025497 / 500000000000000000) (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))) := bmul pi_mem (sGlobal61_hz100 hc) (by norm_num) (by norm_num)

theorem sGlobal61_hz102 {c : ℝ} (hc : B (13 / 20) (131 / 200) c) : B (174997625195254270497 / 100000000000000000) (1789375236489441530979 / 1000000000000000000) (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2))))) := bdiv (sGlobal61_hz97 hc) (sGlobal61_hz101 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal61_hz103 {c : ℝ} (hc : B (13 / 20) (131 / 200) c) : B (-93679082951984113017 / 250000000000000000) (84980721257668129657 / 200000000000000000) ((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) := badd (sGlobal61_hz96 hc) (sGlobal61_hz102 hc) (by norm_num) (by norm_num)

theorem sGlobal61_hz104 : B (3762781186094069 / 250000000000000000) (376278118609407 / 25000000000000000) ((s3e0 12225 46)^2) := bsq sGlobal61_hz16 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal61_hz105 {c : ℝ} (hc : B (13 / 20) (131 / 200) c) : B (-23418830042699504737 / 62500000000000000) (84983731482617004913 / 200000000000000000) (((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) := badd (sGlobal61_hz103 hc) sGlobal61_hz104 (by norm_num) (by norm_num)

theorem sGlobal61_hz106 {c : ℝ} (hc : B (13 / 20) (131 / 200) c) : B (-336204207231944805661 / 1000000000000000000) (463415730867209294581 / 1000000000000000000) ((((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) + (s3rs 12225 46 maskSlack)) := badd (sGlobal61_hz105 hc) sGlobal61_hz29 (by norm_num) (by norm_num)

theorem sGlobal61_hz107 {c : ℝ} (hc : B (13 / 20) (131 / 200) c) : B (-336204207231944805661 / 1000000000000000000) (463415730867209294581 / 1000000000000000000) (s3U 12225 46 maskSlack c) := by
    convert (sGlobal61_hz106 hc) using 1 <;>
      norm_num [s3U] <;> ring

theorem sGlobal61_hz108 {c : ℝ} (hc : B (13 / 20) (131 / 200) c) : B (-2960370950158660976969 / 1000000000000000000) (-1441235036823592922903 / 500000000000000000) ((s3Cpp 12225 c) - (s3rpp 12225 46)) := bsub (sGlobal61_hz90 hc) sGlobal61_hz37 (by norm_num) (by norm_num)

theorem sGlobal61_hz109 {c : ℝ} (hc : B (13 / 20) (131 / 200) c) : B (-2960370950158660976969 / 1000000000000000000) (-1441235036823592922903 / 500000000000000000) (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ)) := bweaken (bmin (sGlobal61_hz108 hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem sGlobal61_hz110 {c : ℝ} (hc : B (13 / 20) (131 / 200) c) : B (-28011344307749106009 / 12500000000000000) (-2177137004543041856009 / 1000000000000000000) ((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) := bmul (sGlobal61_hz76 hc) (sGlobal61_hz109 hc) (by norm_num) (by norm_num)

theorem sGlobal61_hz111 {c : ℝ} (hc : B (13 / 20) (131 / 200) c) : B (-2240922595744672857 / 1000000000000000) (-435430411133557246457 / 200000000000000000) (((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) := bsub (sGlobal61_hz110 hc) sGlobal61_hz104 (by norm_num) (by norm_num)

theorem sGlobal61_hz112 {c : ℝ} (hc : B (13 / 20) (131 / 200) c) : B (-284927458649849640877 / 125000000000000000) (-138478070569939593901 / 62500000000000000) ((((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) - (s3rs 12225 46 maskSlack)) := bsub (sGlobal61_hz111 hc) sGlobal61_hz29 (by norm_num) (by norm_num)

theorem sGlobal61_hz113 {c : ℝ} (hc : B (13 / 20) (131 / 200) c) : B (-284927458649849640877 / 125000000000000000) (-138478070569939593901 / 62500000000000000) (s3L 12225 46 maskSlack c) := by
    convert (sGlobal61_hz112 hc) using 1 <;>
      norm_num [s3L] <;> ring

theorem sGlobal61_hz114 {c : ℝ} (hc : B (13 / 20) (131 / 200) c) : B 0 (463415730867209294581 / 1000000000000000000) |(s3U 12225 46 maskSlack c)| := bweaken (babs (sGlobal61_hz107 hc)) (by norm_num) (by norm_num)

theorem sGlobal61_hz115 {c : ℝ} (hc : B (13 / 20) (131 / 200) c) : B 0 (284927458649849640877 / 125000000000000000) |(s3L 12225 46 maskSlack c)| := bweaken (babs (sGlobal61_hz113 hc)) (by norm_num) (by norm_num)

theorem sGlobal61_hz116 {c : ℝ} (hc : B (13 / 20) (131 / 200) c) : B 0 (284927458649849640877 / 125000000000000000) (max |(s3U 12225 46 maskSlack c)| |(s3L 12225 46 maskSlack c)|) := bweaken (bmax (sGlobal61_hz114 hc) (sGlobal61_hz115 hc)) (by norm_num) (by norm_num)

theorem sGlobal61_hz117 {c : ℝ} (hc : B (13 / 20) (131 / 200) c) : B 0 (284927458649849640877 / 125000000000000000) (s3nks 12225 46 maskSlack c) := by
    convert (sGlobal61_hz116 hc) using 1 <;>
      norm_num [s3nks] <;> ring

theorem sGlobal61 {c : ℝ} (hc : B (13 / 20) (131 / 200) c) :
    0 < s3am 12225 46 ∧ 0 ≤ s3dm 12225 46 c ∧
    s3dm 12225 46 c ^ 2 ≤ 2 * s3ap 12225 46 ^ 2 ∧ s3c1 12225 46 c < 1 ∧
    0 ≤ s3Cpa 12225 c - s3r1 12225 46 ∧
    s3e0 12225 46 ≤ (s3Cpa 12225 c - s3r1 12225 46) / s3ap 12225 46 ∧
    s3nks 12225 46 maskSlack c ≤ 12225 * (23307 / 125000) := by

  refine ⟨lt_of_lt_of_le (by norm_num) sGlobal61_hz14.1,
    le_trans (by norm_num) (sGlobal61_hz64 hc).1, ?_,
    lt_of_le_of_lt (sGlobal61_hz72 hc).2 (by norm_num), ?_, ?_,
    le_trans (sGlobal61_hz117 hc).2 (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (sGlobal61_hz64 hc).1) (sGlobal61_hz64 hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) sGlobal61_hz9.1 2
    nlinarith only [h1, h2]
  · linarith only [(sGlobal61_hz84 hc).1, sGlobal61_hz33.2]
  · have hap : 0 < s3ap 12225 46 := lt_of_lt_of_le (by norm_num) sGlobal61_hz9.1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul sGlobal61_hz16.2 sGlobal61_hz9.2 (le_trans (by norm_num) sGlobal61_hz9.1) (by norm_num)
    linarith only [h, (sGlobal61_hz84 hc).1, sGlobal61_hz33.2]

end BstLean.Part255
