import BstLean.Part255SGlobal34
import BstLean.Part255Numeric10
namespace BstLean.Part255
open Real BstLean.Part130 BstLean.Part182 BstLean.Part197 BstLean.Part246
theorem sGlobal38_hz0 : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal38_hz1 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) ((√(23 : ℝ)) / (12225 : ℝ)) := bdiv sGlobal38_hz0 (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal38_hz2 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) maskSlack := by
    convert sGlobal38_hz1 using 1 <;>
      norm_num [maskSlack] <;> ring

theorem sGlobal38_hz3 : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal38_hz4 : B (6395294793910793 / 500000000000000000) (12790589587821587 / 1000000000000000000) (√((2 / 12225) : ℝ)) := bsqrt (bpoint ((2 / 12225) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal38_hz5 : B (7230130686979 / 62500000000000000) (23136418198333 / 200000000000000000) (√((2 / 149450625) : ℝ)) := bsqrt (bpoint ((2 / 149450625) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal38_hz6 : B (2211334438749598093 / 20000000000000000) (110566721937479904651 / 1000000000000000000) (√(12225 : ℝ)) := bsqrt (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal38_hz7 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))) := bmul sGlobal38_hz3 sGlobal38_hz4 (by norm_num) (by norm_num)

theorem sGlobal38_hz8 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) ((√(12225 : ℝ)) + ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := badd sGlobal38_hz6 sGlobal38_hz7 (by norm_num) (by norm_num)

theorem sGlobal38_hz9 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) (s3ap 12225 46) := by
    convert sGlobal38_hz8 using 1 <;>
      norm_num [s3ap, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal38_hz10 : B (163599182004089 / 1000000000000000000) (16359918200409 / 100000000000000000) ((2 : ℝ) / (12225 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal38_hz11 : B (1222499983640081799591 / 100000000000000000) (12224999836400817995911 / 1000000000000000000) ((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ))) := bsub (bpoint (12225 : ℝ)) sGlobal38_hz10 (by norm_num) (by norm_num)

theorem sGlobal38_hz12 : B (110566721197658827907 / 1000000000000000000) (27641680299414706977 / 250000000000000000) (√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) := bsqrt sGlobal38_hz11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal38_hz13 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) ((√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) - ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bsub sGlobal38_hz12 sGlobal38_hz7 (by norm_num) (by norm_num)

theorem sGlobal38_hz14 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) (s3am 12225 46) := by
    convert sGlobal38_hz13 using 1 <;>
      norm_num [s3am, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal38_hz15 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√((2 / 12225) : ℝ)) * (√(92 : ℝ))) := bmul sGlobal38_hz4 sGlobal38_hz3 (by norm_num) (by norm_num)

theorem sGlobal38_hz16 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) (s3e0 12225 46) := by
    convert sGlobal38_hz15 using 1 <;>
      norm_num [s3e0, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal38_hz17 : B (250196148528560847 / 500000000000000000) (100078459411424339 / 200000000000000000) (((1 / 2) : ℝ) + maskSlack) := badd (bpoint ((1 / 2) : ℝ)) sGlobal38_hz2 (by norm_num) (by norm_num)

theorem sGlobal38_hz18 : B (59827153232297998295487 / 800000000000000) (23930861292919199366019 / 320000000000000) ((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack)) := bmul (bpoint (149450625 : ℝ)) sGlobal38_hz17 (by norm_num) (by norm_num)

theorem sGlobal38_hz19 : B (1729554180017180009583 / 200000000000000000) (8647770900085900056557 / 1000000000000000000) (√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) := bsqrt sGlobal38_hz18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal38_hz20 : B (4328681281566262743499 / 500000000000000000) (8657362563132525495641 / 1000000000000000000) ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))) := badd sGlobal38_hz19 sGlobal38_hz3 (by norm_num) (by norm_num)

theorem sGlobal38_hz21 : B (110732771457999278473 / 1000000000000000000) (55366385728999643621 / 500000000000000000) ((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ)))) := bmul sGlobal38_hz4 sGlobal38_hz20 (by norm_num) (by norm_num)

theorem sGlobal38_hz22 : B (209099159 / 15625000000000000) (13382346177 / 1000000000000000000) ((2 : ℝ) / (149450625 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (149450625 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal38_hz23 : B (2452349334953899930479 / 200000000000000000) (12261746674769501594427 / 1000000000000000000) (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2) := bsq sGlobal38_hz21 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal38_hz24 : B (82045469362091 / 500000000000000000) (32818187747289 / 200000000000000000) (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2)) := bmul sGlobal38_hz22 sGlobal38_hz23 (by norm_num) (by norm_num)

theorem sGlobal38_hz25 : B (82045469362091 / 250000000000000000) (32818187747289 / 100000000000000000) ((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) := bmul (bpoint (2 : ℝ)) sGlobal38_hz24 (by norm_num) (by norm_num)

theorem sGlobal38_hz26 : B (117258080744995992792057 / 1000000000000000000) (58629040372497996396029 / 500000000000000000) (√(13749457500 : ℝ)) := bsqrt (bpoint (13749457500 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal38_hz27 : B (117304080744995992792057 / 1000000000000000000) (58652040372497996396029 / 500000000000000000) ((√(13749457500 : ℝ)) + (46 : ℝ)) := badd sGlobal38_hz26 (bpoint (46 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal38_hz28 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal38_hz25 sGlobal38_hz27 (by norm_num) (by norm_num)

theorem sGlobal38_hz29 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (s3rs 12225 46 maskSlack) := by
    convert sGlobal38_hz28 using 1 <;>
      norm_num [s3rs, s3pp, s3K, mA, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal38_hz30 : B (490797546012267 / 1000000000000000000) (49079754601227 / 100000000000000000) ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (3 : ℝ)) sGlobal38_hz10 (by norm_num) (by norm_num)

theorem sGlobal38_hz31 : B (490797546012267 / 500000000000000000) (49079754601227 / 50000000000000000) ((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal38_hz30 (by norm_num) (by norm_num)

theorem sGlobal38_hz32 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal38_hz31 sGlobal38_hz27 (by norm_num) (by norm_num)

theorem sGlobal38_hz33 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (s3r1 12225 46) := by
    convert sGlobal38_hz32 using 1 <;>
      norm_num [s3r1, mA] <;> ring

theorem sGlobal38_hz34 : B (163599182004089 / 500000000000000000) (16359918200409 / 50000000000000000) ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (2 : ℝ)) sGlobal38_hz10 (by norm_num) (by norm_num)

theorem sGlobal38_hz35 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal38_hz34 (by norm_num) (by norm_num)

theorem sGlobal38_hz36 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal38_hz35 sGlobal38_hz27 (by norm_num) (by norm_num)

theorem sGlobal38_hz37 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (s3rpp 12225 46) := by
    convert sGlobal38_hz36 using 1 <;>
      norm_num [s3rpp, mA] <;> ring

theorem sGlobal38_hz38 {c : ℝ} (hc : B (107 / 200) (27 / 50) c) : B (107 / 200) (27 / 50) c := hc

theorem sGlobal38_hz39 : B (679688396740185101 / 1000000000000000000) (169922099185047551 / 250000000000000000) (kdot ((107 / 200))) := by
    constructor
    · apply bkdot_lower (q := (275196110115679693 / 500000000000000000)) (a := (125786072457575369 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (110078444046271877 / 200000000000000000)) (a := (251572144915146731 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal38_hz40 : B (11449 / 40000) (11449 / 40000) (((107 / 200) : ℝ)^2) := bsq (bpoint ((107 / 200) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal38_hz41 : B (28551 / 40000) (28551 / 40000) ((1 : ℝ) - (((107 / 200) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal38_hz40 (by norm_num) (by norm_num)

theorem sGlobal38_hz42 : B (52803253628446041 / 62500000000000000) (844852058055136657 / 1000000000000000000) (√((1 : ℝ) - (((107 / 200) : ℝ)^2))) := bsqrt sGlobal38_hz41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal38_hz43 : B (268924762441671857 / 1000000000000000000) (268924762441671859 / 1000000000000000000) ((√((1 : ℝ) - (((107 / 200) : ℝ)^2))) / Real.pi) := bdiv sGlobal38_hz42 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal38_hz44 : B (363633292255999029 / 1000000000000000000) (2272708076600011 / 6250000000000000) (((107 / 200) : ℝ) * (kdot ((107 / 200)))) := bmul (bpoint ((107 / 200) : ℝ)) sGlobal38_hz39 (by norm_num) (by norm_num)

theorem sGlobal38_hz45 : B (316279027348835443 / 500000000000000000) (632558054697673619 / 1000000000000000000) (((√((1 : ℝ) - (((107 / 200) : ℝ)^2))) / Real.pi) + (((107 / 200) : ℝ) * (kdot ((107 / 200))))) := badd sGlobal38_hz43 sGlobal38_hz44 (by norm_num) (by norm_num)

theorem sGlobal38_hz46 : B (316279027348835443 / 500000000000000000) (632558054697673619 / 1000000000000000000) (kappa ((107 / 200))) := by rw [kappa_eq]; exact sGlobal38_hz45

theorem sGlobal38_hz47 : B (340787885684049643 / 500000000000000000) (340787885684051451 / 500000000000000000) (kdot ((27 / 50))) := by
    constructor
    · apply bkdot_lower (q := (68316965625002639 / 125000000000000000)) (a := (50017960869748799 / 100000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (546535725000021111 / 1000000000000000000)) (a := (500179608697482311 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal38_hz48 : B (729 / 2500) (729 / 2500) (((27 / 50) : ℝ)^2) := bsq (bpoint ((27 / 50) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal38_hz49 : B (1771 / 2500) (1771 / 2500) ((1 : ℝ) - (((27 / 50) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal38_hz48 (by norm_num) (by norm_num)

theorem sGlobal38_hz50 : B (841665016500032511 / 1000000000000000000) (821938492675813 / 976562500000000) (√((1 : ℝ) - (((27 / 50) : ℝ)^2))) := bsqrt sGlobal38_hz49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal38_hz51 : B (133955147803501823 / 500000000000000000) (267910295607003647 / 1000000000000000000) ((√((1 : ℝ) - (((27 / 50) : ℝ)^2))) / Real.pi) := bdiv sGlobal38_hz50 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal38_hz52 : B (184025458269386807 / 500000000000000000) (23003182283673473 / 62500000000000000) (((27 / 50) : ℝ) * (kdot ((27 / 50)))) := bmul (bpoint ((27 / 50) : ℝ)) sGlobal38_hz47 (by norm_num) (by norm_num)

theorem sGlobal38_hz53 : B (31798060607288863 / 50000000000000000) (127192242429155843 / 200000000000000000) (((√((1 : ℝ) - (((27 / 50) : ℝ)^2))) / Real.pi) + (((27 / 50) : ℝ) * (kdot ((27 / 50))))) := badd sGlobal38_hz51 sGlobal38_hz52 (by norm_num) (by norm_num)

theorem sGlobal38_hz54 : B (31798060607288863 / 50000000000000000) (127192242429155843 / 200000000000000000) (kappa ((27 / 50))) := by rw [kappa_eq]; exact sGlobal38_hz53

theorem sGlobal38_hz55 {c : ℝ} (hc : B (107 / 200) (27 / 50) c) : B (316279027348835443 / 500000000000000000) (127192242429155843 / 200000000000000000) (kappa c) := bkappa (sGlobal38_hz38 hc) (by norm_num) (by norm_num) sGlobal38_hz46.1 sGlobal38_hz54.2

theorem sGlobal38_hz56 : B 24450 24450 ((2 : ℝ) * (12225 : ℝ)) := bmul (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal38_hz57 {c : ℝ} (hc : B (107 / 200) (27 / 50) c) : B (72807757570844157 / 200000000000000000) (183720972651164557 / 500000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (sGlobal38_hz55 hc) (by norm_num) (by norm_num)

theorem sGlobal38_hz58 {c : ℝ} (hc : B (107 / 200) (27 / 50) c) : B (35602993452142792773 / 4000000000000000) (89839555626419468373 / 10000000000000000) (((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) := bmul sGlobal38_hz56 (sGlobal38_hz57 hc) (by norm_num) (by norm_num)

theorem sGlobal38_hz59 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (4 : ℝ)) sGlobal38_hz10 (by norm_num) (by norm_num)

theorem sGlobal38_hz60 {c : ℝ} (hc : B (107 / 200) (27 / 50) c) : B (890074770863897017689 / 100000000000000000) (561497181765326176309 / 62500000000000000) ((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bsub (sGlobal38_hz58 hc) sGlobal38_hz59 (by norm_num) (by norm_num)

theorem sGlobal38_hz61 {c : ℝ} (hc : B (107 / 200) (27 / 50) c) : B (9434377408519848999 / 100000000000000000) (94783727022338696497 / 1000000000000000000) (√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) := bsqrt (sGlobal38_hz60 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal38_hz62 : B (30670756373515103 / 125000000000000000) (122683025494060423 / 500000000000000000) ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal38_hz7 (by norm_num) (by norm_num)

theorem sGlobal38_hz63 {c : ℝ} (hc : B (107 / 200) (27 / 50) c) : B (11762301004276296143 / 125000000000000000) (94538360971350575673 / 1000000000000000000) ((√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) - ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))))) := bsub (sGlobal38_hz61 hc) sGlobal38_hz62 (by norm_num) (by norm_num)

theorem sGlobal38_hz64 {c : ℝ} (hc : B (107 / 200) (27 / 50) c) : B (11762301004276296143 / 125000000000000000) (94538360971350575673 / 1000000000000000000) (s3dm 12225 46 c) := by
    convert (sGlobal38_hz63 hc) using 1 <;>
      norm_num [s3dm, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal38_hz65 : B (6126072185528622723889 / 500000000000000000) (2450428874211449090087 / 200000000000000000) ((s3ap 12225 46)^2) := bsq sGlobal38_hz9 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal38_hz66 : B (6126072185528622723889 / 250000000000000000) (2450428874211449090087 / 100000000000000000) ((2 : ℝ) * ((s3ap 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal38_hz65 (by norm_num) (by norm_num)

theorem sGlobal38_hz67 {c : ℝ} (hc : B (107 / 200) (27 / 50) c) : B (1770902078914549309651 / 200000000000000000) (1787500339029876352377 / 200000000000000000) ((s3dm 12225 46 c)^2) := bsq (sGlobal38_hz64 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal38_hz68 {c : ℝ} (hc : B (107 / 200) (27 / 50) c) : B (15566787046965109133671 / 1000000000000000000) (3129955669508348870523 / 200000000000000000) (((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) := bsub sGlobal38_hz66 (sGlobal38_hz67 hc) (by norm_num) (by norm_num)

theorem sGlobal38_hz69 : B (1524735695971823534271 / 125000000000000000) (609894278388729413841 / 50000000000000000) ((s3am 12225 46)^2) := bsq sGlobal38_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal38_hz70 : B (1524735695971823534271 / 62500000000000000) (609894278388729413841 / 25000000000000000) ((2 : ℝ) * ((s3am 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal38_hz69 (by norm_num) (by norm_num)

theorem sGlobal38_hz71 {c : ℝ} (hc : B (107 / 200) (27 / 50) c) : B (1595234165838829 / 2500000000000000) (320747769369280281 / 500000000000000000) ((((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) / ((2 : ℝ) * ((s3am 12225 46)^2))) := bdiv (sGlobal38_hz68 hc) sGlobal38_hz70 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal38_hz72 {c : ℝ} (hc : B (107 / 200) (27 / 50) c) : B (1595234165838829 / 2500000000000000) (320747769369280281 / 500000000000000000) (s3c1 12225 46 c) := by
    convert (sGlobal38_hz71 hc) using 1 <;>
      norm_num [s3c1] <;> ring

theorem sGlobal38_hz73 {c : ℝ} (hc : B (107 / 200) (27 / 50) c) : B (679688396740185101 / 1000000000000000000) (340787885684051451 / 500000000000000000) (kdot c) := bkdot (sGlobal38_hz38 hc) sGlobal38_hz39.1 sGlobal38_hz47.2

theorem sGlobal38_hz74 : B (5627162128170409 / 7812500000000000) (180069188101453089 / 250000000000000000) (kdot ((1595234165838829 / 2500000000000000))) := by
    constructor
    · apply bkdot_lower (q := (235016703686823987 / 500000000000000000)) (a := (5492353123001117 / 12500000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (470033407373647973 / 1000000000000000000)) (a := (219694124920044677 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal38_hz75 : B (9021071435119927 / 12500000000000000) (180421428702398541 / 250000000000000000) (kdot ((320747769369280281 / 500000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (233667027118246641 / 500000000000000000)) (a := (437175056871636787 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (467334054236493281 / 1000000000000000000)) (a := (437175056871636783 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal38_hz76 {c : ℝ} (hc : B (107 / 200) (27 / 50) c) : B (5627162128170409 / 7812500000000000) (180421428702398541 / 250000000000000000) (kdot (s3c1 12225 46 c)) := bkdot (sGlobal38_hz72 hc) sGlobal38_hz74.1 sGlobal38_hz75.2

theorem sGlobal38_hz77 {c : ℝ} (hc : B (107 / 200) (27 / 50) c) : B (11449 / 40000) (729 / 2500) (c^2) := bsq (sGlobal38_hz38 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal38_hz78 {c : ℝ} (hc : B (107 / 200) (27 / 50) c) : B (1771 / 2500) (28551 / 40000) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (sGlobal38_hz77 hc) (by norm_num) (by norm_num)

theorem sGlobal38_hz79 {c : ℝ} (hc : B (107 / 200) (27 / 50) c) : B (841665016500032511 / 1000000000000000000) (844852058055136657 / 1000000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (sGlobal38_hz78 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal38_hz80 : B (39119999999999765769 / 1600000000000000) (3912000000000000489 / 160000000000000) ((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (149450625 : ℝ)) sGlobal38_hz10 (by norm_num) (by norm_num)

theorem sGlobal38_hz81 {c : ℝ} (hc : B (107 / 200) (27 / 50) c) : B (71508743207151067 / 125000000000000000) (287915346580429511 / 500000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (sGlobal38_hz79 hc) (sGlobal38_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal38_hz82 {c : ℝ} (hc : B (107 / 200) (27 / 50) c) : B (13987110171318664957377 / 1000000000000000000) (14079060447783004847783 / 1000000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) := bmul sGlobal38_hz80 (sGlobal38_hz81 hc) (by norm_num) (by norm_num)

theorem sGlobal38_hz83 {c : ℝ} (hc : B (107 / 200) (27 / 50) c) : B (218548596426854139959 / 31250000000000000) (1759882555972875605973 / 250000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) / (2 : ℝ)) := bdiv (sGlobal38_hz82 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal38_hz84 {c : ℝ} (hc : B (107 / 200) (27 / 50) c) : B (218548596426854139959 / 31250000000000000) (1759882555972875605973 / 250000000000000000) (s3Cpa 12225 c) := by
    convert (sGlobal38_hz83 hc) using 1 <;>
      norm_num [s3Cpa, mA] <;> ring

theorem sGlobal38_hz85 {c : ℝ} (hc : B (107 / 200) (27 / 50) c) : B (133955147803501823 / 500000000000000000) (268924762441671859 / 1000000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (sGlobal38_hz79 hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal38_hz86 {c : ℝ} (hc : B (107 / 200) (27 / 50) c) : B (363633292255999029 / 1000000000000000000) (23003182283673473 / 62500000000000000) (c * (kdot c)) := bmul (sGlobal38_hz38 hc) (sGlobal38_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal38_hz87 {c : ℝ} (hc : B (107 / 200) (27 / 50) c) : B (-50070310465885961 / 500000000000000000) (-9470852981432717 / 100000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (sGlobal38_hz85 hc) (sGlobal38_hz86 hc) (by norm_num) (by norm_num)

theorem sGlobal38_hz88 {c : ℝ} (hc : B (107 / 200) (27 / 50) c) : B (-489687636356364759791 / 200000000000000000) (-2315623553960285441703 / 1000000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) := bmul sGlobal38_hz80 (sGlobal38_hz87 hc) (by norm_num) (by norm_num)

theorem sGlobal38_hz89 {c : ℝ} (hc : B (107 / 200) (27 / 50) c) : B (-612109545445455949739 / 500000000000000000) (-1157811776980142720851 / 1000000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) / (2 : ℝ)) := bdiv (sGlobal38_hz88 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal38_hz90 {c : ℝ} (hc : B (107 / 200) (27 / 50) c) : B (-612109545445455949739 / 500000000000000000) (-1157811776980142720851 / 1000000000000000000) (s3Cpp 12225 c) := by
    convert (sGlobal38_hz89 hc) using 1 <;>
      norm_num [s3Cpp, mA] <;> ring

theorem sGlobal38_hz91 {c : ℝ} (hc : B (107 / 200) (27 / 50) c) : B (7108700195593070187089 / 1000000000000000000) (3577337666912620418059 / 500000000000000000) ((s3Cpa 12225 c) + (s3r1 12225 46)) := badd (sGlobal38_hz84 hc) sGlobal38_hz33 (by norm_num) (by norm_num)

theorem sGlobal38_hz92 {c : ℝ} (hc : B (107 / 200) (27 / 50) c) : B (12872945091905698329 / 200000000000000000) (64781000878220650377 / 1000000000000000000) (((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) := bdiv (sGlobal38_hz91 hc) sGlobal38_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal38_hz93 {c : ℝ} (hc : B (107 / 200) (27 / 50) c) : B (64487408485022552057 / 1000000000000000000) (162259209759286777 / 2500000000000000) ((((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) + (s3e0 12225 46)) := badd (sGlobal38_hz92 hc) sGlobal38_hz16 (by norm_num) (by norm_num)

theorem sGlobal38_hz94 {c : ℝ} (hc : B (107 / 200) (27 / 50) c) : B (64487408485022552057 / 1000000000000000000) (162259209759286777 / 2500000000000000) (s3Lam 12225 46 c) := by
    convert (sGlobal38_hz93 hc) using 1 <;>
      norm_num [s3Lam] <;> ring

theorem sGlobal38_hz95 {c : ℝ} (hc : B (107 / 200) (27 / 50) c) : B (-573727842134210046939 / 500000000000000000) (-1081048370357650446033 / 1000000000000000000) ((s3Cpp 12225 c) + (s3rpp 12225 46)) := badd (sGlobal38_hz90 hc) sGlobal38_hz37 (by norm_num) (by norm_num)

theorem sGlobal38_hz96 {c : ℝ} (hc : B (107 / 200) (27 / 50) c) : B (-165620475142717349707 / 200000000000000000) (-67565523147353152877 / 125000000000000000) (if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) := bweaken (bfirst (sGlobal38_hz95 hc) (sGlobal38_hz76 hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem sGlobal38_hz97 {c : ℝ} (hc : B (107 / 200) (27 / 50) c) : B (519828231639269830331 / 125000000000000000) (4212488184273316041101 / 1000000000000000000) ((s3Lam 12225 46 c)^2) := bsq (sGlobal38_hz94 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal38_hz98 {c : ℝ} (hc : B (107 / 200) (27 / 50) c) : B (407163527017520733 / 1000000000000000000) (82303305244295211 / 200000000000000000) ((s3c1 12225 46 c)^2) := bsq (sGlobal38_hz72 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal38_hz99 {c : ℝ} (hc : B (107 / 200) (27 / 50) c) : B (117696694755704789 / 200000000000000000) (592836472982479267 / 1000000000000000000) ((1 : ℝ) - ((s3c1 12225 46 c)^2)) := bsub (bpoint (1 : ℝ)) (sGlobal38_hz98 hc) (by norm_num) (by norm_num)

theorem sGlobal38_hz100 {c : ℝ} (hc : B (107 / 200) (27 / 50) c) : B (38356338256490411 / 50000000000000000) (769958747584881503 / 1000000000000000000) (√((1 : ℝ) - ((s3c1 12225 46 c)^2))) := bsqrt (sGlobal38_hz99 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal38_hz101 {c : ℝ} (hc : B (107 / 200) (27 / 50) c) : B (1204999904851954137 / 500000000000000000) (2418896744979861687 / 1000000000000000000) (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))) := bmul pi_mem (sGlobal38_hz100 hc) (by norm_num) (by norm_num)

theorem sGlobal38_hz102 {c : ℝ} (hc : B (107 / 200) (27 / 50) c) : B (1719224213164494095827 / 1000000000000000000) (873960273214888936569 / 500000000000000000) (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2))))) := bdiv (sGlobal38_hz97 hc) (sGlobal38_hz101 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal38_hz103 {c : ℝ} (hc : B (107 / 200) (27 / 50) c) : B (222780459362726836823 / 250000000000000000) (603698180625476325061 / 500000000000000000) ((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) := badd (sGlobal38_hz96 hc) (sGlobal38_hz102 hc) (by norm_num) (by norm_num)

theorem sGlobal38_hz104 : B (3762781186094069 / 250000000000000000) (376278118609407 / 25000000000000000) ((s3e0 12225 46)^2) := bsq sGlobal38_hz16 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal38_hz105 {c : ℝ} (hc : B (107 / 200) (27 / 50) c) : B (55696055535978232723 / 62500000000000000) (603705706187848513201 / 500000000000000000) (((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) := badd (sGlobal38_hz103 hc) sGlobal38_hz104 (by norm_num) (by norm_num)

theorem sGlobal38_hz106 {c : ℝ} (hc : B (107 / 200) (27 / 50) c) : B (929633962026898993699 / 1000000000000000000) (622954242914910648209 / 500000000000000000) ((((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) + (s3rs 12225 46 maskSlack)) := badd (sGlobal38_hz105 hc) sGlobal38_hz29 (by norm_num) (by norm_num)

theorem sGlobal38_hz107 {c : ℝ} (hc : B (107 / 200) (27 / 50) c) : B (929633962026898993699 / 1000000000000000000) (622954242914910648209 / 500000000000000000) (s3U 12225 46 maskSlack c) := by
    convert (sGlobal38_hz106 hc) using 1 <;>
      norm_num [s3U] <;> ring

theorem sGlobal38_hz108 {c : ℝ} (hc : B (107 / 200) (27 / 50) c) : B (-162622812189175521787 / 125000000000000000) (-1234575183602634526451 / 1000000000000000000) ((s3Cpp 12225 c) - (s3rpp 12225 46)) := bsub (sGlobal38_hz90 hc) sGlobal38_hz37 (by norm_num) (by norm_num)

theorem sGlobal38_hz109 {c : ℝ} (hc : B (107 / 200) (27 / 50) c) : B (-162622812189175521787 / 125000000000000000) (-1234575183602634526451 / 1000000000000000000) (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ)) := bweaken (bmin (sGlobal38_hz108 hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem sGlobal38_hz110 {c : ℝ} (hc : B (107 / 200) (27 / 50) c) : B (-938900483672732153551 / 1000000000000000000) (-889235803846115114333 / 1000000000000000000) ((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) := bmul (sGlobal38_hz76 hc) (sGlobal38_hz109 hc) (by norm_num) (by norm_num)

theorem sGlobal38_hz111 {c : ℝ} (hc : B (107 / 200) (27 / 50) c) : B (-938915534797476529831 / 1000000000000000000) (-889250854970859490609 / 1000000000000000000) (((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) := bsub (sGlobal38_hz110 hc) sGlobal38_hz104 (by norm_num) (by norm_num)

theorem sGlobal38_hz112 {c : ℝ} (hc : B (107 / 200) (27 / 50) c) : B (-977412608251600799847 / 1000000000000000000) (-46387396421105338037 / 50000000000000000) ((((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) - (s3rs 12225 46 maskSlack)) := bsub (sGlobal38_hz111 hc) sGlobal38_hz29 (by norm_num) (by norm_num)

theorem sGlobal38_hz113 {c : ℝ} (hc : B (107 / 200) (27 / 50) c) : B (-977412608251600799847 / 1000000000000000000) (-46387396421105338037 / 50000000000000000) (s3L 12225 46 maskSlack c) := by
    convert (sGlobal38_hz112 hc) using 1 <;>
      norm_num [s3L] <;> ring

theorem sGlobal38_hz114 {c : ℝ} (hc : B (107 / 200) (27 / 50) c) : B 0 (622954242914910648209 / 500000000000000000) |(s3U 12225 46 maskSlack c)| := bweaken (babs (sGlobal38_hz107 hc)) (by norm_num) (by norm_num)

theorem sGlobal38_hz115 {c : ℝ} (hc : B (107 / 200) (27 / 50) c) : B 0 (977412608251600799847 / 1000000000000000000) |(s3L 12225 46 maskSlack c)| := bweaken (babs (sGlobal38_hz113 hc)) (by norm_num) (by norm_num)

theorem sGlobal38_hz116 {c : ℝ} (hc : B (107 / 200) (27 / 50) c) : B 0 (622954242914910648209 / 500000000000000000) (max |(s3U 12225 46 maskSlack c)| |(s3L 12225 46 maskSlack c)|) := bweaken (bmax (sGlobal38_hz114 hc) (sGlobal38_hz115 hc)) (by norm_num) (by norm_num)

theorem sGlobal38_hz117 {c : ℝ} (hc : B (107 / 200) (27 / 50) c) : B 0 (622954242914910648209 / 500000000000000000) (s3nks 12225 46 maskSlack c) := by
    convert (sGlobal38_hz116 hc) using 1 <;>
      norm_num [s3nks] <;> ring

theorem sGlobal38 {c : ℝ} (hc : B (107 / 200) (27 / 50) c) :
    0 < s3am 12225 46 ∧ 0 ≤ s3dm 12225 46 c ∧
    s3dm 12225 46 c ^ 2 ≤ 2 * s3ap 12225 46 ^ 2 ∧ s3c1 12225 46 c < 1 ∧
    0 ≤ s3Cpa 12225 c - s3r1 12225 46 ∧
    s3e0 12225 46 ≤ (s3Cpa 12225 c - s3r1 12225 46) / s3ap 12225 46 ∧
    s3nks 12225 46 maskSlack c ≤ 12225 * (20383 / 200000) := by

  refine ⟨lt_of_lt_of_le (by norm_num) sGlobal38_hz14.1,
    le_trans (by norm_num) (sGlobal38_hz64 hc).1, ?_,
    lt_of_le_of_lt (sGlobal38_hz72 hc).2 (by norm_num), ?_, ?_,
    le_trans (sGlobal38_hz117 hc).2 (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (sGlobal38_hz64 hc).1) (sGlobal38_hz64 hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) sGlobal38_hz9.1 2
    nlinarith only [h1, h2]
  · linarith only [(sGlobal38_hz84 hc).1, sGlobal38_hz33.2]
  · have hap : 0 < s3ap 12225 46 := lt_of_lt_of_le (by norm_num) sGlobal38_hz9.1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul sGlobal38_hz16.2 sGlobal38_hz9.2 (le_trans (by norm_num) sGlobal38_hz9.1) (by norm_num)
    linarith only [h, (sGlobal38_hz84 hc).1, sGlobal38_hz33.2]

end BstLean.Part255
