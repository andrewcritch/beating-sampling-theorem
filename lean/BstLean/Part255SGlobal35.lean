import BstLean.Part255SGlobal31
import BstLean.Part255Numeric10
namespace BstLean.Part255
open Real BstLean.Part130 BstLean.Part182 BstLean.Part197 BstLean.Part246
theorem sGlobal35_hz0 : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal35_hz1 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) ((√(23 : ℝ)) / (12225 : ℝ)) := bdiv sGlobal35_hz0 (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal35_hz2 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) maskSlack := by
    convert sGlobal35_hz1 using 1 <;>
      norm_num [maskSlack] <;> ring

theorem sGlobal35_hz3 : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal35_hz4 : B (6395294793910793 / 500000000000000000) (12790589587821587 / 1000000000000000000) (√((2 / 12225) : ℝ)) := bsqrt (bpoint ((2 / 12225) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal35_hz5 : B (7230130686979 / 62500000000000000) (23136418198333 / 200000000000000000) (√((2 / 149450625) : ℝ)) := bsqrt (bpoint ((2 / 149450625) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal35_hz6 : B (2211334438749598093 / 20000000000000000) (110566721937479904651 / 1000000000000000000) (√(12225 : ℝ)) := bsqrt (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal35_hz7 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))) := bmul sGlobal35_hz3 sGlobal35_hz4 (by norm_num) (by norm_num)

theorem sGlobal35_hz8 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) ((√(12225 : ℝ)) + ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := badd sGlobal35_hz6 sGlobal35_hz7 (by norm_num) (by norm_num)

theorem sGlobal35_hz9 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) (s3ap 12225 46) := by
    convert sGlobal35_hz8 using 1 <;>
      norm_num [s3ap, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal35_hz10 : B (163599182004089 / 1000000000000000000) (16359918200409 / 100000000000000000) ((2 : ℝ) / (12225 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal35_hz11 : B (1222499983640081799591 / 100000000000000000) (12224999836400817995911 / 1000000000000000000) ((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ))) := bsub (bpoint (12225 : ℝ)) sGlobal35_hz10 (by norm_num) (by norm_num)

theorem sGlobal35_hz12 : B (110566721197658827907 / 1000000000000000000) (27641680299414706977 / 250000000000000000) (√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) := bsqrt sGlobal35_hz11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal35_hz13 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) ((√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) - ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bsub sGlobal35_hz12 sGlobal35_hz7 (by norm_num) (by norm_num)

theorem sGlobal35_hz14 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) (s3am 12225 46) := by
    convert sGlobal35_hz13 using 1 <;>
      norm_num [s3am, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal35_hz15 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√((2 / 12225) : ℝ)) * (√(92 : ℝ))) := bmul sGlobal35_hz4 sGlobal35_hz3 (by norm_num) (by norm_num)

theorem sGlobal35_hz16 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) (s3e0 12225 46) := by
    convert sGlobal35_hz15 using 1 <;>
      norm_num [s3e0, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal35_hz17 : B (250196148528560847 / 500000000000000000) (100078459411424339 / 200000000000000000) (((1 / 2) : ℝ) + maskSlack) := badd (bpoint ((1 / 2) : ℝ)) sGlobal35_hz2 (by norm_num) (by norm_num)

theorem sGlobal35_hz18 : B (59827153232297998295487 / 800000000000000) (23930861292919199366019 / 320000000000000) ((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack)) := bmul (bpoint (149450625 : ℝ)) sGlobal35_hz17 (by norm_num) (by norm_num)

theorem sGlobal35_hz19 : B (1729554180017180009583 / 200000000000000000) (8647770900085900056557 / 1000000000000000000) (√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) := bsqrt sGlobal35_hz18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal35_hz20 : B (4328681281566262743499 / 500000000000000000) (8657362563132525495641 / 1000000000000000000) ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))) := badd sGlobal35_hz19 sGlobal35_hz3 (by norm_num) (by norm_num)

theorem sGlobal35_hz21 : B (110732771457999278473 / 1000000000000000000) (55366385728999643621 / 500000000000000000) ((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ)))) := bmul sGlobal35_hz4 sGlobal35_hz20 (by norm_num) (by norm_num)

theorem sGlobal35_hz22 : B (209099159 / 15625000000000000) (13382346177 / 1000000000000000000) ((2 : ℝ) / (149450625 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (149450625 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal35_hz23 : B (2452349334953899930479 / 200000000000000000) (12261746674769501594427 / 1000000000000000000) (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2) := bsq sGlobal35_hz21 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal35_hz24 : B (82045469362091 / 500000000000000000) (32818187747289 / 200000000000000000) (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2)) := bmul sGlobal35_hz22 sGlobal35_hz23 (by norm_num) (by norm_num)

theorem sGlobal35_hz25 : B (82045469362091 / 250000000000000000) (32818187747289 / 100000000000000000) ((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) := bmul (bpoint (2 : ℝ)) sGlobal35_hz24 (by norm_num) (by norm_num)

theorem sGlobal35_hz26 : B (117258080744995992792057 / 1000000000000000000) (58629040372497996396029 / 500000000000000000) (√(13749457500 : ℝ)) := bsqrt (bpoint (13749457500 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal35_hz27 : B (117304080744995992792057 / 1000000000000000000) (58652040372497996396029 / 500000000000000000) ((√(13749457500 : ℝ)) + (46 : ℝ)) := badd sGlobal35_hz26 (bpoint (46 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal35_hz28 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal35_hz25 sGlobal35_hz27 (by norm_num) (by norm_num)

theorem sGlobal35_hz29 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (s3rs 12225 46 maskSlack) := by
    convert sGlobal35_hz28 using 1 <;>
      norm_num [s3rs, s3pp, s3K, mA, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal35_hz30 : B (490797546012267 / 1000000000000000000) (49079754601227 / 100000000000000000) ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (3 : ℝ)) sGlobal35_hz10 (by norm_num) (by norm_num)

theorem sGlobal35_hz31 : B (490797546012267 / 500000000000000000) (49079754601227 / 50000000000000000) ((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal35_hz30 (by norm_num) (by norm_num)

theorem sGlobal35_hz32 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal35_hz31 sGlobal35_hz27 (by norm_num) (by norm_num)

theorem sGlobal35_hz33 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (s3r1 12225 46) := by
    convert sGlobal35_hz32 using 1 <;>
      norm_num [s3r1, mA] <;> ring

theorem sGlobal35_hz34 : B (163599182004089 / 500000000000000000) (16359918200409 / 50000000000000000) ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (2 : ℝ)) sGlobal35_hz10 (by norm_num) (by norm_num)

theorem sGlobal35_hz35 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal35_hz34 (by norm_num) (by norm_num)

theorem sGlobal35_hz36 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal35_hz35 sGlobal35_hz27 (by norm_num) (by norm_num)

theorem sGlobal35_hz37 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (s3rpp 12225 46) := by
    convert sGlobal35_hz36 using 1 <;>
      norm_num [s3rpp, mA] <;> ring

theorem sGlobal35_hz38 {c : ℝ} (hc : B (13 / 25) (21 / 40) c) : B (13 / 25) (21 / 40) c := hc

theorem sGlobal35_hz39 : B (674068063875522049 / 1000000000000000000) (26962722555021447 / 40000000000000000) (kdot ((13 / 25))) := by
    constructor
    · apply bkdot_lower (q := (28097574347450819 / 50000000000000000)) (a := (255986344024739419 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (561951486949016379 / 1000000000000000000)) (a := (10239453760989133 / 20000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal35_hz40 : B (169 / 625) (169 / 625) (((13 / 25) : ℝ)^2) := bsq (bpoint ((13 / 25) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal35_hz41 : B (456 / 625) (456 / 625) ((1 : ℝ) - (((13 / 25) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal35_hz40 (by norm_num) (by norm_num)

theorem sGlobal35_hz42 : B (13346347815039139 / 15625000000000000) (854166260162504897 / 1000000000000000000) (√((1 : ℝ) - (((13 / 25) : ℝ)^2))) := bsqrt sGlobal35_hz41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal35_hz43 : B (54377913010872213 / 200000000000000000) (135944782527180533 / 500000000000000000) ((√((1 : ℝ) - (((13 / 25) : ℝ)^2))) / Real.pi) := bdiv sGlobal35_hz42 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal35_hz44 : B (70103078643054293 / 200000000000000000) (350515393215278811 / 1000000000000000000) (((13 / 25) : ℝ) * (kdot ((13 / 25)))) := bmul (bpoint ((13 / 25) : ℝ)) sGlobal35_hz39 (by norm_num) (by norm_num)

theorem sGlobal35_hz45 : B (62240495826963253 / 100000000000000000) (622404958269639877 / 1000000000000000000) (((√((1 : ℝ) - (((13 / 25) : ℝ)^2))) / Real.pi) + (((13 / 25) : ℝ) * (kdot ((13 / 25))))) := badd sGlobal35_hz43 sGlobal35_hz44 (by norm_num) (by norm_num)

theorem sGlobal35_hz46 : B (62240495826963253 / 100000000000000000) (622404958269639877 / 1000000000000000000) (kappa ((13 / 25))) := by rw [kappa_eq]; exact sGlobal35_hz45

theorem sGlobal35_hz47 : B (337967342370948439 / 500000000000000000) (168983671185476741 / 250000000000000000) (kdot ((21 / 40))) := by
    constructor
    · apply bkdot_lower (q := (279049910336872163 / 500000000000000000)) (a := (127260151712264637 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (22323992826949773 / 40000000000000000)) (a := (509040606849042707 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal35_hz48 : B (441 / 1600) (441 / 1600) (((21 / 40) : ℝ)^2) := bsq (bpoint ((21 / 40) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal35_hz49 : B (1159 / 1600) (1159 / 1600) ((1 : ℝ) - (((21 / 40) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal35_hz48 (by norm_num) (by norm_num)

theorem sGlobal35_hz50 : B (3324618072372891 / 3906250000000000) (851102226527460097 / 1000000000000000000) (√((1 : ℝ) - (((21 / 40) : ℝ)^2))) := bsqrt sGlobal35_hz49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal35_hz51 : B (33864281607090831 / 125000000000000000) (5418285057134533 / 20000000000000000) ((√((1 : ℝ) - (((21 / 40) : ℝ)^2))) / Real.pi) := bdiv sGlobal35_hz50 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal35_hz52 : B (17743285474474793 / 50000000000000000) (354865709489501157 / 1000000000000000000) (((21 / 40) : ℝ) * (kdot ((21 / 40)))) := bmul (bpoint ((21 / 40) : ℝ)) sGlobal35_hz47 (by norm_num) (by norm_num)

theorem sGlobal35_hz53 : B (156444990586555627 / 250000000000000000) (625779962346227807 / 1000000000000000000) (((√((1 : ℝ) - (((21 / 40) : ℝ)^2))) / Real.pi) + (((21 / 40) : ℝ) * (kdot ((21 / 40))))) := badd sGlobal35_hz51 sGlobal35_hz52 (by norm_num) (by norm_num)

theorem sGlobal35_hz54 : B (156444990586555627 / 250000000000000000) (625779962346227807 / 1000000000000000000) (kappa ((21 / 40))) := by rw [kappa_eq]; exact sGlobal35_hz53

theorem sGlobal35_hz55 {c : ℝ} (hc : B (13 / 25) (21 / 40) c) : B (62240495826963253 / 100000000000000000) (625779962346227807 / 1000000000000000000) (kappa c) := bkappa (sGlobal35_hz38 hc) (by norm_num) (by norm_num) sGlobal35_hz46.1 sGlobal35_hz54.2

theorem sGlobal35_hz56 : B 24450 24450 ((2 : ℝ) * (12225 : ℝ)) := bmul (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal35_hz57 {c : ℝ} (hc : B (13 / 25) (21 / 40) c) : B (374220037653772193 / 1000000000000000000) (37759504173036747 / 100000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (sGlobal35_hz55 hc) (by norm_num) (by norm_num)

theorem sGlobal35_hz58 {c : ℝ} (hc : B (13 / 25) (21 / 40) c) : B (182993598412694602377 / 20000000000000000) (18464397540614969283 / 2000000000000000) (((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) := bmul sGlobal35_hz56 (sGlobal35_hz57 hc) (by norm_num) (by norm_num)

theorem sGlobal35_hz59 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (4 : ℝ)) sGlobal35_hz10 (by norm_num) (by norm_num)

theorem sGlobal35_hz60 {c : ℝ} (hc : B (13 / 25) (21 / 40) c) : B (914967926623800210249 / 100000000000000000) (1154024764488844578143 / 125000000000000000) ((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bsub (sGlobal35_hz58 hc) sGlobal35_hz59 (by norm_num) (by norm_num)

theorem sGlobal35_hz61 {c : ℝ} (hc : B (13 / 25) (21 / 40) c) : B (95653955831622573321 / 1000000000000000000) (96084328149343671337 / 1000000000000000000) (√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) := bsqrt (sGlobal35_hz60 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal35_hz62 : B (30670756373515103 / 125000000000000000) (122683025494060423 / 500000000000000000) ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal35_hz7 (by norm_num) (by norm_num)

theorem sGlobal35_hz63 {c : ℝ} (hc : B (13 / 25) (21 / 40) c) : B (3816343591225378099 / 40000000000000000) (95838962098355550513 / 1000000000000000000) ((√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) - ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))))) := bsub (sGlobal35_hz61 hc) sGlobal35_hz62 (by norm_num) (by norm_num)

theorem sGlobal35_hz64 {c : ℝ} (hc : B (13 / 25) (21 / 40) c) : B (3816343591225378099 / 40000000000000000) (95838962098355550513 / 1000000000000000000) (s3dm 12225 46 c) := by
    convert (sGlobal35_hz63 hc) using 1 <;>
      norm_num [s3dm, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal35_hz65 : B (6126072185528622723889 / 500000000000000000) (2450428874211449090087 / 200000000000000000) ((s3ap 12225 46)^2) := bsq sGlobal35_hz9 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal35_hz66 : B (6126072185528622723889 / 250000000000000000) (2450428874211449090087 / 100000000000000000) ((2 : ℝ) * ((s3ap 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal35_hz65 (by norm_num) (by norm_num)

theorem sGlobal35_hz67 {c : ℝ} (hc : B (13 / 25) (21 / 40) c) : B (2275699750982346220061 / 250000000000000000) (9185106656090031745883 / 1000000000000000000) ((s3dm 12225 46 c)^2) := bsq (sGlobal35_hz64 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal35_hz68 {c : ℝ} (hc : B (13 / 25) (21 / 40) c) : B (15319182086024459149673 / 1000000000000000000) (7700744869092553010313 / 500000000000000000) (((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) := bsub sGlobal35_hz66 (sGlobal35_hz67 hc) (by norm_num) (by norm_num)

theorem sGlobal35_hz69 : B (1524735695971823534271 / 125000000000000000) (609894278388729413841 / 50000000000000000) ((s3am 12225 46)^2) := bsq sGlobal35_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal35_hz70 : B (1524735695971823534271 / 62500000000000000) (609894278388729413841 / 25000000000000000) ((2 : ℝ) * ((s3am 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal35_hz69 (by norm_num) (by norm_num)

theorem sGlobal35_hz71 {c : ℝ} (hc : B (13 / 25) (21 / 40) c) : B (15698604074561883 / 25000000000000000) (315659006075488849 / 500000000000000000) ((((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) / ((2 : ℝ) * ((s3am 12225 46)^2))) := bdiv (sGlobal35_hz68 hc) sGlobal35_hz70 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal35_hz72 {c : ℝ} (hc : B (13 / 25) (21 / 40) c) : B (15698604074561883 / 25000000000000000) (315659006075488849 / 500000000000000000) (s3c1 12225 46 c) := by
    convert (sGlobal35_hz71 hc) using 1 <;>
      norm_num [s3c1] <;> ring

theorem sGlobal35_hz73 {c : ℝ} (hc : B (13 / 25) (21 / 40) c) : B (674068063875522049 / 1000000000000000000) (168983671185476741 / 250000000000000000) (kdot c) := bkdot (sGlobal35_hz38 hc) sGlobal35_hz39.1 sGlobal35_hz47.2

theorem sGlobal35_hz74 : B (358051691531593461 / 500000000000000000) (44756461441449183 / 62500000000000000) (kdot ((15698604074561883 / 25000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (9561241864655831 / 20000000000000000)) (a := (222971881536921909 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (478062093232791549 / 1000000000000000000)) (a := (445943763073843809 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal35_hz75 : B (14349714462246561 / 20000000000000000) (89685715389041007 / 125000000000000000) (kdot ((315659006075488849 / 500000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (237698613684048373 / 500000000000000000)) (a := (443772388402271457 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (95079445473619349 / 200000000000000000)) (a := (443772388402271449 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal35_hz76 {c : ℝ} (hc : B (13 / 25) (21 / 40) c) : B (358051691531593461 / 500000000000000000) (89685715389041007 / 125000000000000000) (kdot (s3c1 12225 46 c)) := bkdot (sGlobal35_hz72 hc) sGlobal35_hz74.1 sGlobal35_hz75.2

theorem sGlobal35_hz77 {c : ℝ} (hc : B (13 / 25) (21 / 40) c) : B (169 / 625) (441 / 1600) (c^2) := bsq (sGlobal35_hz38 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal35_hz78 {c : ℝ} (hc : B (13 / 25) (21 / 40) c) : B (1159 / 1600) (456 / 625) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (sGlobal35_hz77 hc) (by norm_num) (by norm_num)

theorem sGlobal35_hz79 {c : ℝ} (hc : B (13 / 25) (21 / 40) c) : B (3324618072372891 / 3906250000000000) (854166260162504897 / 1000000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (sGlobal35_hz78 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal35_hz80 : B (39119999999999765769 / 1600000000000000) (3912000000000000489 / 160000000000000) ((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (149450625 : ℝ)) sGlobal35_hz10 (by norm_num) (by norm_num)

theorem sGlobal35_hz81 {c : ℝ} (hc : B (13 / 25) (21 / 40) c) : B (17928150937359719 / 31250000000000000) (288680300890058217 / 500000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (sGlobal35_hz79 hc) (sGlobal35_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal35_hz82 {c : ℝ} (hc : B (13 / 25) (21 / 40) c) : B (561079411735606406361 / 40000000000000000) (14116466713523848575859 / 1000000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) := bmul sGlobal35_hz80 (sGlobal35_hz81 hc) (by norm_num) (by norm_num)

theorem sGlobal35_hz83 {c : ℝ} (hc : B (13 / 25) (21 / 40) c) : B (876686580836885009939 / 125000000000000000) (705823335676192428793 / 100000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) / (2 : ℝ)) := bdiv (sGlobal35_hz82 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal35_hz84 {c : ℝ} (hc : B (13 / 25) (21 / 40) c) : B (876686580836885009939 / 125000000000000000) (705823335676192428793 / 100000000000000000) (s3Cpa 12225 c) := by
    convert (sGlobal35_hz83 hc) using 1 <;>
      norm_num [s3Cpa, mA] <;> ring

theorem sGlobal35_hz85 {c : ℝ} (hc : B (13 / 25) (21 / 40) c) : B (33864281607090831 / 125000000000000000) (135944782527180533 / 500000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (sGlobal35_hz79 hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal35_hz86 {c : ℝ} (hc : B (13 / 25) (21 / 40) c) : B (70103078643054293 / 200000000000000000) (354865709489501157 / 1000000000000000000) (c * (kdot c)) := bmul (sGlobal35_hz38 hc) (sGlobal35_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal35_hz87 {c : ℝ} (hc : B (13 / 25) (21 / 40) c) : B (-83951456632774509 / 1000000000000000000) (-78625828160910399 / 1000000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (sGlobal35_hz85 hc) (sGlobal35_hz86 hc) (by norm_num) (by norm_num)

theorem sGlobal35_hz88 {c : ℝ} (hc : B (13 / 25) (21 / 40) c) : B (-2052613114671337001627 / 1000000000000000000) (-1922401498534247745171 / 1000000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) := bmul sGlobal35_hz80 (sGlobal35_hz87 hc) (by norm_num) (by norm_num)

theorem sGlobal35_hz89 {c : ℝ} (hc : B (13 / 25) (21 / 40) c) : B (-513153278667834250407 / 500000000000000000) (-192240149853424774517 / 200000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) / (2 : ℝ)) := bdiv (sGlobal35_hz88 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal35_hz90 {c : ℝ} (hc : B (13 / 25) (21 / 40) c) : B (-513153278667834250407 / 500000000000000000) (-192240149853424774517 / 200000000000000000) (s3Cpp 12225 c) := by
    convert (sGlobal35_hz89 hc) using 1 <;>
      norm_num [s3Cpp, mA] <;> ring

theorem sGlobal35_hz91 {c : ℝ} (hc : B (13 / 25) (21 / 40) c) : B (7128637756628817787913 / 1000000000000000000) (1793344616673915675039 / 250000000000000000) ((s3Cpa 12225 c) + (s3r1 12225 46)) := badd (sGlobal35_hz84 hc) sGlobal35_hz33 (by norm_num) (by norm_num)

theorem sGlobal35_hz92 {c : ℝ} (hc : B (13 / 25) (21 / 40) c) : B (6454524729996199789 / 100000000000000000) (32475172881280841633 / 500000000000000000) (((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) := bdiv (sGlobal35_hz91 hc) sGlobal35_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal35_hz93 {c : ℝ} (hc : B (13 / 25) (21 / 40) c) : B (32333965162728029151 / 500000000000000000) (65073028788055743689 / 1000000000000000000) ((((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) + (s3e0 12225 46)) := badd (sGlobal35_hz92 hc) sGlobal35_hz16 (by norm_num) (by norm_num)

theorem sGlobal35_hz94 {c : ℝ} (hc : B (13 / 25) (21 / 40) c) : B (32333965162728029151 / 500000000000000000) (65073028788055743689 / 1000000000000000000) (s3Lam 12225 46 c) := by
    convert (sGlobal35_hz93 hc) using 1 <;>
      norm_num [s3Lam] <;> ring

theorem sGlobal35_hz95 {c : ℝ} (hc : B (13 / 25) (21 / 40) c) : B (-474771575356588347607 / 500000000000000000) (-884437342644631597767 / 1000000000000000000) ((s3Cpp 12225 c) + (s3rpp 12225 46)) := badd (sGlobal35_hz90 hc) sGlobal35_hz37 (by norm_num) (by norm_num)

theorem sGlobal35_hz96 {c : ℝ} (hc : B (13 / 25) (21 / 40) c) : B (-681283654115801883001 / 1000000000000000000) (-442218671322315798883 / 1000000000000000000) (if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) := bweaken (bfirst (sGlobal35_hz95 hc) (sGlobal35_hz76 hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem sGlobal35_hz97 {c : ℝ} (hc : B (13 / 25) (21 / 40) c) : B (209097060628901964931 / 50000000000000000) (4234499075651131570303 / 1000000000000000000) ((s3Lam 12225 46 c)^2) := bsq (sGlobal35_hz94 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal35_hz98 {c : ℝ} (hc : B (13 / 25) (21 / 40) c) : B (394313871823761527 / 1000000000000000000) (15942497298650481 / 40000000000000000) ((s3c1 12225 46 c)^2) := bsq (sGlobal35_hz72 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal35_hz99 {c : ℝ} (hc : B (13 / 25) (21 / 40) c) : B (24057502701349519 / 40000000000000000) (605686128176238473 / 1000000000000000000) ((1 : ℝ) - ((s3c1 12225 46 c)^2)) := bsub (bpoint (1 : ℝ)) (sGlobal35_hz98 hc) (by norm_num) (by norm_num)

theorem sGlobal35_hz100 {c : ℝ} (hc : B (13 / 25) (21 / 40) c) : B (24235126872881561 / 31250000000000000) (778258394221506919 / 1000000000000000000) (√((1 : ℝ) - ((s3c1 12225 46 c)^2))) := bsqrt (sGlobal35_hz99 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal35_hz101 {c : ℝ} (hc : B (13 / 25) (21 / 40) c) : B (243638068936516131 / 100000000000000000) (2444970853880875331 / 1000000000000000000) (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))) := bmul pi_mem (sGlobal35_hz100 hc) (by norm_num) (by norm_num)

theorem sGlobal35_hz102 {c : ℝ} (hc : B (13 / 25) (21 / 40) c) : B (427606448348871933537 / 250000000000000000) (1738028500281086740433 / 1000000000000000000) (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2))))) := bdiv (sGlobal35_hz97 hc) (sGlobal35_hz101 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal35_hz103 {c : ℝ} (hc : B (13 / 25) (21 / 40) c) : B (1029142139279685851147 / 1000000000000000000) (25916196579175418831 / 20000000000000000) ((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) := badd (sGlobal35_hz96 hc) (sGlobal35_hz102 hc) (by norm_num) (by norm_num)

theorem sGlobal35_hz104 : B (3762781186094069 / 250000000000000000) (376278118609407 / 25000000000000000) ((s3e0 12225 46)^2) := bsq sGlobal35_hz16 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal35_hz105 {c : ℝ} (hc : B (13 / 25) (21 / 40) c) : B (1029157190404430227423 / 1000000000000000000) (129582488008351531783 / 100000000000000000) (((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) := badd (sGlobal35_hz103 hc) sGlobal35_hz104 (by norm_num) (by norm_num)

theorem sGlobal35_hz106 {c : ℝ} (hc : B (13 / 25) (21 / 40) c) : B (533827131927838748777 / 500000000000000000) (667160976768819793923 / 500000000000000000) ((((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) + (s3rs 12225 46 maskSlack)) := badd (sGlobal35_hz105 hc) sGlobal35_hz29 (by norm_num) (by norm_num)

theorem sGlobal35_hz107 {c : ℝ} (hc : B (13 / 25) (21 / 40) c) : B (533827131927838748777 / 500000000000000000) (667160976768819793923 / 500000000000000000) (s3U 12225 46 maskSlack c) := by
    convert (sGlobal35_hz106 hc) using 1 <;>
      norm_num [s3U] <;> ring

theorem sGlobal35_hz108 {c : ℝ} (hc : B (13 / 25) (21 / 40) c) : B (-68941872747385048477 / 62500000000000000) (-207592831177923135637 / 200000000000000000) ((s3Cpp 12225 c) - (s3rpp 12225 46)) := bsub (sGlobal35_hz90 hc) sGlobal35_hz37 (by norm_num) (by norm_num)

theorem sGlobal35_hz109 {c : ℝ} (hc : B (13 / 25) (21 / 40) c) : B (-68941872747385048477 / 62500000000000000) (-207592831177923135637 / 200000000000000000) (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ)) := bweaken (bmin (sGlobal35_hz108 hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem sGlobal35_hz110 {c : ℝ} (hc : B (13 / 25) (21 / 40) c) : B (-395718475367005315269 / 500000000000000000) (-47570537185976251 / 64000000000000) ((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) := bmul (sGlobal35_hz76 hc) (sGlobal35_hz109 hc) (by norm_num) (by norm_num)

theorem sGlobal35_hz111 {c : ℝ} (hc : B (13 / 25) (21 / 40) c) : B (-395726000929377503409 / 500000000000000000) (-743304694655623298151 / 1000000000000000000) (((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) := bsub (sGlobal35_hz110 hc) sGlobal35_hz104 (by norm_num) (by norm_num)

theorem sGlobal35_hz112 {c : ℝ} (hc : B (13 / 25) (21 / 40) c) : B (-414974537656439638417 / 500000000000000000) (-390900884053435284141 / 500000000000000000) ((((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) - (s3rs 12225 46 maskSlack)) := bsub (sGlobal35_hz111 hc) sGlobal35_hz29 (by norm_num) (by norm_num)

theorem sGlobal35_hz113 {c : ℝ} (hc : B (13 / 25) (21 / 40) c) : B (-414974537656439638417 / 500000000000000000) (-390900884053435284141 / 500000000000000000) (s3L 12225 46 maskSlack c) := by
    convert (sGlobal35_hz112 hc) using 1 <;>
      norm_num [s3L] <;> ring

theorem sGlobal35_hz114 {c : ℝ} (hc : B (13 / 25) (21 / 40) c) : B 0 (667160976768819793923 / 500000000000000000) |(s3U 12225 46 maskSlack c)| := bweaken (babs (sGlobal35_hz107 hc)) (by norm_num) (by norm_num)

theorem sGlobal35_hz115 {c : ℝ} (hc : B (13 / 25) (21 / 40) c) : B 0 (414974537656439638417 / 500000000000000000) |(s3L 12225 46 maskSlack c)| := bweaken (babs (sGlobal35_hz113 hc)) (by norm_num) (by norm_num)

theorem sGlobal35_hz116 {c : ℝ} (hc : B (13 / 25) (21 / 40) c) : B 0 (667160976768819793923 / 500000000000000000) (max |(s3U 12225 46 maskSlack c)| |(s3L 12225 46 maskSlack c)|) := bweaken (bmax (sGlobal35_hz114 hc) (sGlobal35_hz115 hc)) (by norm_num) (by norm_num)

theorem sGlobal35_hz117 {c : ℝ} (hc : B (13 / 25) (21 / 40) c) : B 0 (667160976768819793923 / 500000000000000000) (s3nks 12225 46 maskSlack c) := by
    convert (sGlobal35_hz116 hc) using 1 <;>
      norm_num [s3nks] <;> ring

theorem sGlobal35 {c : ℝ} (hc : B (13 / 25) (21 / 40) c) :
    0 < s3am 12225 46 ∧ 0 ≤ s3dm 12225 46 c ∧
    s3dm 12225 46 c ^ 2 ≤ 2 * s3ap 12225 46 ^ 2 ∧ s3c1 12225 46 c < 1 ∧
    0 ≤ s3Cpa 12225 c - s3r1 12225 46 ∧
    s3e0 12225 46 ≤ (s3Cpa 12225 c - s3r1 12225 46) / s3ap 12225 46 ∧
    s3nks 12225 46 maskSlack c ≤ 12225 * (109147 / 1000000) := by

  refine ⟨lt_of_lt_of_le (by norm_num) sGlobal35_hz14.1,
    le_trans (by norm_num) (sGlobal35_hz64 hc).1, ?_,
    lt_of_le_of_lt (sGlobal35_hz72 hc).2 (by norm_num), ?_, ?_,
    le_trans (sGlobal35_hz117 hc).2 (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (sGlobal35_hz64 hc).1) (sGlobal35_hz64 hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) sGlobal35_hz9.1 2
    nlinarith only [h1, h2]
  · linarith only [(sGlobal35_hz84 hc).1, sGlobal35_hz33.2]
  · have hap : 0 < s3ap 12225 46 := lt_of_lt_of_le (by norm_num) sGlobal35_hz9.1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul sGlobal35_hz16.2 sGlobal35_hz9.2 (le_trans (by norm_num) sGlobal35_hz9.1) (by norm_num)
    linarith only [h, (sGlobal35_hz84 hc).1, sGlobal35_hz33.2]

end BstLean.Part255
