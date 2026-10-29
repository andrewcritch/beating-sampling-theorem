import BstLean.Part255SGlobal1
import BstLean.Part255Numeric10
namespace BstLean.Part255
open Real BstLean.Part130 BstLean.Part182 BstLean.Part197 BstLean.Part246
theorem sGlobal5_hz0 : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal5_hz1 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) ((√(23 : ℝ)) / (12225 : ℝ)) := bdiv sGlobal5_hz0 (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal5_hz2 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) maskSlack := by
    convert sGlobal5_hz1 using 1 <;>
      norm_num [maskSlack] <;> ring

theorem sGlobal5_hz3 : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal5_hz4 : B (6395294793910793 / 500000000000000000) (12790589587821587 / 1000000000000000000) (√((2 / 12225) : ℝ)) := bsqrt (bpoint ((2 / 12225) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal5_hz5 : B (7230130686979 / 62500000000000000) (23136418198333 / 200000000000000000) (√((2 / 149450625) : ℝ)) := bsqrt (bpoint ((2 / 149450625) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal5_hz6 : B (2211334438749598093 / 20000000000000000) (110566721937479904651 / 1000000000000000000) (√(12225 : ℝ)) := bsqrt (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal5_hz7 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))) := bmul sGlobal5_hz3 sGlobal5_hz4 (by norm_num) (by norm_num)

theorem sGlobal5_hz8 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) ((√(12225 : ℝ)) + ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := badd sGlobal5_hz6 sGlobal5_hz7 (by norm_num) (by norm_num)

theorem sGlobal5_hz9 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) (s3ap 12225 46) := by
    convert sGlobal5_hz8 using 1 <;>
      norm_num [s3ap, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal5_hz10 : B (163599182004089 / 1000000000000000000) (16359918200409 / 100000000000000000) ((2 : ℝ) / (12225 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal5_hz11 : B (1222499983640081799591 / 100000000000000000) (12224999836400817995911 / 1000000000000000000) ((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ))) := bsub (bpoint (12225 : ℝ)) sGlobal5_hz10 (by norm_num) (by norm_num)

theorem sGlobal5_hz12 : B (110566721197658827907 / 1000000000000000000) (27641680299414706977 / 250000000000000000) (√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) := bsqrt sGlobal5_hz11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal5_hz13 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) ((√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) - ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bsub sGlobal5_hz12 sGlobal5_hz7 (by norm_num) (by norm_num)

theorem sGlobal5_hz14 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) (s3am 12225 46) := by
    convert sGlobal5_hz13 using 1 <;>
      norm_num [s3am, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal5_hz15 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√((2 / 12225) : ℝ)) * (√(92 : ℝ))) := bmul sGlobal5_hz4 sGlobal5_hz3 (by norm_num) (by norm_num)

theorem sGlobal5_hz16 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) (s3e0 12225 46) := by
    convert sGlobal5_hz15 using 1 <;>
      norm_num [s3e0, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal5_hz17 : B (250196148528560847 / 500000000000000000) (100078459411424339 / 200000000000000000) (((1 / 2) : ℝ) + maskSlack) := badd (bpoint ((1 / 2) : ℝ)) sGlobal5_hz2 (by norm_num) (by norm_num)

theorem sGlobal5_hz18 : B (59827153232297998295487 / 800000000000000) (23930861292919199366019 / 320000000000000) ((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack)) := bmul (bpoint (149450625 : ℝ)) sGlobal5_hz17 (by norm_num) (by norm_num)

theorem sGlobal5_hz19 : B (1729554180017180009583 / 200000000000000000) (8647770900085900056557 / 1000000000000000000) (√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) := bsqrt sGlobal5_hz18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal5_hz20 : B (4328681281566262743499 / 500000000000000000) (8657362563132525495641 / 1000000000000000000) ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))) := badd sGlobal5_hz19 sGlobal5_hz3 (by norm_num) (by norm_num)

theorem sGlobal5_hz21 : B (110732771457999278473 / 1000000000000000000) (55366385728999643621 / 500000000000000000) ((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ)))) := bmul sGlobal5_hz4 sGlobal5_hz20 (by norm_num) (by norm_num)

theorem sGlobal5_hz22 : B (209099159 / 15625000000000000) (13382346177 / 1000000000000000000) ((2 : ℝ) / (149450625 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (149450625 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal5_hz23 : B (2452349334953899930479 / 200000000000000000) (12261746674769501594427 / 1000000000000000000) (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2) := bsq sGlobal5_hz21 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal5_hz24 : B (82045469362091 / 500000000000000000) (32818187747289 / 200000000000000000) (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2)) := bmul sGlobal5_hz22 sGlobal5_hz23 (by norm_num) (by norm_num)

theorem sGlobal5_hz25 : B (82045469362091 / 250000000000000000) (32818187747289 / 100000000000000000) ((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) := bmul (bpoint (2 : ℝ)) sGlobal5_hz24 (by norm_num) (by norm_num)

theorem sGlobal5_hz26 : B (117258080744995992792057 / 1000000000000000000) (58629040372497996396029 / 500000000000000000) (√(13749457500 : ℝ)) := bsqrt (bpoint (13749457500 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal5_hz27 : B (117304080744995992792057 / 1000000000000000000) (58652040372497996396029 / 500000000000000000) ((√(13749457500 : ℝ)) + (46 : ℝ)) := badd sGlobal5_hz26 (bpoint (46 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal5_hz28 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal5_hz25 sGlobal5_hz27 (by norm_num) (by norm_num)

theorem sGlobal5_hz29 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (s3rs 12225 46 maskSlack) := by
    convert sGlobal5_hz28 using 1 <;>
      norm_num [s3rs, s3pp, s3K, mA, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal5_hz30 : B (490797546012267 / 1000000000000000000) (49079754601227 / 100000000000000000) ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (3 : ℝ)) sGlobal5_hz10 (by norm_num) (by norm_num)

theorem sGlobal5_hz31 : B (490797546012267 / 500000000000000000) (49079754601227 / 50000000000000000) ((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal5_hz30 (by norm_num) (by norm_num)

theorem sGlobal5_hz32 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal5_hz31 sGlobal5_hz27 (by norm_num) (by norm_num)

theorem sGlobal5_hz33 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (s3r1 12225 46) := by
    convert sGlobal5_hz32 using 1 <;>
      norm_num [s3r1, mA] <;> ring

theorem sGlobal5_hz34 : B (163599182004089 / 500000000000000000) (16359918200409 / 50000000000000000) ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (2 : ℝ)) sGlobal5_hz10 (by norm_num) (by norm_num)

theorem sGlobal5_hz35 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal5_hz34 (by norm_num) (by norm_num)

theorem sGlobal5_hz36 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal5_hz35 sGlobal5_hz27 (by norm_num) (by norm_num)

theorem sGlobal5_hz37 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (s3rpp 12225 46) := by
    convert sGlobal5_hz36 using 1 <;>
      norm_num [s3rpp, mA] <;> ring

theorem sGlobal5_hz38 {c : ℝ} (hc : B (37 / 100) (3 / 8) c) : B (37 / 100) (3 / 8) c := hc

theorem sGlobal5_hz39 : B (77580289777347187 / 125000000000000000) (620642318359675101 / 1000000000000000000) (kdot ((37 / 100))) := by
    constructor
    · apply bkdot_lower (q := (678125367906657911 / 1000000000000000000)) (a := (595893653083371583 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (67812536790665791 / 100000000000000000)) (a := (18621676651939067 / 31250000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal5_hz40 : B (1369 / 10000) (1369 / 10000) (((37 / 100) : ℝ)^2) := bsq (bpoint ((37 / 100) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal5_hz41 : B (8631 / 10000) (8631 / 10000) ((1 : ℝ) - (((37 / 100) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal5_hz40 (by norm_num) (by norm_num)

theorem sGlobal5_hz42 : B (116128969254015167 / 125000000000000000) (929031754032121337 / 1000000000000000000) (√((1 : ℝ) - (((37 / 100) : ℝ)^2))) := bsqrt sGlobal5_hz41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal5_hz43 : B (18482499492943247 / 62500000000000000) (147859995943545977 / 500000000000000000) ((√((1 : ℝ) - (((37 / 100) : ℝ)^2))) / Real.pi) := bdiv sGlobal5_hz42 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal5_hz44 : B (229637657740947673 / 1000000000000000000) (57409414448269947 / 250000000000000000) (((37 / 100) : ℝ) * (kdot ((37 / 100)))) := bmul (bpoint ((37 / 100) : ℝ)) sGlobal5_hz39 (by norm_num) (by norm_num)

theorem sGlobal5_hz45 : B (4202861197024317 / 8000000000000000) (262678824840085871 / 500000000000000000) (((√((1 : ℝ) - (((37 / 100) : ℝ)^2))) / Real.pi) + (((37 / 100) : ℝ) * (kdot ((37 / 100))))) := badd sGlobal5_hz43 sGlobal5_hz44 (by norm_num) (by norm_num)

theorem sGlobal5_hz46 : B (4202861197024317 / 8000000000000000) (262678824840085871 / 500000000000000000) (kappa ((37 / 100))) := by rw [kappa_eq]; exact sGlobal5_hz45

theorem sGlobal5_hz47 : B (622357293523016123 / 1000000000000000000) (311178646814514469 / 500000000000000000) (kdot ((3 / 8))) := by
    constructor
    · apply bkdot_lower (q := (674199862463242087 / 1000000000000000000)) (a := (148299944043732397 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (337099931231621043 / 500000000000000000)) (a := (593199776008405049 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal5_hz48 : B (9 / 64) (9 / 64) (((3 / 8) : ℝ)^2) := bsq (bpoint ((3 / 8) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal5_hz49 : B (55 / 64) (55 / 64) ((1 : ℝ) - (((3 / 8) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal5_hz48 (by norm_num) (by norm_num)

theorem sGlobal5_hz50 : B (231756202721739467 / 250000000000000000) (927024810886957869 / 1000000000000000000) (√((1 : ℝ) - (((3 / 8) : ℝ)^2))) := bsqrt sGlobal5_hz49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal5_hz51 : B (29508116204297763 / 100000000000000000) (295081162042977631 / 1000000000000000000) ((√((1 : ℝ) - (((3 / 8) : ℝ)^2))) / Real.pi) := bdiv sGlobal5_hz50 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal5_hz52 : B (116691992535565523 / 500000000000000000) (58345996277721463 / 250000000000000000) (((3 / 8) : ℝ) * (kdot ((3 / 8)))) := bmul (bpoint ((3 / 8) : ℝ)) sGlobal5_hz47 (by norm_num) (by norm_num)

theorem sGlobal5_hz53 : B (132116286778527169 / 250000000000000000) (528465147153863483 / 1000000000000000000) (((√((1 : ℝ) - (((3 / 8) : ℝ)^2))) / Real.pi) + (((3 / 8) : ℝ) * (kdot ((3 / 8))))) := badd sGlobal5_hz51 sGlobal5_hz52 (by norm_num) (by norm_num)

theorem sGlobal5_hz54 : B (132116286778527169 / 250000000000000000) (528465147153863483 / 1000000000000000000) (kappa ((3 / 8))) := by rw [kappa_eq]; exact sGlobal5_hz53

theorem sGlobal5_hz55 {c : ℝ} (hc : B (37 / 100) (3 / 8) c) : B (4202861197024317 / 8000000000000000) (528465147153863483 / 1000000000000000000) (kappa c) := bkappa (sGlobal5_hz38 hc) (by norm_num) (by norm_num) sGlobal5_hz46.1 sGlobal5_hz54.2

theorem sGlobal5_hz56 : B 24450 24450 ((2 : ℝ) * (12225 : ℝ)) := bmul (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal5_hz57 {c : ℝ} (hc : B (37 / 100) (3 / 8) c) : B (471534852846136517 / 1000000000000000000) (3797138802975683 / 8000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (sGlobal5_hz55 hc) (by norm_num) (by norm_num)

theorem sGlobal5_hz58 {c : ℝ} (hc : B (37 / 100) (3 / 8) c) : B (230580543041760756813 / 20000000000000000) (1856800874655108987 / 160000000000000) (((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) := bmul sGlobal5_hz56 (sGlobal5_hz57 hc) (by norm_num) (by norm_num)

theorem sGlobal5_hz59 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (4 : ℝ)) sGlobal5_hz10 (by norm_num) (by norm_num)

theorem sGlobal5_hz60 {c : ℝ} (hc : B (37 / 100) (3 / 8) c) : B (1152902649769130982429 / 100000000000000000) (5802502406098851576197 / 500000000000000000) ((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bsub (sGlobal5_hz58 hc) sGlobal5_hz59 (by norm_num) (by norm_num)

theorem sGlobal5_hz61 {c : ℝ} (hc : B (37 / 100) (3 / 8) c) : B (26843326099902501911 / 250000000000000000) (26931631973617128853 / 250000000000000000) (√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) := bsqrt (sGlobal5_hz60 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal5_hz62 : B (30670756373515103 / 125000000000000000) (122683025494060423 / 500000000000000000) ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal5_hz7 (by norm_num) (by norm_num)

theorem sGlobal5_hz63 {c : ℝ} (hc : B (37 / 100) (3 / 8) c) : B (53563969174310943399 / 500000000000000000) (26870290460870098647 / 250000000000000000) ((√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) - ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))))) := bsub (sGlobal5_hz61 hc) sGlobal5_hz62 (by norm_num) (by norm_num)

theorem sGlobal5_hz64 {c : ℝ} (hc : B (37 / 100) (3 / 8) c) : B (53563969174310943399 / 500000000000000000) (26870290460870098647 / 250000000000000000) (s3dm 12225 46 c) := by
    convert (sGlobal5_hz63 hc) using 1 <;>
      norm_num [s3dm, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal5_hz65 : B (6126072185528622723889 / 500000000000000000) (2450428874211449090087 / 200000000000000000) ((s3ap 12225 46)^2) := bsq sGlobal5_hz9 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal5_hz66 : B (6126072185528622723889 / 250000000000000000) (2450428874211449090087 / 100000000000000000) ((2 : ℝ) * ((s3ap 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal5_hz65 (by norm_num) (by norm_num)

theorem sGlobal5_hz67 {c : ℝ} (hc : B (37 / 100) (3 / 8) c) : B (2295279034965226374043 / 200000000000000000) (2888050037806106473393 / 250000000000000000) ((s3dm 12225 46 c)^2) := bsq (sGlobal5_hz64 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal5_hz68 {c : ℝ} (hc : B (37 / 100) (3 / 8) c) : B (25297048029082158207 / 1953125000000000) (2605578713457671806131 / 200000000000000000) (((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) := bsub sGlobal5_hz66 (sGlobal5_hz67 hc) (by norm_num) (by norm_num)

theorem sGlobal5_hz69 : B (1524735695971823534271 / 125000000000000000) (609894278388729413841 / 50000000000000000) ((s3am 12225 46)^2) := bsq sGlobal5_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal5_hz70 : B (1524735695971823534271 / 62500000000000000) (609894278388729413841 / 25000000000000000) ((2 : ℝ) * ((s3am 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal5_hz69 (by norm_num) (by norm_num)

theorem sGlobal5_hz71 {c : ℝ} (hc : B (37 / 100) (3 / 8) c) : B (2073887961034333 / 3906250000000000) (106804523578304067 / 200000000000000000) ((((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) / ((2 : ℝ) * ((s3am 12225 46)^2))) := bdiv (sGlobal5_hz68 hc) sGlobal5_hz70 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal5_hz72 {c : ℝ} (hc : B (37 / 100) (3 / 8) c) : B (2073887961034333 / 3906250000000000) (106804523578304067 / 200000000000000000) (s3c1 12225 46 c) := by
    convert (sGlobal5_hz71 hc) using 1 <;>
      norm_num [s3c1] <;> ring

theorem sGlobal5_hz73 {c : ℝ} (hc : B (37 / 100) (3 / 8) c) : B (77580289777347187 / 125000000000000000) (311178646814514469 / 500000000000000000) (kdot c) := bkdot (sGlobal5_hz38 hc) sGlobal5_hz39.1 sGlobal5_hz47.2

theorem sGlobal5_hz74 : B (678151778115445371 / 1000000000000000000) (16953794452886303 / 25000000000000000) (kdot ((2073887961034333 / 3906250000000000))) := by
    constructor
    · apply bkdot_lower (q := (553541315283884457 / 1000000000000000000)) (a := (50555800472172727 / 100000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (69192664410485557 / 125000000000000000)) (a := (505558004721716671 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal5_hz75 : B (339660144499156791 / 500000000000000000) (679320288998319039 / 1000000000000000000) (kdot ((106804523578304067 / 200000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (137786461061277889 / 250000000000000000)) (a := (251861256059549011 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (110229168849022311 / 200000000000000000)) (a := (125930628029772363 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal5_hz76 {c : ℝ} (hc : B (37 / 100) (3 / 8) c) : B (678151778115445371 / 1000000000000000000) (679320288998319039 / 1000000000000000000) (kdot (s3c1 12225 46 c)) := bkdot (sGlobal5_hz72 hc) sGlobal5_hz74.1 sGlobal5_hz75.2

theorem sGlobal5_hz77 {c : ℝ} (hc : B (37 / 100) (3 / 8) c) : B (1369 / 10000) (9 / 64) (c^2) := bsq (sGlobal5_hz38 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal5_hz78 {c : ℝ} (hc : B (37 / 100) (3 / 8) c) : B (55 / 64) (8631 / 10000) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (sGlobal5_hz77 hc) (by norm_num) (by norm_num)

theorem sGlobal5_hz79 {c : ℝ} (hc : B (37 / 100) (3 / 8) c) : B (231756202721739467 / 250000000000000000) (929031754032121337 / 1000000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (sGlobal5_hz78 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal5_hz80 : B (39119999999999765769 / 1600000000000000) (3912000000000000489 / 160000000000000) ((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (149450625 : ℝ)) sGlobal5_hz10 (by norm_num) (by norm_num)

theorem sGlobal5_hz81 {c : ℝ} (hc : B (37 / 100) (3 / 8) c) : B (287675413837602667 / 500000000000000000) (72273711016857591 / 125000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (sGlobal5_hz79 hc) (sGlobal5_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal5_hz82 {c : ℝ} (hc : B (37 / 100) (3 / 8) c) : B (562693109466347447527 / 40000000000000000) (14136737874897346566693 / 1000000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) := bmul sGlobal5_hz80 (sGlobal5_hz81 hc) (by norm_num) (by norm_num)

theorem sGlobal5_hz83 {c : ℝ} (hc : B (37 / 100) (3 / 8) c) : B (7033663868329343094087 / 1000000000000000000) (7068368937448673283347 / 1000000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) / (2 : ℝ)) := bdiv (sGlobal5_hz82 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal5_hz84 {c : ℝ} (hc : B (37 / 100) (3 / 8) c) : B (7033663868329343094087 / 1000000000000000000) (7068368937448673283347 / 1000000000000000000) (s3Cpa 12225 c) := by
    convert (sGlobal5_hz83 hc) using 1 <;>
      norm_num [s3Cpa, mA] <;> ring

theorem sGlobal5_hz85 {c : ℝ} (hc : B (37 / 100) (3 / 8) c) : B (29508116204297763 / 100000000000000000) (147859995943545977 / 500000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (sGlobal5_hz79 hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal5_hz86 {c : ℝ} (hc : B (37 / 100) (3 / 8) c) : B (229637657740947673 / 1000000000000000000) (58345996277721463 / 250000000000000000) (c * (kdot c)) := bmul (sGlobal5_hz38 hc) (sGlobal5_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal5_hz87 {c : ℝ} (hc : B (37 / 100) (3 / 8) c) : B (30848588466045889 / 500000000000000000) (66082334146144281 / 1000000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (sGlobal5_hz85 hc) (sGlobal5_hz86 hc) (by norm_num) (by norm_num)

theorem sGlobal5_hz88 {c : ℝ} (hc : B (37 / 100) (3 / 8) c) : B (75424798799481746999 / 50000000000000000) (323142613974645574483 / 200000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) := bmul sGlobal5_hz80 (sGlobal5_hz87 hc) (by norm_num) (by norm_num)

theorem sGlobal5_hz89 {c : ℝ} (hc : B (37 / 100) (3 / 8) c) : B (75424798799481746999 / 100000000000000000) (50491033433538371013 / 62500000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) / (2 : ℝ)) := bdiv (sGlobal5_hz88 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal5_hz90 {c : ℝ} (hc : B (37 / 100) (3 / 8) c) : B (75424798799481746999 / 100000000000000000) (50491033433538371013 / 62500000000000000) (s3Cpp 12225 c) := by
    convert (sGlobal5_hz89 hc) using 1 <;>
      norm_num [s3Cpp, mA] <;> ring

theorem sGlobal5_hz91 {c : ℝ} (hc : B (37 / 100) (3 / 8) c) : B (893601122282885100311 / 125000000000000000) (7183514047382411695573 / 1000000000000000000) ((s3Cpa 12225 c) + (s3r1 12225 46)) := badd (sGlobal5_hz84 hc) sGlobal5_hz33 (by norm_num) (by norm_num)

theorem sGlobal5_hz92 {c : ℝ} (hc : B (37 / 100) (3 / 8) c) : B (4045492799212495499 / 62500000000000000) (13008423390286491977 / 200000000000000000) (((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) := bdiv (sGlobal5_hz91 hc) sGlobal5_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal5_hz93 {c : ℝ} (hc : B (37 / 100) (3 / 8) c) : B (16212641953223497099 / 250000000000000000) (16291199994231630077 / 250000000000000000) ((((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) + (s3e0 12225 46)) := badd (sGlobal5_hz92 hc) sGlobal5_hz16 (by norm_num) (by norm_num)

theorem sGlobal5_hz94 {c : ℝ} (hc : B (37 / 100) (3 / 8) c) : B (16212641953223497099 / 250000000000000000) (16291199994231630077 / 250000000000000000) (s3Lam 12225 46 c) := by
    convert (sGlobal5_hz93 hc) using 1 <;>
      norm_num [s3Lam] <;> ring

theorem sGlobal5_hz95 {c : ℝ} (hc : B (37 / 100) (3 / 8) c) : B (83101139461730927559 / 100000000000000000) (442309970779553105513 / 500000000000000000) ((s3Cpp 12225 c) + (s3rpp 12225 46)) := badd (sGlobal5_hz90 hc) sGlobal5_hz37 (by norm_num) (by norm_num)

theorem sGlobal5_hz96 {c : ℝ} (hc : B (37 / 100) (3 / 8) c) : B (83101139461730927559 / 200000000000000000) (120188054870721626047 / 200000000000000000) (if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) := bweaken (bfirst (sGlobal5_hz95 hc) (sGlobal5_hz76 hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem sGlobal5_hz97 {c : ℝ} (hc : B (37 / 100) (3 / 8) c) : B (210279807282738088877 / 50000000000000000) (2123225578016421310833 / 500000000000000000) ((s3Lam 12225 46 c)^2) := bsq (sGlobal5_hz94 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal5_hz98 {c : ℝ} (hc : B (37 / 100) (3 / 8) c) : B (140935537456681553 / 500000000000000000) (57036031283942547 / 200000000000000000) ((s3c1 12225 46 c)^2) := bsq (sGlobal5_hz72 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal5_hz99 {c : ℝ} (hc : B (37 / 100) (3 / 8) c) : B (142963968716057453 / 200000000000000000) (359064462543318447 / 500000000000000000) ((1 : ℝ) - ((s3c1 12225 46 c)^2)) := bsub (bpoint (1 : ℝ)) (sGlobal5_hz98 hc) (by norm_num) (by norm_num)

theorem sGlobal5_hz100 {c : ℝ} (hc : B (37 / 100) (3 / 8) c) : B (169094038165783629 / 200000000000000000) (847424878727688107 / 1000000000000000000) (√((1 : ℝ) - ((s3c1 12225 46 c)^2))) := bsqrt (sGlobal5_hz99 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal5_hz101 {c : ℝ} (hc : B (37 / 100) (3 / 8) c) : B (1328061470168644913 / 500000000000000000) (2662263773480126409 / 1000000000000000000) (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))) := bmul pi_mem (sGlobal5_hz100 hc) (by norm_num) (by norm_num)

theorem sGlobal5_hz102 {c : ℝ} (hc : B (37 / 100) (3 / 8) c) : B (1579706784710210167339 / 1000000000000000000) (7993702195677741741 / 5000000000000000) (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2))))) := bdiv (sGlobal5_hz97 hc) (sGlobal5_hz101 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal5_hz103 {c : ℝ} (hc : B (37 / 100) (3 / 8) c) : B (997606241009432402567 / 500000000000000000) (439936142697831295687 / 200000000000000000) ((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) := badd (sGlobal5_hz96 hc) (sGlobal5_hz102 hc) (by norm_num) (by norm_num)

theorem sGlobal5_hz104 : B (3762781186094069 / 250000000000000000) (376278118609407 / 25000000000000000) ((s3e0 12225 46)^2) := bsq sGlobal5_hz16 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal5_hz105 {c : ℝ} (hc : B (37 / 100) (3 / 8) c) : B (199522753314360918141 / 100000000000000000) (439939152922780170943 / 200000000000000000) (((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) := badd (sGlobal5_hz103 hc) sGlobal5_hz104 (by norm_num) (by norm_num)

theorem sGlobal5_hz106 {c : ℝ} (hc : B (37 / 100) (3 / 8) c) : B (2033724606594856451541 / 1000000000000000000) (2238192838068025124731 / 1000000000000000000) ((((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) + (s3rs 12225 46 maskSlack)) := badd (sGlobal5_hz105 hc) sGlobal5_hz29 (by norm_num) (by norm_num)

theorem sGlobal5_hz107 {c : ℝ} (hc : B (37 / 100) (3 / 8) c) : B (2033724606594856451541 / 1000000000000000000) (2238192838068025124731 / 1000000000000000000) (s3U 12225 46 maskSlack c) := by
    convert (sGlobal5_hz106 hc) using 1 <;>
      norm_num [s3U] <;> ring

theorem sGlobal5_hz108 {c : ℝ} (hc : B (37 / 100) (3 / 8) c) : B (169371145343081298793 / 250000000000000000) (45693320519632633163 / 62500000000000000) ((s3Cpp 12225 c) - (s3rpp 12225 46)) := bsub (sGlobal5_hz90 hc) sGlobal5_hz37 (by norm_num) (by norm_num)

theorem sGlobal5_hz109 {c : ℝ} (hc : B (37 / 100) (3 / 8) c) : B 0 0 (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ)) := bweaken (bmin (sGlobal5_hz108 hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem sGlobal5_hz110 {c : ℝ} (hc : B (37 / 100) (3 / 8) c) : B 0 0 ((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) := bmul (sGlobal5_hz76 hc) (sGlobal5_hz109 hc) (by norm_num) (by norm_num)

theorem sGlobal5_hz111 {c : ℝ} (hc : B (37 / 100) (3 / 8) c) : B (-376278118609407 / 25000000000000000) (-3762781186094069 / 250000000000000000) (((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) := bsub (sGlobal5_hz110 hc) sGlobal5_hz104 (by norm_num) (by norm_num)

theorem sGlobal5_hz112 {c : ℝ} (hc : B (37 / 100) (3 / 8) c) : B (-4814015572358580787 / 125000000000000000) (-38512124575991646407 / 1000000000000000000) ((((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) - (s3rs 12225 46 maskSlack)) := bsub (sGlobal5_hz111 hc) sGlobal5_hz29 (by norm_num) (by norm_num)

theorem sGlobal5_hz113 {c : ℝ} (hc : B (37 / 100) (3 / 8) c) : B (-4814015572358580787 / 125000000000000000) (-38512124575991646407 / 1000000000000000000) (s3L 12225 46 maskSlack c) := by
    convert (sGlobal5_hz112 hc) using 1 <;>
      norm_num [s3L] <;> ring

theorem sGlobal5_hz114 {c : ℝ} (hc : B (37 / 100) (3 / 8) c) : B 0 (2238192838068025124731 / 1000000000000000000) |(s3U 12225 46 maskSlack c)| := bweaken (babs (sGlobal5_hz107 hc)) (by norm_num) (by norm_num)

theorem sGlobal5_hz115 {c : ℝ} (hc : B (37 / 100) (3 / 8) c) : B 0 (4814015572358580787 / 125000000000000000) |(s3L 12225 46 maskSlack c)| := bweaken (babs (sGlobal5_hz113 hc)) (by norm_num) (by norm_num)

theorem sGlobal5_hz116 {c : ℝ} (hc : B (37 / 100) (3 / 8) c) : B 0 (2238192838068025124731 / 1000000000000000000) (max |(s3U 12225 46 maskSlack c)| |(s3L 12225 46 maskSlack c)|) := bweaken (bmax (sGlobal5_hz114 hc) (sGlobal5_hz115 hc)) (by norm_num) (by norm_num)

theorem sGlobal5_hz117 {c : ℝ} (hc : B (37 / 100) (3 / 8) c) : B 0 (2238192838068025124731 / 1000000000000000000) (s3nks 12225 46 maskSlack c) := by
    convert (sGlobal5_hz116 hc) using 1 <;>
      norm_num [s3nks] <;> ring

theorem sGlobal5 {c : ℝ} (hc : B (37 / 100) (3 / 8) c) :
    0 < s3am 12225 46 ∧ 0 ≤ s3dm 12225 46 c ∧
    s3dm 12225 46 c ^ 2 ≤ 2 * s3ap 12225 46 ^ 2 ∧ s3c1 12225 46 c < 1 ∧
    0 ≤ s3Cpa 12225 c - s3r1 12225 46 ∧
    s3e0 12225 46 ≤ (s3Cpa 12225 c - s3r1 12225 46) / s3ap 12225 46 ∧
    s3nks 12225 46 maskSlack c ≤ 12225 * (45771 / 250000) := by

  refine ⟨lt_of_lt_of_le (by norm_num) sGlobal5_hz14.1,
    le_trans (by norm_num) (sGlobal5_hz64 hc).1, ?_,
    lt_of_le_of_lt (sGlobal5_hz72 hc).2 (by norm_num), ?_, ?_,
    le_trans (sGlobal5_hz117 hc).2 (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (sGlobal5_hz64 hc).1) (sGlobal5_hz64 hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) sGlobal5_hz9.1 2
    nlinarith only [h1, h2]
  · linarith only [(sGlobal5_hz84 hc).1, sGlobal5_hz33.2]
  · have hap : 0 < s3ap 12225 46 := lt_of_lt_of_le (by norm_num) sGlobal5_hz9.1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul sGlobal5_hz16.2 sGlobal5_hz9.2 (le_trans (by norm_num) sGlobal5_hz9.1) (by norm_num)
    linarith only [h, (sGlobal5_hz84 hc).1, sGlobal5_hz33.2]

end BstLean.Part255
