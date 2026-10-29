import BstLean.Part255SGlobal0
import BstLean.Part255Numeric10
namespace BstLean.Part255
open Real BstLean.Part130 BstLean.Part182 BstLean.Part197 BstLean.Part246
theorem sGlobal4_hz0 : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal4_hz1 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) ((√(23 : ℝ)) / (12225 : ℝ)) := bdiv sGlobal4_hz0 (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal4_hz2 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) maskSlack := by
    convert sGlobal4_hz1 using 1 <;>
      norm_num [maskSlack] <;> ring

theorem sGlobal4_hz3 : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal4_hz4 : B (6395294793910793 / 500000000000000000) (12790589587821587 / 1000000000000000000) (√((2 / 12225) : ℝ)) := bsqrt (bpoint ((2 / 12225) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal4_hz5 : B (7230130686979 / 62500000000000000) (23136418198333 / 200000000000000000) (√((2 / 149450625) : ℝ)) := bsqrt (bpoint ((2 / 149450625) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal4_hz6 : B (2211334438749598093 / 20000000000000000) (110566721937479904651 / 1000000000000000000) (√(12225 : ℝ)) := bsqrt (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal4_hz7 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))) := bmul sGlobal4_hz3 sGlobal4_hz4 (by norm_num) (by norm_num)

theorem sGlobal4_hz8 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) ((√(12225 : ℝ)) + ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := badd sGlobal4_hz6 sGlobal4_hz7 (by norm_num) (by norm_num)

theorem sGlobal4_hz9 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) (s3ap 12225 46) := by
    convert sGlobal4_hz8 using 1 <;>
      norm_num [s3ap, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal4_hz10 : B (163599182004089 / 1000000000000000000) (16359918200409 / 100000000000000000) ((2 : ℝ) / (12225 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal4_hz11 : B (1222499983640081799591 / 100000000000000000) (12224999836400817995911 / 1000000000000000000) ((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ))) := bsub (bpoint (12225 : ℝ)) sGlobal4_hz10 (by norm_num) (by norm_num)

theorem sGlobal4_hz12 : B (110566721197658827907 / 1000000000000000000) (27641680299414706977 / 250000000000000000) (√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) := bsqrt sGlobal4_hz11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal4_hz13 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) ((√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) - ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bsub sGlobal4_hz12 sGlobal4_hz7 (by norm_num) (by norm_num)

theorem sGlobal4_hz14 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) (s3am 12225 46) := by
    convert sGlobal4_hz13 using 1 <;>
      norm_num [s3am, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal4_hz15 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√((2 / 12225) : ℝ)) * (√(92 : ℝ))) := bmul sGlobal4_hz4 sGlobal4_hz3 (by norm_num) (by norm_num)

theorem sGlobal4_hz16 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) (s3e0 12225 46) := by
    convert sGlobal4_hz15 using 1 <;>
      norm_num [s3e0, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal4_hz17 : B (250196148528560847 / 500000000000000000) (100078459411424339 / 200000000000000000) (((1 / 2) : ℝ) + maskSlack) := badd (bpoint ((1 / 2) : ℝ)) sGlobal4_hz2 (by norm_num) (by norm_num)

theorem sGlobal4_hz18 : B (59827153232297998295487 / 800000000000000) (23930861292919199366019 / 320000000000000) ((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack)) := bmul (bpoint (149450625 : ℝ)) sGlobal4_hz17 (by norm_num) (by norm_num)

theorem sGlobal4_hz19 : B (1729554180017180009583 / 200000000000000000) (8647770900085900056557 / 1000000000000000000) (√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) := bsqrt sGlobal4_hz18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal4_hz20 : B (4328681281566262743499 / 500000000000000000) (8657362563132525495641 / 1000000000000000000) ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))) := badd sGlobal4_hz19 sGlobal4_hz3 (by norm_num) (by norm_num)

theorem sGlobal4_hz21 : B (110732771457999278473 / 1000000000000000000) (55366385728999643621 / 500000000000000000) ((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ)))) := bmul sGlobal4_hz4 sGlobal4_hz20 (by norm_num) (by norm_num)

theorem sGlobal4_hz22 : B (209099159 / 15625000000000000) (13382346177 / 1000000000000000000) ((2 : ℝ) / (149450625 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (149450625 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal4_hz23 : B (2452349334953899930479 / 200000000000000000) (12261746674769501594427 / 1000000000000000000) (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2) := bsq sGlobal4_hz21 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal4_hz24 : B (82045469362091 / 500000000000000000) (32818187747289 / 200000000000000000) (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2)) := bmul sGlobal4_hz22 sGlobal4_hz23 (by norm_num) (by norm_num)

theorem sGlobal4_hz25 : B (82045469362091 / 250000000000000000) (32818187747289 / 100000000000000000) ((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) := bmul (bpoint (2 : ℝ)) sGlobal4_hz24 (by norm_num) (by norm_num)

theorem sGlobal4_hz26 : B (117258080744995992792057 / 1000000000000000000) (58629040372497996396029 / 500000000000000000) (√(13749457500 : ℝ)) := bsqrt (bpoint (13749457500 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal4_hz27 : B (117304080744995992792057 / 1000000000000000000) (58652040372497996396029 / 500000000000000000) ((√(13749457500 : ℝ)) + (46 : ℝ)) := badd sGlobal4_hz26 (bpoint (46 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal4_hz28 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal4_hz25 sGlobal4_hz27 (by norm_num) (by norm_num)

theorem sGlobal4_hz29 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (s3rs 12225 46 maskSlack) := by
    convert sGlobal4_hz28 using 1 <;>
      norm_num [s3rs, s3pp, s3K, mA, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal4_hz30 : B (490797546012267 / 1000000000000000000) (49079754601227 / 100000000000000000) ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (3 : ℝ)) sGlobal4_hz10 (by norm_num) (by norm_num)

theorem sGlobal4_hz31 : B (490797546012267 / 500000000000000000) (49079754601227 / 50000000000000000) ((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal4_hz30 (by norm_num) (by norm_num)

theorem sGlobal4_hz32 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal4_hz31 sGlobal4_hz27 (by norm_num) (by norm_num)

theorem sGlobal4_hz33 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (s3r1 12225 46) := by
    convert sGlobal4_hz32 using 1 <;>
      norm_num [s3r1, mA] <;> ring

theorem sGlobal4_hz34 : B (163599182004089 / 500000000000000000) (16359918200409 / 50000000000000000) ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (2 : ℝ)) sGlobal4_hz10 (by norm_num) (by norm_num)

theorem sGlobal4_hz35 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal4_hz34 (by norm_num) (by norm_num)

theorem sGlobal4_hz36 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal4_hz35 sGlobal4_hz27 (by norm_num) (by norm_num)

theorem sGlobal4_hz37 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (s3rpp 12225 46) := by
    convert sGlobal4_hz36 using 1 <;>
      norm_num [s3rpp, mA] <;> ring

theorem sGlobal4_hz38 {c : ℝ} (hc : B (73 / 200) (37 / 100) c) : B (73 / 200) (37 / 100) c := hc

theorem sGlobal4_hz39 : B (618931014992546163 / 1000000000000000000) (309465507589790037 / 500000000000000000) (kdot ((73 / 200))) := by
    constructor
    · apply bkdot_lower (q := (682056790305224659 / 1000000000000000000)) (a := (598581761905168017 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (341028395152612329 / 500000000000000000)) (a := (299290880805687919 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal4_hz40 : B (5329 / 40000) (5329 / 40000) (((73 / 200) : ℝ)^2) := bsq (bpoint ((73 / 200) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal4_hz41 : B (34671 / 40000) (34671 / 40000) ((1 : ℝ) - (((73 / 200) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal4_hz40 (by norm_num) (by norm_num)

theorem sGlobal4_hz42 : B (465503759383315829 / 500000000000000000) (931007518766631659 / 1000000000000000000) (√((1 : ℝ) - (((73 / 200) : ℝ)^2))) := bsqrt sGlobal4_hz41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal4_hz43 : B (7408722433371497 / 25000000000000000) (148174448667429941 / 500000000000000000) ((√((1 : ℝ) - (((73 / 200) : ℝ)^2))) / Real.pi) := bdiv sGlobal4_hz42 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal4_hz44 : B (225909820472279349 / 1000000000000000000) (28238727567568341 / 125000000000000000) (((73 / 200) : ℝ) * (kdot ((73 / 200)))) := bmul (bpoint ((73 / 200) : ℝ)) sGlobal4_hz39 (by norm_num) (by norm_num)

theorem sGlobal4_hz45 : B (522258717807139229 / 1000000000000000000) (52225871787540661 / 100000000000000000) (((√((1 : ℝ) - (((73 / 200) : ℝ)^2))) / Real.pi) + (((73 / 200) : ℝ) * (kdot ((73 / 200))))) := badd sGlobal4_hz43 sGlobal4_hz44 (by norm_num) (by norm_num)

theorem sGlobal4_hz46 : B (522258717807139229 / 1000000000000000000) (52225871787540661 / 100000000000000000) (kappa ((73 / 200))) := by rw [kappa_eq]; exact sGlobal4_hz45

theorem sGlobal4_hz47 : B (77580289777347187 / 125000000000000000) (620642318359675101 / 1000000000000000000) (kdot ((37 / 100))) := by
    constructor
    · apply bkdot_lower (q := (678125367906657911 / 1000000000000000000)) (a := (595893653083371583 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (67812536790665791 / 100000000000000000)) (a := (18621676651939067 / 31250000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal4_hz48 : B (1369 / 10000) (1369 / 10000) (((37 / 100) : ℝ)^2) := bsq (bpoint ((37 / 100) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal4_hz49 : B (8631 / 10000) (8631 / 10000) ((1 : ℝ) - (((37 / 100) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal4_hz48 (by norm_num) (by norm_num)

theorem sGlobal4_hz50 : B (116128969254015167 / 125000000000000000) (929031754032121337 / 1000000000000000000) (√((1 : ℝ) - (((37 / 100) : ℝ)^2))) := bsqrt sGlobal4_hz49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal4_hz51 : B (18482499492943247 / 62500000000000000) (147859995943545977 / 500000000000000000) ((√((1 : ℝ) - (((37 / 100) : ℝ)^2))) / Real.pi) := bdiv sGlobal4_hz50 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal4_hz52 : B (229637657740947673 / 1000000000000000000) (57409414448269947 / 250000000000000000) (((37 / 100) : ℝ) * (kdot ((37 / 100)))) := bmul (bpoint ((37 / 100) : ℝ)) sGlobal4_hz47 (by norm_num) (by norm_num)

theorem sGlobal4_hz53 : B (4202861197024317 / 8000000000000000) (262678824840085871 / 500000000000000000) (((√((1 : ℝ) - (((37 / 100) : ℝ)^2))) / Real.pi) + (((37 / 100) : ℝ) * (kdot ((37 / 100))))) := badd sGlobal4_hz51 sGlobal4_hz52 (by norm_num) (by norm_num)

theorem sGlobal4_hz54 : B (4202861197024317 / 8000000000000000) (262678824840085871 / 500000000000000000) (kappa ((37 / 100))) := by rw [kappa_eq]; exact sGlobal4_hz53

theorem sGlobal4_hz55 {c : ℝ} (hc : B (73 / 200) (37 / 100) c) : B (522258717807139229 / 1000000000000000000) (262678824840085871 / 500000000000000000) (kappa c) := bkappa (sGlobal4_hz38 hc) (by norm_num) (by norm_num) sGlobal4_hz46.1 sGlobal4_hz54.2

theorem sGlobal4_hz56 : B 24450 24450 ((2 : ℝ) * (12225 : ℝ)) := bmul (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal4_hz57 {c : ℝ} (hc : B (73 / 200) (37 / 100) c) : B (237321175159914129 / 500000000000000000) (477741282192860771 / 1000000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (sGlobal4_hz55 hc) (by norm_num) (by norm_num)

theorem sGlobal4_hz58 {c : ℝ} (hc : B (73 / 200) (37 / 100) c) : B (116050054653198009081 / 10000000000000000) (233615486992308917019 / 20000000000000000) (((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) := bmul sGlobal4_hz56 (sGlobal4_hz57 hc) (by norm_num) (by norm_num)

theorem sGlobal4_hz59 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (4 : ℝ)) sGlobal4_hz10 (by norm_num) (by norm_num)

theorem sGlobal4_hz60 {c : ℝ} (hc : B (73 / 200) (37 / 100) c) : B (580250240546153644587 / 50000000000000000) (5840386847609358917297 / 500000000000000000) ((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bsub (sGlobal4_hz58 hc) sGlobal4_hz59 (by norm_num) (by norm_num)

theorem sGlobal4_hz61 {c : ℝ} (hc : B (73 / 200) (37 / 100) c) : B (53863263944276234539 / 500000000000000000) (54038814048836040853 / 500000000000000000) (√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) := bsqrt (sGlobal4_hz60 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal4_hz62 : B (30670756373515103 / 125000000000000000) (122683025494060423 / 500000000000000000) ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal4_hz7 (by norm_num) (by norm_num)

theorem sGlobal4_hz63 {c : ℝ} (hc : B (73 / 200) (37 / 100) c) : B (13435145229695543529 / 125000000000000000) (53916131023341980441 / 500000000000000000) ((√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) - ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))))) := bsub (sGlobal4_hz61 hc) sGlobal4_hz62 (by norm_num) (by norm_num)

theorem sGlobal4_hz64 {c : ℝ} (hc : B (73 / 200) (37 / 100) c) : B (13435145229695543529 / 125000000000000000) (53916131023341980441 / 500000000000000000) (s3dm 12225 46 c) := by
    convert (sGlobal4_hz63 hc) using 1 <;>
      norm_num [s3dm, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal4_hz65 : B (6126072185528622723889 / 500000000000000000) (2450428874211449090087 / 200000000000000000) ((s3ap 12225 46)^2) := bsq sGlobal4_hz9 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal4_hz66 : B (6126072185528622723889 / 250000000000000000) (2450428874211449090087 / 100000000000000000) ((2 : ℝ) * ((s3ap 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal4_hz65 (by norm_num) (by norm_num)

theorem sGlobal4_hz67 {c : ℝ} (hc : B (73 / 200) (37 / 100) c) : B (11552200149952698821881 / 1000000000000000000) (11627796738104718204231 / 1000000000000000000) ((s3dm 12225 46 c)^2) := bsq (sGlobal4_hz64 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal4_hz68 {c : ℝ} (hc : B (73 / 200) (37 / 100) c) : B (515059680160390907653 / 40000000000000000) (12952088592161792078989 / 1000000000000000000) (((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) := bsub sGlobal4_hz66 (sGlobal4_hz67 hc) (by norm_num) (by norm_num)

theorem sGlobal4_hz69 : B (1524735695971823534271 / 125000000000000000) (609894278388729413841 / 50000000000000000) ((s3am 12225 46)^2) := bsq sGlobal4_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal4_hz70 : B (1524735695971823534271 / 62500000000000000) (609894278388729413841 / 25000000000000000) ((2 : ℝ) * ((s3am 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal4_hz69 (by norm_num) (by norm_num)

theorem sGlobal4_hz71 {c : ℝ} (hc : B (73 / 200) (37 / 100) c) : B (263908280096264893 / 500000000000000000) (265457659038459123 / 500000000000000000) ((((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) / ((2 : ℝ) * ((s3am 12225 46)^2))) := bdiv (sGlobal4_hz68 hc) sGlobal4_hz70 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal4_hz72 {c : ℝ} (hc : B (73 / 200) (37 / 100) c) : B (263908280096264893 / 500000000000000000) (265457659038459123 / 500000000000000000) (s3c1 12225 46 c) := by
    convert (sGlobal4_hz71 hc) using 1 <;>
      norm_num [s3c1] <;> ring

theorem sGlobal4_hz73 {c : ℝ} (hc : B (73 / 200) (37 / 100) c) : B (618931014992546163 / 1000000000000000000) (620642318359675101 / 1000000000000000000) (kdot c) := bkdot (sGlobal4_hz38 hc) sGlobal4_hz39.1 sGlobal4_hz47.2

theorem sGlobal4_hz74 : B (8462364372231641 / 12500000000000000) (676989149778539613 / 1000000000000000000) (kdot ((263908280096264893 / 500000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (138982390713216869 / 250000000000000000)) (a := (507384257042779583 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (22237182514114699 / 40000000000000000)) (a := (15855758032586453 / 31250000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal4_hz75 : B (339075889067513037 / 500000000000000000) (678151778135032823 / 1000000000000000000) (kdot ((265457659038459123 / 500000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (276770657621851439 / 500000000000000000)) (a := (505558004690969973 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (553541315243702877 / 1000000000000000000)) (a := (252779002345479687 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal4_hz76 {c : ℝ} (hc : B (73 / 200) (37 / 100) c) : B (8462364372231641 / 12500000000000000) (678151778135032823 / 1000000000000000000) (kdot (s3c1 12225 46 c)) := bkdot (sGlobal4_hz72 hc) sGlobal4_hz74.1 sGlobal4_hz75.2

theorem sGlobal4_hz77 {c : ℝ} (hc : B (73 / 200) (37 / 100) c) : B (5329 / 40000) (1369 / 10000) (c^2) := bsq (sGlobal4_hz38 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal4_hz78 {c : ℝ} (hc : B (73 / 200) (37 / 100) c) : B (8631 / 10000) (34671 / 40000) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (sGlobal4_hz77 hc) (by norm_num) (by norm_num)

theorem sGlobal4_hz79 {c : ℝ} (hc : B (73 / 200) (37 / 100) c) : B (116128969254015167 / 125000000000000000) (931007518766631659 / 1000000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (sGlobal4_hz78 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal4_hz80 : B (39119999999999765769 / 1600000000000000) (3912000000000000489 / 160000000000000) ((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (149450625 : ℝ)) sGlobal4_hz10 (by norm_num) (by norm_num)

theorem sGlobal4_hz81 {c : ℝ} (hc : B (73 / 200) (37 / 100) c) : B (575006566483406349 / 1000000000000000000) (288911332428805499 / 500000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (sGlobal4_hz79 hc) (sGlobal4_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal4_hz82 {c : ℝ} (hc : B (73 / 200) (37 / 100) c) : B (14058910550519201055323 / 1000000000000000000) (14127764155768590667071 / 1000000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) := bmul sGlobal4_hz80 (sGlobal4_hz81 hc) (by norm_num) (by norm_num)

theorem sGlobal4_hz83 {c : ℝ} (hc : B (73 / 200) (37 / 100) c) : B (7029455275259600527661 / 1000000000000000000) (220746314933884229173 / 31250000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) / (2 : ℝ)) := bdiv (sGlobal4_hz82 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal4_hz84 {c : ℝ} (hc : B (73 / 200) (37 / 100) c) : B (7029455275259600527661 / 1000000000000000000) (220746314933884229173 / 31250000000000000) (s3Cpa 12225 c) := by
    convert (sGlobal4_hz83 hc) using 1 <;>
      norm_num [s3Cpa, mA] <;> ring

theorem sGlobal4_hz85 {c : ℝ} (hc : B (73 / 200) (37 / 100) c) : B (18482499492943247 / 62500000000000000) (148174448667429941 / 500000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (sGlobal4_hz79 hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal4_hz86 {c : ℝ} (hc : B (73 / 200) (37 / 100) c) : B (225909820472279349 / 1000000000000000000) (57409414448269947 / 250000000000000000) (c * (kdot c)) := bmul (sGlobal4_hz38 hc) (sGlobal4_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal4_hz87 {c : ℝ} (hc : B (73 / 200) (37 / 100) c) : B (16520583523503041 / 250000000000000000) (70439076862580533 / 1000000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (sGlobal4_hz85 hc) (sGlobal4_hz86 hc) (by norm_num) (by norm_num)

theorem sGlobal4_hz88 {c : ℝ} (hc : B (73 / 200) (37 / 100) c) : B (807856534299293867859 / 500000000000000000) (172223542929009424713 / 100000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) := bmul sGlobal4_hz80 (sGlobal4_hz87 hc) (by norm_num) (by norm_num)

theorem sGlobal4_hz89 {c : ℝ} (hc : B (73 / 200) (37 / 100) c) : B (807856534299293867859 / 1000000000000000000) (172223542929009424713 / 200000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) / (2 : ℝ)) := bdiv (sGlobal4_hz88 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal4_hz90 {c : ℝ} (hc : B (73 / 200) (37 / 100) c) : B (807856534299293867859 / 1000000000000000000) (172223542929009424713 / 200000000000000000) (s3Cpp 12225 c) := by
    convert (sGlobal4_hz89 hc) using 1 <;>
      norm_num [s3Cpp, mA] <;> ring

theorem sGlobal4_hz91 {c : ℝ} (hc : B (73 / 200) (37 / 100) c) : B (3572300192596669118031 / 500000000000000000) (3589513593909016872881 / 500000000000000000) ((s3Cpa 12225 c) + (s3r1 12225 46)) := badd (sGlobal4_hz84 hc) sGlobal4_hz33 (by norm_num) (by norm_num)

theorem sGlobal4_hz92 {c : ℝ} (hc : B (73 / 200) (37 / 100) c) : B (32344889336878635003 / 500000000000000000) (65001491312976686961 / 1000000000000000000) (((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) := bdiv (sGlobal4_hz91 hc) sGlobal4_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal4_hz93 {c : ℝ} (hc : B (73 / 200) (37 / 100) c) : B (32406230849625665209 / 500000000000000000) (8140521792308843423 / 125000000000000000) ((((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) + (s3e0 12225 46)) := badd (sGlobal4_hz92 hc) sGlobal4_hz16 (by norm_num) (by norm_num)

theorem sGlobal4_hz94 {c : ℝ} (hc : B (73 / 200) (37 / 100) c) : B (32406230849625665209 / 500000000000000000) (8140521792308843423 / 125000000000000000) (s3Lam 12225 46 c) := by
    convert (sGlobal4_hz93 hc) using 1 <;>
      norm_num [s3Lam] <;> ring

theorem sGlobal4_hz95 {c : ℝ} (hc : B (73 / 200) (37 / 100) c) : B (884619940921785673459 / 1000000000000000000) (937881121267539398383 / 1000000000000000000) ((s3Cpp 12225 c) + (s3rpp 12225 46)) := badd (sGlobal4_hz90 hc) sGlobal4_hz37 (by norm_num) (by norm_num)

theorem sGlobal4_hz96 {c : ℝ} (hc : B (73 / 200) (37 / 100) c) : B (442309970460892836729 / 1000000000000000000) (318012875033430096071 / 500000000000000000) (if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) := bweaken (bfirst (sGlobal4_hz95 hc) (sGlobal4_hz76 hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem sGlobal4_hz97 {c : ℝ} (hc : B (73 / 200) (37 / 100) c) : B (4200655191516920652781 / 1000000000000000000) (2120579041633765903827 / 500000000000000000) ((s3Lam 12225 46 c)^2) := bsq (sGlobal4_hz94 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal4_hz98 {c : ℝ} (hc : B (73 / 200) (37 / 100) c) : B (139295160606737209 / 500000000000000000) (11274842998748611 / 40000000000000000) ((s3c1 12225 46 c)^2) := bsq (sGlobal4_hz72 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal4_hz99 {c : ℝ} (hc : B (73 / 200) (37 / 100) c) : B (28725157001251389 / 40000000000000000) (360704839393262791 / 500000000000000000) ((1 : ℝ) - ((s3c1 12225 46 c)^2)) := bsub (bpoint (1 : ℝ)) (sGlobal4_hz98 hc) (by norm_num) (by norm_num)

theorem sGlobal4_hz100 {c : ℝ} (hc : B (73 / 200) (37 / 100) c) : B (105928109836878633 / 125000000000000000) (849358392427204773 / 1000000000000000000) (√((1 : ℝ) - ((s3c1 12225 46 c)^2))) := bsqrt (sGlobal4_hz99 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal4_hz101 {c : ℝ} (hc : B (73 / 200) (37 / 100) c) : B (1331131886688762499 / 500000000000000000) (266833808591414319 / 100000000000000000) (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))) := bmul pi_mem (sGlobal4_hz100 hc) (by norm_num) (by norm_num)

theorem sGlobal4_hz102 {c : ℝ} (hc : B (73 / 200) (37 / 100) c) : B (1574258979284411977941 / 1000000000000000000) (796532283104111132433 / 500000000000000000) (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2))))) := bdiv (sGlobal4_hz97 hc) (sGlobal4_hz101 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal4_hz103 {c : ℝ} (hc : B (73 / 200) (37 / 100) c) : B (201656894974530481467 / 100000000000000000) (139318144767192653563 / 62500000000000000) ((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) := badd (sGlobal4_hz96 hc) (sGlobal4_hz102 hc) (by norm_num) (by norm_num)

theorem sGlobal4_hz104 : B (3762781186094069 / 250000000000000000) (376278118609407 / 25000000000000000) ((s3e0 12225 46)^2) := bsq sGlobal4_hz16 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal4_hz105 {c : ℝ} (hc : B (73 / 200) (37 / 100) c) : B (1008292000435024595473 / 500000000000000000) (278638170924978354161 / 125000000000000000) (((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) := badd (sGlobal4_hz103 hc) sGlobal4_hz104 (by norm_num) (by norm_num)

theorem sGlobal4_hz106 {c : ℝ} (hc : B (73 / 200) (37 / 100) c) : B (2055081074321296461077 / 1000000000000000000) (283450305106743887913 / 125000000000000000) ((((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) + (s3rs 12225 46 maskSlack)) := badd (sGlobal4_hz105 hc) sGlobal4_hz29 (by norm_num) (by norm_num)

theorem sGlobal4_hz107 {c : ℝ} (hc : B (73 / 200) (37 / 100) c) : B (2055081074321296461077 / 1000000000000000000) (283450305106743887913 / 125000000000000000) (s3U 12225 46 maskSlack c) := by
    convert (sGlobal4_hz106 hc) using 1 <;>
      norm_num [s3U] <;> ring

theorem sGlobal4_hz108 {c : ℝ} (hc : B (73 / 200) (37 / 100) c) : B (731093127676801593041 / 1000000000000000000) (156870861604511063593 / 200000000000000000) ((s3Cpp 12225 c) - (s3rpp 12225 46)) := bsub (sGlobal4_hz90 hc) sGlobal4_hz37 (by norm_num) (by norm_num)

theorem sGlobal4_hz109 {c : ℝ} (hc : B (73 / 200) (37 / 100) c) : B 0 0 (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ)) := bweaken (bmin (sGlobal4_hz108 hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem sGlobal4_hz110 {c : ℝ} (hc : B (73 / 200) (37 / 100) c) : B 0 0 ((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) := bmul (sGlobal4_hz76 hc) (sGlobal4_hz109 hc) (by norm_num) (by norm_num)

theorem sGlobal4_hz111 {c : ℝ} (hc : B (73 / 200) (37 / 100) c) : B (-376278118609407 / 25000000000000000) (-3762781186094069 / 250000000000000000) (((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) := bsub (sGlobal4_hz110 hc) sGlobal4_hz104 (by norm_num) (by norm_num)

theorem sGlobal4_hz112 {c : ℝ} (hc : B (73 / 200) (37 / 100) c) : B (-4814015572358580787 / 125000000000000000) (-38512124575991646407 / 1000000000000000000) ((((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) - (s3rs 12225 46 maskSlack)) := bsub (sGlobal4_hz111 hc) sGlobal4_hz29 (by norm_num) (by norm_num)

theorem sGlobal4_hz113 {c : ℝ} (hc : B (73 / 200) (37 / 100) c) : B (-4814015572358580787 / 125000000000000000) (-38512124575991646407 / 1000000000000000000) (s3L 12225 46 maskSlack c) := by
    convert (sGlobal4_hz112 hc) using 1 <;>
      norm_num [s3L] <;> ring

theorem sGlobal4_hz114 {c : ℝ} (hc : B (73 / 200) (37 / 100) c) : B 0 (283450305106743887913 / 125000000000000000) |(s3U 12225 46 maskSlack c)| := bweaken (babs (sGlobal4_hz107 hc)) (by norm_num) (by norm_num)

theorem sGlobal4_hz115 {c : ℝ} (hc : B (73 / 200) (37 / 100) c) : B 0 (4814015572358580787 / 125000000000000000) |(s3L 12225 46 maskSlack c)| := bweaken (babs (sGlobal4_hz113 hc)) (by norm_num) (by norm_num)

theorem sGlobal4_hz116 {c : ℝ} (hc : B (73 / 200) (37 / 100) c) : B 0 (283450305106743887913 / 125000000000000000) (max |(s3U 12225 46 maskSlack c)| |(s3L 12225 46 maskSlack c)|) := bweaken (bmax (sGlobal4_hz114 hc) (sGlobal4_hz115 hc)) (by norm_num) (by norm_num)

theorem sGlobal4_hz117 {c : ℝ} (hc : B (73 / 200) (37 / 100) c) : B 0 (283450305106743887913 / 125000000000000000) (s3nks 12225 46 maskSlack c) := by
    convert (sGlobal4_hz116 hc) using 1 <;>
      norm_num [s3nks] <;> ring

theorem sGlobal4 {c : ℝ} (hc : B (73 / 200) (37 / 100) c) :
    0 < s3am 12225 46 ∧ 0 ≤ s3dm 12225 46 c ∧
    s3dm 12225 46 c ^ 2 ≤ 2 * s3ap 12225 46 ^ 2 ∧ s3c1 12225 46 c < 1 ∧
    0 ≤ s3Cpa 12225 c - s3r1 12225 46 ∧
    s3e0 12225 46 ≤ (s3Cpa 12225 c - s3r1 12225 46) / s3ap 12225 46 ∧
    s3nks 12225 46 maskSlack c ≤ 12225 * (185489 / 1000000) := by

  refine ⟨lt_of_lt_of_le (by norm_num) sGlobal4_hz14.1,
    le_trans (by norm_num) (sGlobal4_hz64 hc).1, ?_,
    lt_of_le_of_lt (sGlobal4_hz72 hc).2 (by norm_num), ?_, ?_,
    le_trans (sGlobal4_hz117 hc).2 (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (sGlobal4_hz64 hc).1) (sGlobal4_hz64 hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) sGlobal4_hz9.1 2
    nlinarith only [h1, h2]
  · linarith only [(sGlobal4_hz84 hc).1, sGlobal4_hz33.2]
  · have hap : 0 < s3ap 12225 46 := lt_of_lt_of_le (by norm_num) sGlobal4_hz9.1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul sGlobal4_hz16.2 sGlobal4_hz9.2 (le_trans (by norm_num) sGlobal4_hz9.1) (by norm_num)
    linarith only [h, (sGlobal4_hz84 hc).1, sGlobal4_hz33.2]

end BstLean.Part255
