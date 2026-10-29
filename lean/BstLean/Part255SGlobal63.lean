import BstLean.Part255SGlobal59
import BstLean.Part255Numeric10
namespace BstLean.Part255
open Real BstLean.Part130 BstLean.Part182 BstLean.Part197 BstLean.Part246
theorem sGlobal63_hz0 : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal63_hz1 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) ((√(23 : ℝ)) / (12225 : ℝ)) := bdiv sGlobal63_hz0 (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal63_hz2 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) maskSlack := by
    convert sGlobal63_hz1 using 1 <;>
      norm_num [maskSlack] <;> ring

theorem sGlobal63_hz3 : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal63_hz4 : B (6395294793910793 / 500000000000000000) (12790589587821587 / 1000000000000000000) (√((2 / 12225) : ℝ)) := bsqrt (bpoint ((2 / 12225) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal63_hz5 : B (7230130686979 / 62500000000000000) (23136418198333 / 200000000000000000) (√((2 / 149450625) : ℝ)) := bsqrt (bpoint ((2 / 149450625) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal63_hz6 : B (2211334438749598093 / 20000000000000000) (110566721937479904651 / 1000000000000000000) (√(12225 : ℝ)) := bsqrt (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal63_hz7 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))) := bmul sGlobal63_hz3 sGlobal63_hz4 (by norm_num) (by norm_num)

theorem sGlobal63_hz8 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) ((√(12225 : ℝ)) + ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := badd sGlobal63_hz6 sGlobal63_hz7 (by norm_num) (by norm_num)

theorem sGlobal63_hz9 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) (s3ap 12225 46) := by
    convert sGlobal63_hz8 using 1 <;>
      norm_num [s3ap, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal63_hz10 : B (163599182004089 / 1000000000000000000) (16359918200409 / 100000000000000000) ((2 : ℝ) / (12225 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal63_hz11 : B (1222499983640081799591 / 100000000000000000) (12224999836400817995911 / 1000000000000000000) ((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ))) := bsub (bpoint (12225 : ℝ)) sGlobal63_hz10 (by norm_num) (by norm_num)

theorem sGlobal63_hz12 : B (110566721197658827907 / 1000000000000000000) (27641680299414706977 / 250000000000000000) (√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) := bsqrt sGlobal63_hz11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal63_hz13 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) ((√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) - ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bsub sGlobal63_hz12 sGlobal63_hz7 (by norm_num) (by norm_num)

theorem sGlobal63_hz14 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) (s3am 12225 46) := by
    convert sGlobal63_hz13 using 1 <;>
      norm_num [s3am, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal63_hz15 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√((2 / 12225) : ℝ)) * (√(92 : ℝ))) := bmul sGlobal63_hz4 sGlobal63_hz3 (by norm_num) (by norm_num)

theorem sGlobal63_hz16 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) (s3e0 12225 46) := by
    convert sGlobal63_hz15 using 1 <;>
      norm_num [s3e0, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal63_hz17 : B (250196148528560847 / 500000000000000000) (100078459411424339 / 200000000000000000) (((1 / 2) : ℝ) + maskSlack) := badd (bpoint ((1 / 2) : ℝ)) sGlobal63_hz2 (by norm_num) (by norm_num)

theorem sGlobal63_hz18 : B (59827153232297998295487 / 800000000000000) (23930861292919199366019 / 320000000000000) ((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack)) := bmul (bpoint (149450625 : ℝ)) sGlobal63_hz17 (by norm_num) (by norm_num)

theorem sGlobal63_hz19 : B (1729554180017180009583 / 200000000000000000) (8647770900085900056557 / 1000000000000000000) (√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) := bsqrt sGlobal63_hz18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal63_hz20 : B (4328681281566262743499 / 500000000000000000) (8657362563132525495641 / 1000000000000000000) ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))) := badd sGlobal63_hz19 sGlobal63_hz3 (by norm_num) (by norm_num)

theorem sGlobal63_hz21 : B (110732771457999278473 / 1000000000000000000) (55366385728999643621 / 500000000000000000) ((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ)))) := bmul sGlobal63_hz4 sGlobal63_hz20 (by norm_num) (by norm_num)

theorem sGlobal63_hz22 : B (209099159 / 15625000000000000) (13382346177 / 1000000000000000000) ((2 : ℝ) / (149450625 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (149450625 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal63_hz23 : B (2452349334953899930479 / 200000000000000000) (12261746674769501594427 / 1000000000000000000) (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2) := bsq sGlobal63_hz21 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal63_hz24 : B (82045469362091 / 500000000000000000) (32818187747289 / 200000000000000000) (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2)) := bmul sGlobal63_hz22 sGlobal63_hz23 (by norm_num) (by norm_num)

theorem sGlobal63_hz25 : B (82045469362091 / 250000000000000000) (32818187747289 / 100000000000000000) ((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) := bmul (bpoint (2 : ℝ)) sGlobal63_hz24 (by norm_num) (by norm_num)

theorem sGlobal63_hz26 : B (117258080744995992792057 / 1000000000000000000) (58629040372497996396029 / 500000000000000000) (√(13749457500 : ℝ)) := bsqrt (bpoint (13749457500 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal63_hz27 : B (117304080744995992792057 / 1000000000000000000) (58652040372497996396029 / 500000000000000000) ((√(13749457500 : ℝ)) + (46 : ℝ)) := badd sGlobal63_hz26 (bpoint (46 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal63_hz28 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal63_hz25 sGlobal63_hz27 (by norm_num) (by norm_num)

theorem sGlobal63_hz29 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (s3rs 12225 46 maskSlack) := by
    convert sGlobal63_hz28 using 1 <;>
      norm_num [s3rs, s3pp, s3K, mA, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal63_hz30 : B (490797546012267 / 1000000000000000000) (49079754601227 / 100000000000000000) ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (3 : ℝ)) sGlobal63_hz10 (by norm_num) (by norm_num)

theorem sGlobal63_hz31 : B (490797546012267 / 500000000000000000) (49079754601227 / 50000000000000000) ((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal63_hz30 (by norm_num) (by norm_num)

theorem sGlobal63_hz32 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal63_hz31 sGlobal63_hz27 (by norm_num) (by norm_num)

theorem sGlobal63_hz33 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (s3r1 12225 46) := by
    convert sGlobal63_hz32 using 1 <;>
      norm_num [s3r1, mA] <;> ring

theorem sGlobal63_hz34 : B (163599182004089 / 500000000000000000) (16359918200409 / 50000000000000000) ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (2 : ℝ)) sGlobal63_hz10 (by norm_num) (by norm_num)

theorem sGlobal63_hz35 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal63_hz34 (by norm_num) (by norm_num)

theorem sGlobal63_hz36 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal63_hz35 sGlobal63_hz27 (by norm_num) (by norm_num)

theorem sGlobal63_hz37 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (s3rpp 12225 46) := by
    convert sGlobal63_hz36 using 1 <;>
      norm_num [s3rpp, mA] <;> ring

theorem sGlobal63_hz38 {c : ℝ} (hc : B (33 / 50) (133 / 200) c) : B (33 / 50) (133 / 200) c := hc

theorem sGlobal63_hz39 : B (364721868865849627 / 500000000000000000) (729443737731699257 / 1000000000000000000) (kdot ((33 / 50))) := by
    constructor
    · apply bkdot_lower (q := (452569637855251769 / 1000000000000000000)) (a := (84997756592480699 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (56571204731906471 / 125000000000000000)) (a := (424988782962403493 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal63_hz40 : B (1089 / 2500) (1089 / 2500) (((33 / 50) : ℝ)^2) := bsq (bpoint ((33 / 50) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal63_hz41 : B (1411 / 2500) (1411 / 2500) ((1 : ℝ) - (((33 / 50) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal63_hz40 (by norm_num) (by norm_num)

theorem sGlobal63_hz42 : B (46954099927482371 / 62500000000000000) (751265598839717937 / 1000000000000000000) (√((1 : ℝ) - (((33 / 50) : ℝ)^2))) := bsqrt sGlobal63_hz41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal63_hz43 : B (239135267260467957 / 1000000000000000000) (119567633630233979 / 500000000000000000) ((√((1 : ℝ) - (((33 / 50) : ℝ)^2))) / Real.pi) := bdiv sGlobal63_hz42 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal63_hz44 : B (481432866902921507 / 1000000000000000000) (48143286690292151 / 100000000000000000) (((33 / 50) : ℝ) * (kdot ((33 / 50)))) := bmul (bpoint ((33 / 50) : ℝ)) sGlobal63_hz39 (by norm_num) (by norm_num)

theorem sGlobal63_hz45 : B (90071016770423683 / 125000000000000000) (180142033540847367 / 250000000000000000) (((√((1 : ℝ) - (((33 / 50) : ℝ)^2))) / Real.pi) + (((33 / 50) : ℝ) * (kdot ((33 / 50))))) := badd sGlobal63_hz43 sGlobal63_hz44 (by norm_num) (by norm_num)

theorem sGlobal63_hz46 : B (90071016770423683 / 125000000000000000) (180142033540847367 / 250000000000000000) (kappa ((33 / 50))) := by rw [kappa_eq]; exact sGlobal63_hz45

theorem sGlobal63_hz47 : B (731568474407441717 / 1000000000000000000) (731568474407441719 / 1000000000000000000) (kdot ((133 / 200))) := by
    constructor
    · apply bkdot_lower (q := (448554568810976667 / 1000000000000000000)) (a := (84330250879348167 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (224277284405488333 / 500000000000000000)) (a := (421651254396740833 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal63_hz48 : B (17689 / 40000) (17689 / 40000) (((133 / 200) : ℝ)^2) := bsq (bpoint ((133 / 200) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal63_hz49 : B (22311 / 40000) (22311 / 40000) ((1 : ℝ) - (((133 / 200) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal63_hz48 (by norm_num) (by norm_num)

theorem sGlobal63_hz50 : B (746843357070276149 / 1000000000000000000) (14936867141405523 / 20000000000000000) (√((1 : ℝ) - (((133 / 200) : ℝ)^2))) := bsqrt sGlobal63_hz49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal63_hz51 : B (237727623986159737 / 1000000000000000000) (118863811993079869 / 500000000000000000) ((√((1 : ℝ) - (((133 / 200) : ℝ)^2))) / Real.pi) := bdiv sGlobal63_hz50 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal63_hz52 : B (486493035480948741 / 1000000000000000000) (60811629435118593 / 125000000000000000) (((133 / 200) : ℝ) * (kdot ((133 / 200)))) := bmul (bpoint ((133 / 200) : ℝ)) sGlobal63_hz47 (by norm_num) (by norm_num)

theorem sGlobal63_hz53 : B (362110329733554239 / 500000000000000000) (362110329733554241 / 500000000000000000) (((√((1 : ℝ) - (((133 / 200) : ℝ)^2))) / Real.pi) + (((133 / 200) : ℝ) * (kdot ((133 / 200))))) := badd sGlobal63_hz51 sGlobal63_hz52 (by norm_num) (by norm_num)

theorem sGlobal63_hz54 : B (362110329733554239 / 500000000000000000) (362110329733554241 / 500000000000000000) (kappa ((133 / 200))) := by rw [kappa_eq]; exact sGlobal63_hz53

theorem sGlobal63_hz55 {c : ℝ} (hc : B (33 / 50) (133 / 200) c) : B (90071016770423683 / 125000000000000000) (362110329733554241 / 500000000000000000) (kappa c) := bkappa (sGlobal63_hz38 hc) (by norm_num) (by norm_num) sGlobal63_hz46.1 sGlobal63_hz54.2

theorem sGlobal63_hz56 : B 24450 24450 ((2 : ℝ) * (12225 : ℝ)) := bmul (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal63_hz57 {c : ℝ} (hc : B (33 / 50) (133 / 200) c) : B (137889670266445759 / 500000000000000000) (34928983229576317 / 125000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (sGlobal63_hz55 hc) (by norm_num) (by norm_num)

theorem sGlobal63_hz58 {c : ℝ} (hc : B (33 / 50) (133 / 200) c) : B (67428048760291976151 / 10000000000000000) (17080272799262819013 / 2500000000000000) (((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) := bmul sGlobal63_hz56 (sGlobal63_hz57 hc) (by norm_num) (by norm_num)

theorem sGlobal63_hz59 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (4 : ℝ)) sGlobal63_hz10 (by norm_num) (by norm_num)

theorem sGlobal63_hz60 {c : ℝ} (hc : B (33 / 50) (133 / 200) c) : B (337140211081623479937 / 50000000000000000) (1708027116327099897211 / 250000000000000000) ((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bsub (sGlobal63_hz58 hc) sGlobal63_hz59 (by norm_num) (by norm_num)

theorem sGlobal63_hz61 {c : ℝ} (hc : B (33 / 50) (133 / 200) c) : B (82114579835936989337 / 1000000000000000000) (41328284701002289447 / 500000000000000000) (√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) := bsqrt (sGlobal63_hz60 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal63_hz62 : B (30670756373515103 / 125000000000000000) (122683025494060423 / 500000000000000000) ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal63_hz7 (by norm_num) (by norm_num)

theorem sGlobal63_hz63 {c : ℝ} (hc : B (33 / 50) (133 / 200) c) : B (81869213784948868491 / 1000000000000000000) (8241120335101645807 / 100000000000000000) ((√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) - ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))))) := bsub (sGlobal63_hz61 hc) sGlobal63_hz62 (by norm_num) (by norm_num)

theorem sGlobal63_hz64 {c : ℝ} (hc : B (33 / 50) (133 / 200) c) : B (81869213784948868491 / 1000000000000000000) (8241120335101645807 / 100000000000000000) (s3dm 12225 46 c) := by
    convert (sGlobal63_hz63 hc) using 1 <;>
      norm_num [s3dm, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal63_hz65 : B (6126072185528622723889 / 500000000000000000) (2450428874211449090087 / 200000000000000000) ((s3ap 12225 46)^2) := bsq sGlobal63_hz9 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal63_hz66 : B (6126072185528622723889 / 250000000000000000) (2450428874211449090087 / 100000000000000000) ((2 : ℝ) * ((s3ap 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal63_hz65 (by norm_num) (by norm_num)

theorem sGlobal63_hz67 {c : ℝ} (hc : B (33 / 50) (133 / 200) c) : B (3351284082882830916671 / 500000000000000000) (6791606437762586287909 / 1000000000000000000) ((s3dm 12225 46 c)^2) := bsq (sGlobal63_hz64 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal63_hz68 {c : ℝ} (hc : B (33 / 50) (133 / 200) c) : B (17712682304351904607647 / 1000000000000000000) (2225215072043603633441 / 125000000000000000) (((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) := bsub sGlobal63_hz66 (sGlobal63_hz67 hc) (by norm_num) (by norm_num)

theorem sGlobal63_hz69 : B (1524735695971823534271 / 125000000000000000) (609894278388729413841 / 50000000000000000) ((s3am 12225 46)^2) := bsq sGlobal63_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal63_hz70 : B (1524735695971823534271 / 62500000000000000) (609894278388729413841 / 25000000000000000) ((2 : ℝ) * ((s3am 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal63_hz69 (by norm_num) (by norm_num)

theorem sGlobal63_hz71 {c : ℝ} (hc : B (33 / 50) (133 / 200) c) : B (726055438294435859 / 1000000000000000000) (91213147544291041 / 125000000000000000) ((((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) / ((2 : ℝ) * ((s3am 12225 46)^2))) := bdiv (sGlobal63_hz68 hc) sGlobal63_hz70 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal63_hz72 {c : ℝ} (hc : B (33 / 50) (133 / 200) c) : B (726055438294435859 / 1000000000000000000) (91213147544291041 / 125000000000000000) (s3c1 12225 46 c) := by
    convert (sGlobal63_hz71 hc) using 1 <;>
      norm_num [s3c1] <;> ring

theorem sGlobal63_hz73 {c : ℝ} (hc : B (33 / 50) (133 / 200) c) : B (364721868865849627 / 500000000000000000) (731568474407441719 / 1000000000000000000) (kdot c) := bkdot (sGlobal63_hz38 hc) sGlobal63_hz39.1 sGlobal63_hz47.2

theorem sGlobal63_hz74 : B (758648437824030509 / 1000000000000000000) (758648437824030511 / 1000000000000000000) (kdot ((726055438294435859 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (99596477821280293 / 250000000000000000)) (a := (189557073666111491 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (398385911285121171 / 1000000000000000000)) (a := (18955707366611149 / 50000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal63_hz75 : B (760342688756481299 / 1000000000000000000) (760342688756481301 / 1000000000000000000) (kdot ((91213147544291041 / 125000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (197652732358742473 / 500000000000000000)) (a := (94113206047715113 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (79061092943496989 / 200000000000000000)) (a := (376452824190860451 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal63_hz76 {c : ℝ} (hc : B (33 / 50) (133 / 200) c) : B (758648437824030509 / 1000000000000000000) (760342688756481301 / 1000000000000000000) (kdot (s3c1 12225 46 c)) := bkdot (sGlobal63_hz72 hc) sGlobal63_hz74.1 sGlobal63_hz75.2

theorem sGlobal63_hz77 {c : ℝ} (hc : B (33 / 50) (133 / 200) c) : B (1089 / 2500) (17689 / 40000) (c^2) := bsq (sGlobal63_hz38 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal63_hz78 {c : ℝ} (hc : B (33 / 50) (133 / 200) c) : B (22311 / 40000) (1411 / 2500) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (sGlobal63_hz77 hc) (by norm_num) (by norm_num)

theorem sGlobal63_hz79 {c : ℝ} (hc : B (33 / 50) (133 / 200) c) : B (746843357070276149 / 1000000000000000000) (751265598839717937 / 1000000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (sGlobal63_hz78 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal63_hz80 : B (39119999999999765769 / 1600000000000000) (3912000000000000489 / 160000000000000) ((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (149450625 : ℝ)) sGlobal63_hz10 (by norm_num) (by norm_num)

theorem sGlobal63_hz81 {c : ℝ} (hc : B (33 / 50) (133 / 200) c) : B (136195052470358083 / 250000000000000000) (549602228017965569 / 1000000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (sGlobal63_hz79 hc) (sGlobal63_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal63_hz82 {c : ℝ} (hc : B (33 / 50) (133 / 200) c) : B (13319876131600940764641 / 1000000000000000000) (3359443618759814960443 / 250000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) := bmul sGlobal63_hz80 (sGlobal63_hz81 hc) (by norm_num) (by norm_num)

theorem sGlobal63_hz83 {c : ℝ} (hc : B (33 / 50) (133 / 200) c) : B (83249225822505879779 / 12500000000000000) (3359443618759814960443 / 500000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) / (2 : ℝ)) := bdiv (sGlobal63_hz82 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal63_hz84 {c : ℝ} (hc : B (33 / 50) (133 / 200) c) : B (83249225822505879779 / 12500000000000000) (3359443618759814960443 / 500000000000000000) (s3Cpa 12225 c) := by
    convert (sGlobal63_hz83 hc) using 1 <;>
      norm_num [s3Cpa, mA] <;> ring

theorem sGlobal63_hz85 {c : ℝ} (hc : B (33 / 50) (133 / 200) c) : B (237727623986159737 / 1000000000000000000) (119567633630233979 / 500000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (sGlobal63_hz79 hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal63_hz86 {c : ℝ} (hc : B (33 / 50) (133 / 200) c) : B (481432866902921507 / 1000000000000000000) (60811629435118593 / 125000000000000000) (c * (kdot c)) := bmul (sGlobal63_hz38 hc) (sGlobal63_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal63_hz87 {c : ℝ} (hc : B (33 / 50) (133 / 200) c) : B (-248765411494789007 / 1000000000000000000) (-242297599642453549 / 1000000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (sGlobal63_hz85 hc) (sGlobal63_hz86 hc) (by norm_num) (by norm_num)

theorem sGlobal63_hz88 {c : ℝ} (hc : B (33 / 50) (133 / 200) c) : B (-9503616111011862471 / 1562500000000000) (-1481044077814488450511 / 250000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) := bmul sGlobal63_hz80 (sGlobal63_hz87 hc) (by norm_num) (by norm_num)

theorem sGlobal63_hz89 {c : ℝ} (hc : B (33 / 50) (133 / 200) c) : B (-9503616111011862471 / 3125000000000000) (-1481044077814488450511 / 500000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) / (2 : ℝ)) := bdiv (sGlobal63_hz88 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal63_hz90 {c : ℝ} (hc : B (33 / 50) (133 / 200) c) : B (-9503616111011862471 / 3125000000000000) (-1481044077814488450511 / 500000000000000000) (s3Cpp 12225 c) := by
    convert (sGlobal63_hz89 hc) using 1 <;>
      norm_num [s3Cpp, mA] <;> ring

theorem sGlobal63_hz91 {c : ℝ} (hc : B (33 / 50) (133 / 200) c) : B (6775083175734208090721 / 1000000000000000000) (854254043431671041639 / 125000000000000000) ((s3Cpa 12225 c) + (s3r1 12225 46)) := badd (sGlobal63_hz84 hc) sGlobal63_hz33 (by norm_num) (by norm_num)

theorem sGlobal63_hz92 {c : ℝ} (hc : B (33 / 50) (133 / 200) c) : B (1533600927641953431 / 25000000000000000) (12375556816928758117 / 200000000000000000) (((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) := bdiv (sGlobal63_hz91 hc) sGlobal63_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal63_hz93 {c : ℝ} (hc : B (33 / 50) (133 / 200) c) : B (15366680032793049413 / 250000000000000000) (484378649297951961 / 7812500000000000) ((((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) + (s3e0 12225 46)) := badd (sGlobal63_hz92 hc) sGlobal63_hz16 (by norm_num) (by norm_num)

theorem sGlobal63_hz94 {c : ℝ} (hc : B (33 / 50) (133 / 200) c) : B (15366680032793049413 / 250000000000000000) (484378649297951961 / 7812500000000000) (s3Lam 12225 46 c) := by
    convert (sGlobal63_hz93 hc) using 1 <;>
      norm_num [s3Lam] <;> ring

theorem sGlobal63_hz95 {c : ℝ} (hc : B (33 / 50) (133 / 200) c) : B (-18527460930633151157 / 6250000000000000) (-721331187251621156551 / 250000000000000000) ((s3Cpp 12225 c) + (s3rpp 12225 46)) := badd (sGlobal63_hz90 hc) sGlobal63_hz37 (by norm_num) (by norm_num)

theorem sGlobal63_hz96 {c : ℝ} (hc : B (33 / 50) (133 / 200) c) : B (-450791022714504622133 / 200000000000000000) (-721331187251621156551 / 500000000000000000) (if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) := bweaken (bfirst (sGlobal63_hz95 hc) (sGlobal63_hz76 hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem sGlobal63_hz97 {c : ℝ} (hc : B (33 / 50) (133 / 200) c) : B (1889078841841924753463 / 500000000000000000) (961014480468821351469 / 250000000000000000) ((s3Lam 12225 46 c)^2) := bsq (sGlobal63_hz94 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal63_hz98 {c : ℝ} (hc : B (33 / 50) (133 / 200) c) : B (527156499476925357 / 1000000000000000000) (532469650235942833 / 1000000000000000000) ((s3c1 12225 46 c)^2) := bsq (sGlobal63_hz72 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal63_hz99 {c : ℝ} (hc : B (33 / 50) (133 / 200) c) : B (467530349764057167 / 1000000000000000000) (472843500523074643 / 1000000000000000000) ((1 : ℝ) - ((s3c1 12225 46 c)^2)) := bsub (bpoint (1 : ℝ)) (sGlobal63_hz98 hc) (by norm_num) (by norm_num)

theorem sGlobal63_hz100 {c : ℝ} (hc : B (33 / 50) (133 / 200) c) : B (683761910144208871 / 1000000000000000000) (137527233742713613 / 200000000000000000) (√((1 : ℝ) - ((s3c1 12225 46 c)^2))) := bsqrt (sGlobal63_hz99 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal63_hz101 {c : ℝ} (hc : B (33 / 50) (133 / 200) c) : B (214810139371357091 / 100000000000000000) (1080136367986588529 / 500000000000000000) (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))) := bmul pi_mem (sGlobal63_hz100 hc) (by norm_num) (by norm_num)

theorem sGlobal63_hz102 {c : ℝ} (hc : B (33 / 50) (133 / 200) c) : B (437231561178528067827 / 250000000000000000) (357902837652350997577 / 200000000000000000) (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2))))) := bdiv (sGlobal63_hz97 hc) (sGlobal63_hz101 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal63_hz103 {c : ℝ} (hc : B (33 / 50) (133 / 200) c) : B (-505028868858410839357 / 1000000000000000000) (346851813758512674783 / 1000000000000000000) ((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) := badd (sGlobal63_hz96 hc) (sGlobal63_hz102 hc) (by norm_num) (by norm_num)

theorem sGlobal63_hz104 : B (3762781186094069 / 250000000000000000) (376278118609407 / 25000000000000000) ((s3e0 12225 46)^2) := bsq sGlobal63_hz16 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal63_hz105 {c : ℝ} (hc : B (33 / 50) (133 / 200) c) : B (-505013817733666463081 / 1000000000000000000) (346866864883257051063 / 1000000000000000000) (((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) := badd (sGlobal63_hz103 hc) sGlobal63_hz104 (by norm_num) (by norm_num)

theorem sGlobal63_hz106 {c : ℝ} (hc : B (33 / 50) (133 / 200) c) : B (-9330334885648383859 / 20000000000000000) (385363938337381321079 / 1000000000000000000) ((((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) + (s3rs 12225 46 maskSlack)) := badd (sGlobal63_hz105 hc) sGlobal63_hz29 (by norm_num) (by norm_num)

theorem sGlobal63_hz107 {c : ℝ} (hc : B (33 / 50) (133 / 200) c) : B (-9330334885648383859 / 20000000000000000) (385363938337381321079 / 1000000000000000000) (s3U 12225 46 maskSlack c) := by
    convert (sGlobal63_hz106 hc) using 1 <;>
      norm_num [s3U] <;> ring

theorem sGlobal63_hz108 {c : ℝ} (hc : B (33 / 50) (133 / 200) c) : B (-1558960281073144132769 / 500000000000000000) (-1519425781125734353311 / 500000000000000000) ((s3Cpp 12225 c) - (s3rpp 12225 46)) := bsub (sGlobal63_hz90 hc) sGlobal63_hz37 (by norm_num) (by norm_num)

theorem sGlobal63_hz109 {c : ℝ} (hc : B (33 / 50) (133 / 200) c) : B (-1558960281073144132769 / 500000000000000000) (-1519425781125734353311 / 500000000000000000) (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ)) := bweaken (bmin (sGlobal63_hz108 hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem sGlobal63_hz110 {c : ℝ} (hc : B (33 / 50) (133 / 200) c) : B (-237068810355142847231 / 100000000000000000) (-46108399809623826697 / 20000000000000000) ((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) := bmul (sGlobal63_hz76 hc) (sGlobal63_hz109 hc) (by norm_num) (by norm_num)

theorem sGlobal63_hz111 {c : ℝ} (hc : B (33 / 50) (133 / 200) c) : B (-237070315467617284859 / 100000000000000000) (-1152717520802967855563 / 500000000000000000) (((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) := bsub (sGlobal63_hz110 hc) sGlobal63_hz104 (by norm_num) (by norm_num)

theorem sGlobal63_hz112 {c : ℝ} (hc : B (33 / 50) (133 / 200) c) : B (-1204600114065148559303 / 500000000000000000) (-2343932115057182981257 / 1000000000000000000) ((((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) - (s3rs 12225 46 maskSlack)) := bsub (sGlobal63_hz111 hc) sGlobal63_hz29 (by norm_num) (by norm_num)

theorem sGlobal63_hz113 {c : ℝ} (hc : B (33 / 50) (133 / 200) c) : B (-1204600114065148559303 / 500000000000000000) (-2343932115057182981257 / 1000000000000000000) (s3L 12225 46 maskSlack c) := by
    convert (sGlobal63_hz112 hc) using 1 <;>
      norm_num [s3L] <;> ring

theorem sGlobal63_hz114 {c : ℝ} (hc : B (33 / 50) (133 / 200) c) : B 0 (9330334885648383859 / 20000000000000000) |(s3U 12225 46 maskSlack c)| := bweaken (babs (sGlobal63_hz107 hc)) (by norm_num) (by norm_num)

theorem sGlobal63_hz115 {c : ℝ} (hc : B (33 / 50) (133 / 200) c) : B 0 (1204600114065148559303 / 500000000000000000) |(s3L 12225 46 maskSlack c)| := bweaken (babs (sGlobal63_hz113 hc)) (by norm_num) (by norm_num)

theorem sGlobal63_hz116 {c : ℝ} (hc : B (33 / 50) (133 / 200) c) : B 0 (1204600114065148559303 / 500000000000000000) (max |(s3U 12225 46 maskSlack c)| |(s3L 12225 46 maskSlack c)|) := bweaken (bmax (sGlobal63_hz114 hc) (sGlobal63_hz115 hc)) (by norm_num) (by norm_num)

theorem sGlobal63_hz117 {c : ℝ} (hc : B (33 / 50) (133 / 200) c) : B 0 (1204600114065148559303 / 500000000000000000) (s3nks 12225 46 maskSlack c) := by
    convert (sGlobal63_hz116 hc) using 1 <;>
      norm_num [s3nks] <;> ring

theorem sGlobal63 {c : ℝ} (hc : B (33 / 50) (133 / 200) c) :
    0 < s3am 12225 46 ∧ 0 ≤ s3dm 12225 46 c ∧
    s3dm 12225 46 c ^ 2 ≤ 2 * s3ap 12225 46 ^ 2 ∧ s3c1 12225 46 c < 1 ∧
    0 ≤ s3Cpa 12225 c - s3r1 12225 46 ∧
    s3e0 12225 46 ≤ (s3Cpa 12225 c - s3r1 12225 46) / s3ap 12225 46 ∧
    s3nks 12225 46 maskSlack c ≤ 12225 * (12317 / 62500) := by

  refine ⟨lt_of_lt_of_le (by norm_num) sGlobal63_hz14.1,
    le_trans (by norm_num) (sGlobal63_hz64 hc).1, ?_,
    lt_of_le_of_lt (sGlobal63_hz72 hc).2 (by norm_num), ?_, ?_,
    le_trans (sGlobal63_hz117 hc).2 (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (sGlobal63_hz64 hc).1) (sGlobal63_hz64 hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) sGlobal63_hz9.1 2
    nlinarith only [h1, h2]
  · linarith only [(sGlobal63_hz84 hc).1, sGlobal63_hz33.2]
  · have hap : 0 < s3ap 12225 46 := lt_of_lt_of_le (by norm_num) sGlobal63_hz9.1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul sGlobal63_hz16.2 sGlobal63_hz9.2 (le_trans (by norm_num) sGlobal63_hz9.1) (by norm_num)
    linarith only [h, (sGlobal63_hz84 hc).1, sGlobal63_hz33.2]

end BstLean.Part255
