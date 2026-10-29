import BstLean.Part255SGlobal53
import BstLean.Part255Numeric10
namespace BstLean.Part255
open Real BstLean.Part130 BstLean.Part182 BstLean.Part197 BstLean.Part246
theorem sGlobal57_hz0 : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal57_hz1 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) ((√(23 : ℝ)) / (12225 : ℝ)) := bdiv sGlobal57_hz0 (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal57_hz2 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) maskSlack := by
    convert sGlobal57_hz1 using 1 <;>
      norm_num [maskSlack] <;> ring

theorem sGlobal57_hz3 : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal57_hz4 : B (6395294793910793 / 500000000000000000) (12790589587821587 / 1000000000000000000) (√((2 / 12225) : ℝ)) := bsqrt (bpoint ((2 / 12225) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal57_hz5 : B (7230130686979 / 62500000000000000) (23136418198333 / 200000000000000000) (√((2 / 149450625) : ℝ)) := bsqrt (bpoint ((2 / 149450625) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal57_hz6 : B (2211334438749598093 / 20000000000000000) (110566721937479904651 / 1000000000000000000) (√(12225 : ℝ)) := bsqrt (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal57_hz7 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))) := bmul sGlobal57_hz3 sGlobal57_hz4 (by norm_num) (by norm_num)

theorem sGlobal57_hz8 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) ((√(12225 : ℝ)) + ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := badd sGlobal57_hz6 sGlobal57_hz7 (by norm_num) (by norm_num)

theorem sGlobal57_hz9 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) (s3ap 12225 46) := by
    convert sGlobal57_hz8 using 1 <;>
      norm_num [s3ap, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal57_hz10 : B (163599182004089 / 1000000000000000000) (16359918200409 / 100000000000000000) ((2 : ℝ) / (12225 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal57_hz11 : B (1222499983640081799591 / 100000000000000000) (12224999836400817995911 / 1000000000000000000) ((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ))) := bsub (bpoint (12225 : ℝ)) sGlobal57_hz10 (by norm_num) (by norm_num)

theorem sGlobal57_hz12 : B (110566721197658827907 / 1000000000000000000) (27641680299414706977 / 250000000000000000) (√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) := bsqrt sGlobal57_hz11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal57_hz13 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) ((√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) - ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bsub sGlobal57_hz12 sGlobal57_hz7 (by norm_num) (by norm_num)

theorem sGlobal57_hz14 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) (s3am 12225 46) := by
    convert sGlobal57_hz13 using 1 <;>
      norm_num [s3am, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal57_hz15 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√((2 / 12225) : ℝ)) * (√(92 : ℝ))) := bmul sGlobal57_hz4 sGlobal57_hz3 (by norm_num) (by norm_num)

theorem sGlobal57_hz16 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) (s3e0 12225 46) := by
    convert sGlobal57_hz15 using 1 <;>
      norm_num [s3e0, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal57_hz17 : B (250196148528560847 / 500000000000000000) (100078459411424339 / 200000000000000000) (((1 / 2) : ℝ) + maskSlack) := badd (bpoint ((1 / 2) : ℝ)) sGlobal57_hz2 (by norm_num) (by norm_num)

theorem sGlobal57_hz18 : B (59827153232297998295487 / 800000000000000) (23930861292919199366019 / 320000000000000) ((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack)) := bmul (bpoint (149450625 : ℝ)) sGlobal57_hz17 (by norm_num) (by norm_num)

theorem sGlobal57_hz19 : B (1729554180017180009583 / 200000000000000000) (8647770900085900056557 / 1000000000000000000) (√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) := bsqrt sGlobal57_hz18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal57_hz20 : B (4328681281566262743499 / 500000000000000000) (8657362563132525495641 / 1000000000000000000) ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))) := badd sGlobal57_hz19 sGlobal57_hz3 (by norm_num) (by norm_num)

theorem sGlobal57_hz21 : B (110732771457999278473 / 1000000000000000000) (55366385728999643621 / 500000000000000000) ((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ)))) := bmul sGlobal57_hz4 sGlobal57_hz20 (by norm_num) (by norm_num)

theorem sGlobal57_hz22 : B (209099159 / 15625000000000000) (13382346177 / 1000000000000000000) ((2 : ℝ) / (149450625 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (149450625 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal57_hz23 : B (2452349334953899930479 / 200000000000000000) (12261746674769501594427 / 1000000000000000000) (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2) := bsq sGlobal57_hz21 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal57_hz24 : B (82045469362091 / 500000000000000000) (32818187747289 / 200000000000000000) (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2)) := bmul sGlobal57_hz22 sGlobal57_hz23 (by norm_num) (by norm_num)

theorem sGlobal57_hz25 : B (82045469362091 / 250000000000000000) (32818187747289 / 100000000000000000) ((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) := bmul (bpoint (2 : ℝ)) sGlobal57_hz24 (by norm_num) (by norm_num)

theorem sGlobal57_hz26 : B (117258080744995992792057 / 1000000000000000000) (58629040372497996396029 / 500000000000000000) (√(13749457500 : ℝ)) := bsqrt (bpoint (13749457500 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal57_hz27 : B (117304080744995992792057 / 1000000000000000000) (58652040372497996396029 / 500000000000000000) ((√(13749457500 : ℝ)) + (46 : ℝ)) := badd sGlobal57_hz26 (bpoint (46 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal57_hz28 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal57_hz25 sGlobal57_hz27 (by norm_num) (by norm_num)

theorem sGlobal57_hz29 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (s3rs 12225 46 maskSlack) := by
    convert sGlobal57_hz28 using 1 <;>
      norm_num [s3rs, s3pp, s3K, mA, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal57_hz30 : B (490797546012267 / 1000000000000000000) (49079754601227 / 100000000000000000) ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (3 : ℝ)) sGlobal57_hz10 (by norm_num) (by norm_num)

theorem sGlobal57_hz31 : B (490797546012267 / 500000000000000000) (49079754601227 / 50000000000000000) ((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal57_hz30 (by norm_num) (by norm_num)

theorem sGlobal57_hz32 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal57_hz31 sGlobal57_hz27 (by norm_num) (by norm_num)

theorem sGlobal57_hz33 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (s3r1 12225 46) := by
    convert sGlobal57_hz32 using 1 <;>
      norm_num [s3r1, mA] <;> ring

theorem sGlobal57_hz34 : B (163599182004089 / 500000000000000000) (16359918200409 / 50000000000000000) ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (2 : ℝ)) sGlobal57_hz10 (by norm_num) (by norm_num)

theorem sGlobal57_hz35 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal57_hz34 (by norm_num) (by norm_num)

theorem sGlobal57_hz36 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal57_hz35 sGlobal57_hz27 (by norm_num) (by norm_num)

theorem sGlobal57_hz37 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (s3rpp 12225 46) := by
    convert sGlobal57_hz36 using 1 <;>
      norm_num [s3rpp, mA] <;> ring

theorem sGlobal57_hz38 {c : ℝ} (hc : B (63 / 100) (127 / 200) c) : B (63 / 100) (127 / 200) c := hc

theorem sGlobal57_hz39 : B (716945125200852751 / 1000000000000000000) (716945125200852757 / 1000000000000000000) (kdot ((63 / 100))) := by
    constructor
    · apply bkdot_lower (q := (119109682916281739 / 250000000000000000)) (a := (444621557615889849 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (95287746333025391 / 200000000000000000)) (a := (444621557615889841 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal57_hz40 : B (3969 / 10000) (3969 / 10000) (((63 / 100) : ℝ)^2) := bsq (bpoint ((63 / 100) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal57_hz41 : B (6031 / 10000) (6031 / 10000) ((1 : ℝ) - (((63 / 100) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal57_hz40 (by norm_num) (by norm_num)

theorem sGlobal57_hz42 : B (776595132614156937 / 1000000000000000000) (388297566307078469 / 500000000000000000) (√((1 : ℝ) - (((63 / 100) : ℝ)^2))) := bsqrt sGlobal57_hz41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal57_hz43 : B (247197908273298117 / 1000000000000000000) (123598954136649059 / 500000000000000000) ((√((1 : ℝ) - (((63 / 100) : ℝ)^2))) / Real.pi) := bdiv sGlobal57_hz42 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal57_hz44 : B (451675428876537233 / 1000000000000000000) (451675428876537237 / 1000000000000000000) (((63 / 100) : ℝ) * (kdot ((63 / 100)))) := bmul (bpoint ((63 / 100) : ℝ)) sGlobal57_hz39 (by norm_num) (by norm_num)

theorem sGlobal57_hz45 : B (13977466742996707 / 20000000000000000) (139774667429967071 / 200000000000000000) (((√((1 : ℝ) - (((63 / 100) : ℝ)^2))) / Real.pi) + (((63 / 100) : ℝ) * (kdot ((63 / 100))))) := badd sGlobal57_hz43 sGlobal57_hz44 (by norm_num) (by norm_num)

theorem sGlobal57_hz46 : B (13977466742996707 / 20000000000000000) (139774667429967071 / 200000000000000000) (kappa ((63 / 100))) := by rw [kappa_eq]; exact sGlobal57_hz45

theorem sGlobal57_hz47 : B (359499956852941657 / 500000000000000000) (718999913705883319 / 1000000000000000000) (kdot ((127 / 200))) := by
    constructor
    · apply bkdot_lower (q := (236242243372172581 / 500000000000000000)) (a := (55174237922480933 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (472484486744345161 / 1000000000000000000)) (a := (220696951689923729 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal57_hz48 : B (16129 / 40000) (16129 / 40000) (((127 / 200) : ℝ)^2) := bsq (bpoint ((127 / 200) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal57_hz49 : B (23871 / 40000) (23871 / 40000) ((1 : ℝ) - (((127 / 200) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal57_hz48 (by norm_num) (by norm_num)

theorem sGlobal57_hz50 : B (386256067913502169 / 500000000000000000) (772512135827004339 / 1000000000000000000) (√((1 : ℝ) - (((127 / 200) : ℝ)^2))) := bsqrt sGlobal57_hz49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal57_hz51 : B (24589825003069079 / 100000000000000000) (30737281253836349 / 125000000000000000) ((√((1 : ℝ) - (((127 / 200) : ℝ)^2))) / Real.pi) := bdiv sGlobal57_hz50 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal57_hz52 : B (7133827268800561 / 15625000000000000) (114141236300808977 / 250000000000000000) (((127 / 200) : ℝ) * (kdot ((127 / 200)))) := bmul (bpoint ((127 / 200) : ℝ)) sGlobal57_hz47 (by norm_num) (by norm_num)

theorem sGlobal57_hz53 : B (351231597616963347 / 500000000000000000) (7024631952339267 / 10000000000000000) (((√((1 : ℝ) - (((127 / 200) : ℝ)^2))) / Real.pi) + (((127 / 200) : ℝ) * (kdot ((127 / 200))))) := badd sGlobal57_hz51 sGlobal57_hz52 (by norm_num) (by norm_num)

theorem sGlobal57_hz54 : B (351231597616963347 / 500000000000000000) (7024631952339267 / 10000000000000000) (kappa ((127 / 200))) := by rw [kappa_eq]; exact sGlobal57_hz53

theorem sGlobal57_hz55 {c : ℝ} (hc : B (63 / 100) (127 / 200) c) : B (13977466742996707 / 20000000000000000) (7024631952339267 / 10000000000000000) (kappa c) := bkappa (sGlobal57_hz38 hc) (by norm_num) (by norm_num) sGlobal57_hz46.1 sGlobal57_hz54.2

theorem sGlobal57_hz56 : B 24450 24450 ((2 : ℝ) * (12225 : ℝ)) := bmul (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal57_hz57 {c : ℝ} (hc : B (63 / 100) (127 / 200) c) : B (2975368047660733 / 10000000000000000) (6022533257003293 / 20000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (sGlobal57_hz55 hc) (by norm_num) (by norm_num)

theorem sGlobal57_hz58 {c : ℝ} (hc : B (63 / 100) (127 / 200) c) : B (1454954975306098437 / 200000000000000) (2945018762674610277 / 400000000000000) (((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) := bmul sGlobal57_hz56 (sGlobal57_hz57 hc) (by norm_num) (by norm_num)

theorem sGlobal57_hz59 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (4 : ℝ)) sGlobal57_hz10 (by norm_num) (by norm_num)

theorem sGlobal57_hz60 {c : ℝ} (hc : B (63 / 100) (127 / 200) c) : B (22733669444168013027 / 3125000000000000) (460159140768112354759 / 62500000000000000) ((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bsub (sGlobal57_hz58 hc) sGlobal57_hz59 (by norm_num) (by norm_num)

theorem sGlobal57_hz61 {c : ℝ} (hc : B (63 / 100) (127 / 200) c) : B (21323071750649817211 / 250000000000000000) (85805281027975181827 / 1000000000000000000) (√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) := bsqrt (sGlobal57_hz60 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal57_hz62 : B (30670756373515103 / 125000000000000000) (122683025494060423 / 500000000000000000) ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal57_hz7 (by norm_num) (by norm_num)

theorem sGlobal57_hz63 {c : ℝ} (hc : B (63 / 100) (127 / 200) c) : B (42523460475805573999 / 500000000000000000) (85559914976987061003 / 1000000000000000000) ((√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) - ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))))) := bsub (sGlobal57_hz61 hc) sGlobal57_hz62 (by norm_num) (by norm_num)

theorem sGlobal57_hz64 {c : ℝ} (hc : B (63 / 100) (127 / 200) c) : B (42523460475805573999 / 500000000000000000) (85559914976987061003 / 1000000000000000000) (s3dm 12225 46 c) := by
    convert (sGlobal57_hz63 hc) using 1 <;>
      norm_num [s3dm, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal57_hz65 : B (6126072185528622723889 / 500000000000000000) (2450428874211449090087 / 200000000000000000) ((s3ap 12225 46)^2) := bsq sGlobal57_hz9 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal57_hz66 : B (6126072185528622723889 / 250000000000000000) (2450428874211449090087 / 100000000000000000) ((2 : ℝ) * ((s3ap 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal57_hz65 (by norm_num) (by norm_num)

theorem sGlobal57_hz67 {c : ℝ} (hc : B (63 / 100) (127 / 200) c) : B (7232978763349595255351 / 1000000000000000000) (7320499050869254791563 / 1000000000000000000) ((s3dm 12225 46 c)^2) := bsq (sGlobal57_hz64 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal57_hz68 {c : ℝ} (hc : B (63 / 100) (127 / 200) c) : B (17183789691245236103993 / 1000000000000000000) (17271309978764895645519 / 1000000000000000000) (((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) := bsub sGlobal57_hz66 (sGlobal57_hz67 hc) (by norm_num) (by norm_num)

theorem sGlobal57_hz69 : B (1524735695971823534271 / 125000000000000000) (609894278388729413841 / 50000000000000000) ((s3am 12225 46)^2) := bsq sGlobal57_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal57_hz70 : B (1524735695971823534271 / 62500000000000000) (609894278388729413841 / 25000000000000000) ((2 : ℝ) * ((s3am 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal57_hz69 (by norm_num) (by norm_num)

theorem sGlobal57_hz71 {c : ℝ} (hc : B (63 / 100) (127 / 200) c) : B (352187877066227639 / 500000000000000000) (353981636464800743 / 500000000000000000) ((((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) / ((2 : ℝ) * ((s3am 12225 46)^2))) := bdiv (sGlobal57_hz68 hc) sGlobal57_hz70 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal57_hz72 {c : ℝ} (hc : B (63 / 100) (127 / 200) c) : B (352187877066227639 / 500000000000000000) (353981636464800743 / 500000000000000000) (s3c1 12225 46 c) := by
    convert (sGlobal57_hz71 hc) using 1 <;>
      norm_num [s3c1] <;> ring

theorem sGlobal57_hz73 {c : ℝ} (hc : B (63 / 100) (127 / 200) c) : B (716945125200852751 / 1000000000000000000) (718999913705883319 / 1000000000000000000) (kdot c) := bkdot (sGlobal57_hz38 hc) sGlobal57_hz39.1 sGlobal57_hz47.2

theorem sGlobal57_hz74 : B (748772967853183561 / 1000000000000000000) (748772967853183563 / 1000000000000000000) (kdot ((352187877066227639 / 500000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (416473479571388967 / 1000000000000000000)) (a := (394626499287802673 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (208236739785694483 / 500000000000000000)) (a := (394626499287802671 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal57_hz75 : B (375192895314213651 / 500000000000000000) (93798223828553413 / 125000000000000000) (kdot ((353981636464800743 / 500000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (413503769045976577 / 1000000000000000000)) (a := (392093083196678653 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (807624548917923 / 1953125000000000)) (a := (392093083196678651 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal57_hz76 {c : ℝ} (hc : B (63 / 100) (127 / 200) c) : B (748772967853183561 / 1000000000000000000) (93798223828553413 / 125000000000000000) (kdot (s3c1 12225 46 c)) := bkdot (sGlobal57_hz72 hc) sGlobal57_hz74.1 sGlobal57_hz75.2

theorem sGlobal57_hz77 {c : ℝ} (hc : B (63 / 100) (127 / 200) c) : B (3969 / 10000) (16129 / 40000) (c^2) := bsq (sGlobal57_hz38 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal57_hz78 {c : ℝ} (hc : B (63 / 100) (127 / 200) c) : B (23871 / 40000) (6031 / 10000) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (sGlobal57_hz77 hc) (by norm_num) (by norm_num)

theorem sGlobal57_hz79 {c : ℝ} (hc : B (63 / 100) (127 / 200) c) : B (386256067913502169 / 500000000000000000) (388297566307078469 / 500000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (sGlobal57_hz78 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal57_hz80 : B (39119999999999765769 / 1600000000000000) (3912000000000000489 / 160000000000000) ((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (149450625 : ℝ)) sGlobal57_hz10 (by norm_num) (by norm_num)

theorem sGlobal57_hz81 {c : ℝ} (hc : B (63 / 100) (127 / 200) c) : B (553848809939669791 / 1000000000000000000) (558371833333987851 / 1000000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (sGlobal57_hz79 hc) (sGlobal57_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal57_hz82 {c : ℝ} (hc : B (63 / 100) (127 / 200) c) : B (13541603403024845309599 / 1000000000000000000) (6826095662508002331737 / 500000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) := bmul sGlobal57_hz80 (sGlobal57_hz81 hc) (by norm_num) (by norm_num)

theorem sGlobal57_hz83 {c : ℝ} (hc : B (63 / 100) (127 / 200) c) : B (6770801701512422654799 / 1000000000000000000) (6826095662508002331737 / 1000000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) / (2 : ℝ)) := bdiv (sGlobal57_hz82 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal57_hz84 {c : ℝ} (hc : B (63 / 100) (127 / 200) c) : B (6770801701512422654799 / 1000000000000000000) (6826095662508002331737 / 1000000000000000000) (s3Cpa 12225 c) := by
    convert (sGlobal57_hz83 hc) using 1 <;>
      norm_num [s3Cpa, mA] <;> ring

theorem sGlobal57_hz85 {c : ℝ} (hc : B (63 / 100) (127 / 200) c) : B (24589825003069079 / 100000000000000000) (123598954136649059 / 500000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (sGlobal57_hz79 hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal57_hz86 {c : ℝ} (hc : B (63 / 100) (127 / 200) c) : B (451675428876537233 / 1000000000000000000) (114141236300808977 / 250000000000000000) (c * (kdot c)) := bmul (sGlobal57_hz38 hc) (sGlobal57_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal57_hz87 {c : ℝ} (hc : B (63 / 100) (127 / 200) c) : B (-105333347586272559 / 500000000000000000) (-40895504120647823 / 200000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (sGlobal57_hz85 hc) (sGlobal57_hz86 hc) (by norm_num) (by norm_num)

theorem sGlobal57_hz88 {c : ℝ} (hc : B (63 / 100) (127 / 200) c) : B (-5150800696968728778951 / 1000000000000000000) (-4999475378749166427391 / 1000000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) := bmul sGlobal57_hz80 (sGlobal57_hz87 hc) (by norm_num) (by norm_num)

theorem sGlobal57_hz89 {c : ℝ} (hc : B (63 / 100) (127 / 200) c) : B (-643850087121091097369 / 250000000000000000) (-499947537874916642739 / 200000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) / (2 : ℝ)) := bdiv (sGlobal57_hz88 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal57_hz90 {c : ℝ} (hc : B (63 / 100) (127 / 200) c) : B (-643850087121091097369 / 250000000000000000) (-499947537874916642739 / 200000000000000000) (s3Cpp 12225 c) := by
    convert (sGlobal57_hz89 hc) using 1 <;>
      norm_num [s3Cpp, mA] <;> ring

theorem sGlobal57_hz91 {c : ℝ} (hc : B (63 / 100) (127 / 200) c) : B (4303716757153850227 / 625000000000000) (6941240772441740743963 / 1000000000000000000) ((s3Cpa 12225 c) + (s3r1 12225 46)) := badd (sGlobal57_hz84 hc) sGlobal57_hz33 (by norm_num) (by norm_num)

theorem sGlobal57_hz92 {c : ℝ} (hc : B (63 / 100) (127 / 200) c) : B (15586959073137247173 / 250000000000000000) (62848487680443605981 / 1000000000000000000) (((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) := bdiv (sGlobal57_hz91 hc) sGlobal57_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal57_hz93 {c : ℝ} (hc : B (63 / 100) (127 / 200) c) : B (3904407457377690569 / 62500000000000000) (15742792676484416601 / 250000000000000000) ((((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) + (s3e0 12225 46)) := badd (sGlobal57_hz92 hc) sGlobal57_hz16 (by norm_num) (by norm_num)

theorem sGlobal57_hz94 {c : ℝ} (hc : B (63 / 100) (127 / 200) c) : B (3904407457377690569 / 62500000000000000) (15742792676484416601 / 250000000000000000) (s3Lam 12225 46 c) := by
    convert (sGlobal57_hz93 hc) using 1 <;>
      norm_num [s3Lam] <;> ring

theorem sGlobal57_hz95 {c : ℝ} (hc : B (63 / 100) (127 / 200) c) : B (-624659235465468145969 / 250000000000000000) (-2422974282752090938877 / 1000000000000000000) ((s3Cpp 12225 c) + (s3rpp 12225 46)) := badd (sGlobal57_hz90 hc) sGlobal57_hz37 (by norm_num) (by norm_num)

theorem sGlobal57_hz96 {c : ℝ} (hc : B (63 / 100) (127 / 200) c) : B (-1874941657112417006781 / 1000000000000000000) (-605743570688022734719 / 500000000000000000) (if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) := bweaken (bfirst (sGlobal57_hz95 hc) (sGlobal57_hz76 hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem sGlobal57_hz97 {c : ℝ} (hc : B (63 / 100) (127 / 200) c) : B (390256578386598978489 / 100000000000000000) (247835521254771381213 / 62500000000000000) ((s3Lam 12225 46 c)^2) := bsq (sGlobal57_hz94 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal57_hz98 {c : ℝ} (hc : B (63 / 100) (127 / 200) c) : B (7752268797026017 / 15625000000000000) (100242399163438681 / 200000000000000000) ((s3c1 12225 46 c)^2) := bsq (sGlobal57_hz72 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal57_hz99 {c : ℝ} (hc : B (63 / 100) (127 / 200) c) : B (99757600836561319 / 200000000000000000) (7872731202973983 / 15625000000000000) ((1 : ℝ) - ((s3c1 12225 46 c)^2)) := bsub (bpoint (1 : ℝ)) (sGlobal57_hz98 hc) (by norm_num) (by norm_num)

theorem sGlobal57_hz100 {c : ℝ} (hc : B (63 / 100) (127 / 200) c) : B (706249250748492189 / 1000000000000000000) (709827300820653779 / 1000000000000000000) (√((1 : ℝ) - ((s3c1 12225 46 c)^2))) := bsqrt (sGlobal57_hz99 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal57_hz101 {c : ℝ} (hc : B (63 / 100) (127 / 200) c) : B (554686864438689711 / 250000000000000000) (1114994116787819063 / 500000000000000000) (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))) := bmul pi_mem (sGlobal57_hz100 hc) (by norm_num) (by norm_num)

theorem sGlobal57_hz102 {c : ℝ} (hc : B (63 / 100) (127 / 200) c) : B (875019366718470206373 / 500000000000000000) (1787210313736679274999 / 1000000000000000000) (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2))))) := bdiv (sGlobal57_hz97 hc) (sGlobal57_hz101 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal57_hz103 {c : ℝ} (hc : B (63 / 100) (127 / 200) c) : B (-24980584735095318807 / 200000000000000000) (575723172360633805561 / 1000000000000000000) ((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) := badd (sGlobal57_hz96 hc) (sGlobal57_hz102 hc) (by norm_num) (by norm_num)

theorem sGlobal57_hz104 : B (3762781186094069 / 250000000000000000) (376278118609407 / 25000000000000000) ((s3e0 12225 46)^2) := bsq sGlobal57_hz16 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal57_hz105 {c : ℝ} (hc : B (63 / 100) (127 / 200) c) : B (-124887872550732217759 / 1000000000000000000) (575738223485378181841 / 1000000000000000000) (((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) := badd (sGlobal57_hz103 hc) sGlobal57_hz104 (by norm_num) (by norm_num)

theorem sGlobal57_hz106 {c : ℝ} (hc : B (63 / 100) (127 / 200) c) : B (-21597699774871236907 / 250000000000000000) (614235296939502451857 / 1000000000000000000) ((((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) + (s3rs 12225 46 maskSlack)) := badd (sGlobal57_hz105 hc) sGlobal57_hz29 (by norm_num) (by norm_num)

theorem sGlobal57_hz107 {c : ℝ} (hc : B (63 / 100) (127 / 200) c) : B (-21597699774871236907 / 250000000000000000) (614235296939502451857 / 1000000000000000000) (s3U 12225 46 maskSlack c) := by
    convert (sGlobal57_hz106 hc) using 1 <;>
      norm_num [s3U] <;> ring

theorem sGlobal57_hz108 {c : ℝ} (hc : B (63 / 100) (127 / 200) c) : B (-1326081877553428332147 / 500000000000000000) (-515300219199415003859 / 200000000000000000) ((s3Cpp 12225 c) - (s3rpp 12225 46)) := bsub (sGlobal57_hz90 hc) sGlobal57_hz37 (by norm_num) (by norm_num)

theorem sGlobal57_hz109 {c : ℝ} (hc : B (63 / 100) (127 / 200) c) : B (-1326081877553428332147 / 500000000000000000) (-515300219199415003859 / 200000000000000000) (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ)) := bweaken (bmin (sGlobal57_hz108 hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem sGlobal57_hz110 {c : ℝ} (hc : B (63 / 100) (127 / 200) c) : B (-995072998125958645421 / 500000000000000000) (-964607186163355032761 / 500000000000000000) ((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) := bmul (sGlobal57_hz76 hc) (sGlobal57_hz109 hc) (by norm_num) (by norm_num)

theorem sGlobal57_hz111 {c : ℝ} (hc : B (63 / 100) (127 / 200) c) : B (-995080523688330833561 / 500000000000000000) (-964614711725727220899 / 500000000000000000) (((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) := bsub (sGlobal57_hz110 hc) sGlobal57_hz104 (by norm_num) (by norm_num)

theorem sGlobal57_hz112 {c : ℝ} (hc : B (63 / 100) (127 / 200) c) : B (-1014329060415392968569 / 500000000000000000) (-1967726496902701711929 / 1000000000000000000) ((((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) - (s3rs 12225 46 maskSlack)) := bsub (sGlobal57_hz111 hc) sGlobal57_hz29 (by norm_num) (by norm_num)

theorem sGlobal57_hz113 {c : ℝ} (hc : B (63 / 100) (127 / 200) c) : B (-1014329060415392968569 / 500000000000000000) (-1967726496902701711929 / 1000000000000000000) (s3L 12225 46 maskSlack c) := by
    convert (sGlobal57_hz112 hc) using 1 <;>
      norm_num [s3L] <;> ring

theorem sGlobal57_hz114 {c : ℝ} (hc : B (63 / 100) (127 / 200) c) : B 0 (614235296939502451857 / 1000000000000000000) |(s3U 12225 46 maskSlack c)| := bweaken (babs (sGlobal57_hz107 hc)) (by norm_num) (by norm_num)

theorem sGlobal57_hz115 {c : ℝ} (hc : B (63 / 100) (127 / 200) c) : B 0 (1014329060415392968569 / 500000000000000000) |(s3L 12225 46 maskSlack c)| := bweaken (babs (sGlobal57_hz113 hc)) (by norm_num) (by norm_num)

theorem sGlobal57_hz116 {c : ℝ} (hc : B (63 / 100) (127 / 200) c) : B 0 (1014329060415392968569 / 500000000000000000) (max |(s3U 12225 46 maskSlack c)| |(s3L 12225 46 maskSlack c)|) := bweaken (bmax (sGlobal57_hz114 hc) (sGlobal57_hz115 hc)) (by norm_num) (by norm_num)

theorem sGlobal57_hz117 {c : ℝ} (hc : B (63 / 100) (127 / 200) c) : B 0 (1014329060415392968569 / 500000000000000000) (s3nks 12225 46 maskSlack c) := by
    convert (sGlobal57_hz116 hc) using 1 <;>
      norm_num [s3nks] <;> ring

theorem sGlobal57 {c : ℝ} (hc : B (63 / 100) (127 / 200) c) :
    0 < s3am 12225 46 ∧ 0 ≤ s3dm 12225 46 c ∧
    s3dm 12225 46 c ^ 2 ≤ 2 * s3ap 12225 46 ^ 2 ∧ s3c1 12225 46 c < 1 ∧
    0 ≤ s3Cpa 12225 c - s3r1 12225 46 ∧
    s3e0 12225 46 ≤ (s3Cpa 12225 c - s3r1 12225 46) / s3ap 12225 46 ∧
    s3nks 12225 46 maskSlack c ≤ 12225 * (20743 / 125000) := by

  refine ⟨lt_of_lt_of_le (by norm_num) sGlobal57_hz14.1,
    le_trans (by norm_num) (sGlobal57_hz64 hc).1, ?_,
    lt_of_le_of_lt (sGlobal57_hz72 hc).2 (by norm_num), ?_, ?_,
    le_trans (sGlobal57_hz117 hc).2 (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (sGlobal57_hz64 hc).1) (sGlobal57_hz64 hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) sGlobal57_hz9.1 2
    nlinarith only [h1, h2]
  · linarith only [(sGlobal57_hz84 hc).1, sGlobal57_hz33.2]
  · have hap : 0 < s3ap 12225 46 := lt_of_lt_of_le (by norm_num) sGlobal57_hz9.1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul sGlobal57_hz16.2 sGlobal57_hz9.2 (le_trans (by norm_num) sGlobal57_hz9.1) (by norm_num)
    linarith only [h, (sGlobal57_hz84 hc).1, sGlobal57_hz33.2]

end BstLean.Part255
