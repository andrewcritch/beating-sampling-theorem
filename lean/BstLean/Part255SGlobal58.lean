import BstLean.Part255SGlobal54
import BstLean.Part255Numeric10
namespace BstLean.Part255
open Real BstLean.Part130 BstLean.Part182 BstLean.Part197 BstLean.Part246
theorem sGlobal58_hz0 : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal58_hz1 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) ((√(23 : ℝ)) / (12225 : ℝ)) := bdiv sGlobal58_hz0 (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal58_hz2 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) maskSlack := by
    convert sGlobal58_hz1 using 1 <;>
      norm_num [maskSlack] <;> ring

theorem sGlobal58_hz3 : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal58_hz4 : B (6395294793910793 / 500000000000000000) (12790589587821587 / 1000000000000000000) (√((2 / 12225) : ℝ)) := bsqrt (bpoint ((2 / 12225) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal58_hz5 : B (7230130686979 / 62500000000000000) (23136418198333 / 200000000000000000) (√((2 / 149450625) : ℝ)) := bsqrt (bpoint ((2 / 149450625) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal58_hz6 : B (2211334438749598093 / 20000000000000000) (110566721937479904651 / 1000000000000000000) (√(12225 : ℝ)) := bsqrt (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal58_hz7 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))) := bmul sGlobal58_hz3 sGlobal58_hz4 (by norm_num) (by norm_num)

theorem sGlobal58_hz8 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) ((√(12225 : ℝ)) + ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := badd sGlobal58_hz6 sGlobal58_hz7 (by norm_num) (by norm_num)

theorem sGlobal58_hz9 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) (s3ap 12225 46) := by
    convert sGlobal58_hz8 using 1 <;>
      norm_num [s3ap, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal58_hz10 : B (163599182004089 / 1000000000000000000) (16359918200409 / 100000000000000000) ((2 : ℝ) / (12225 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal58_hz11 : B (1222499983640081799591 / 100000000000000000) (12224999836400817995911 / 1000000000000000000) ((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ))) := bsub (bpoint (12225 : ℝ)) sGlobal58_hz10 (by norm_num) (by norm_num)

theorem sGlobal58_hz12 : B (110566721197658827907 / 1000000000000000000) (27641680299414706977 / 250000000000000000) (√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) := bsqrt sGlobal58_hz11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal58_hz13 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) ((√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) - ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bsub sGlobal58_hz12 sGlobal58_hz7 (by norm_num) (by norm_num)

theorem sGlobal58_hz14 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) (s3am 12225 46) := by
    convert sGlobal58_hz13 using 1 <;>
      norm_num [s3am, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal58_hz15 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√((2 / 12225) : ℝ)) * (√(92 : ℝ))) := bmul sGlobal58_hz4 sGlobal58_hz3 (by norm_num) (by norm_num)

theorem sGlobal58_hz16 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) (s3e0 12225 46) := by
    convert sGlobal58_hz15 using 1 <;>
      norm_num [s3e0, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal58_hz17 : B (250196148528560847 / 500000000000000000) (100078459411424339 / 200000000000000000) (((1 / 2) : ℝ) + maskSlack) := badd (bpoint ((1 / 2) : ℝ)) sGlobal58_hz2 (by norm_num) (by norm_num)

theorem sGlobal58_hz18 : B (59827153232297998295487 / 800000000000000) (23930861292919199366019 / 320000000000000) ((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack)) := bmul (bpoint (149450625 : ℝ)) sGlobal58_hz17 (by norm_num) (by norm_num)

theorem sGlobal58_hz19 : B (1729554180017180009583 / 200000000000000000) (8647770900085900056557 / 1000000000000000000) (√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) := bsqrt sGlobal58_hz18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal58_hz20 : B (4328681281566262743499 / 500000000000000000) (8657362563132525495641 / 1000000000000000000) ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))) := badd sGlobal58_hz19 sGlobal58_hz3 (by norm_num) (by norm_num)

theorem sGlobal58_hz21 : B (110732771457999278473 / 1000000000000000000) (55366385728999643621 / 500000000000000000) ((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ)))) := bmul sGlobal58_hz4 sGlobal58_hz20 (by norm_num) (by norm_num)

theorem sGlobal58_hz22 : B (209099159 / 15625000000000000) (13382346177 / 1000000000000000000) ((2 : ℝ) / (149450625 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (149450625 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal58_hz23 : B (2452349334953899930479 / 200000000000000000) (12261746674769501594427 / 1000000000000000000) (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2) := bsq sGlobal58_hz21 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal58_hz24 : B (82045469362091 / 500000000000000000) (32818187747289 / 200000000000000000) (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2)) := bmul sGlobal58_hz22 sGlobal58_hz23 (by norm_num) (by norm_num)

theorem sGlobal58_hz25 : B (82045469362091 / 250000000000000000) (32818187747289 / 100000000000000000) ((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) := bmul (bpoint (2 : ℝ)) sGlobal58_hz24 (by norm_num) (by norm_num)

theorem sGlobal58_hz26 : B (117258080744995992792057 / 1000000000000000000) (58629040372497996396029 / 500000000000000000) (√(13749457500 : ℝ)) := bsqrt (bpoint (13749457500 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal58_hz27 : B (117304080744995992792057 / 1000000000000000000) (58652040372497996396029 / 500000000000000000) ((√(13749457500 : ℝ)) + (46 : ℝ)) := badd sGlobal58_hz26 (bpoint (46 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal58_hz28 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal58_hz25 sGlobal58_hz27 (by norm_num) (by norm_num)

theorem sGlobal58_hz29 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (s3rs 12225 46 maskSlack) := by
    convert sGlobal58_hz28 using 1 <;>
      norm_num [s3rs, s3pp, s3K, mA, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal58_hz30 : B (490797546012267 / 1000000000000000000) (49079754601227 / 100000000000000000) ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (3 : ℝ)) sGlobal58_hz10 (by norm_num) (by norm_num)

theorem sGlobal58_hz31 : B (490797546012267 / 500000000000000000) (49079754601227 / 50000000000000000) ((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal58_hz30 (by norm_num) (by norm_num)

theorem sGlobal58_hz32 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal58_hz31 sGlobal58_hz27 (by norm_num) (by norm_num)

theorem sGlobal58_hz33 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (s3r1 12225 46) := by
    convert sGlobal58_hz32 using 1 <;>
      norm_num [s3r1, mA] <;> ring

theorem sGlobal58_hz34 : B (163599182004089 / 500000000000000000) (16359918200409 / 50000000000000000) ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (2 : ℝ)) sGlobal58_hz10 (by norm_num) (by norm_num)

theorem sGlobal58_hz35 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal58_hz34 (by norm_num) (by norm_num)

theorem sGlobal58_hz36 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal58_hz35 sGlobal58_hz27 (by norm_num) (by norm_num)

theorem sGlobal58_hz37 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (s3rpp 12225 46) := by
    convert sGlobal58_hz36 using 1 <;>
      norm_num [s3rpp, mA] <;> ring

theorem sGlobal58_hz38 {c : ℝ} (hc : B (127 / 200) (16 / 25) c) : B (127 / 200) (16 / 25) c := hc

theorem sGlobal58_hz39 : B (359499956852941657 / 500000000000000000) (718999913705883319 / 1000000000000000000) (kdot ((127 / 200))) := by
    constructor
    · apply bkdot_lower (q := (236242243372172581 / 500000000000000000)) (a := (55174237922480933 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (472484486744345161 / 1000000000000000000)) (a := (220696951689923729 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal58_hz40 : B (16129 / 40000) (16129 / 40000) (((127 / 200) : ℝ)^2) := bsq (bpoint ((127 / 200) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal58_hz41 : B (23871 / 40000) (23871 / 40000) ((1 : ℝ) - (((127 / 200) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal58_hz40 (by norm_num) (by norm_num)

theorem sGlobal58_hz42 : B (386256067913502169 / 500000000000000000) (772512135827004339 / 1000000000000000000) (√((1 : ℝ) - (((127 / 200) : ℝ)^2))) := bsqrt sGlobal58_hz41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal58_hz43 : B (24589825003069079 / 100000000000000000) (30737281253836349 / 125000000000000000) ((√((1 : ℝ) - (((127 / 200) : ℝ)^2))) / Real.pi) := bdiv sGlobal58_hz42 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal58_hz44 : B (7133827268800561 / 15625000000000000) (114141236300808977 / 250000000000000000) (((127 / 200) : ℝ) * (kdot ((127 / 200)))) := bmul (bpoint ((127 / 200) : ℝ)) sGlobal58_hz39 (by norm_num) (by norm_num)

theorem sGlobal58_hz45 : B (351231597616963347 / 500000000000000000) (7024631952339267 / 10000000000000000) (((√((1 : ℝ) - (((127 / 200) : ℝ)^2))) / Real.pi) + (((127 / 200) : ℝ) * (kdot ((127 / 200))))) := badd sGlobal58_hz43 sGlobal58_hz44 (by norm_num) (by norm_num)

theorem sGlobal58_hz46 : B (351231597616963347 / 500000000000000000) (7024631952339267 / 10000000000000000) (kappa ((127 / 200))) := by rw [kappa_eq]; exact sGlobal58_hz45

theorem sGlobal58_hz47 : B (5633325499112727 / 7812500000000000) (721065663886429061 / 1000000000000000000) (kdot ((16 / 25))) := by
    constructor
    · apply bkdot_lower (q := (468521285665818197 / 1000000000000000000)) (a := (438149030584170317 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (117130321416454549 / 250000000000000000)) (a := (54768628823021289 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal58_hz48 : B (256 / 625) (256 / 625) (((16 / 25) : ℝ)^2) := bsq (bpoint ((16 / 25) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal58_hz49 : B (369 / 625) (369 / 625) ((1 : ℝ) - (((16 / 25) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal58_hz48 (by norm_num) (by norm_num)

theorem sGlobal58_hz50 : B (384187454245970921 / 500000000000000000) (768374908491941843 / 1000000000000000000) (√((1 : ℝ) - (((16 / 25) : ℝ)^2))) := bsqrt sGlobal58_hz49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal58_hz51 : B (12229066483427529 / 50000000000000000) (244581329668550581 / 1000000000000000000) ((√((1 : ℝ) - (((16 / 25) : ℝ)^2))) / Real.pi) := bdiv sGlobal58_hz50 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal58_hz52 : B (92296404977462919 / 200000000000000000) (2307410124436573 / 5000000000000000) (((16 / 25) : ℝ) * (kdot ((16 / 25)))) := bmul (bpoint ((16 / 25) : ℝ)) sGlobal58_hz47 (by norm_num) (by norm_num)

theorem sGlobal58_hz53 : B (28242534182234607 / 40000000000000000) (706063354555865181 / 1000000000000000000) (((√((1 : ℝ) - (((16 / 25) : ℝ)^2))) / Real.pi) + (((16 / 25) : ℝ) * (kdot ((16 / 25))))) := badd sGlobal58_hz51 sGlobal58_hz52 (by norm_num) (by norm_num)

theorem sGlobal58_hz54 : B (28242534182234607 / 40000000000000000) (706063354555865181 / 1000000000000000000) (kappa ((16 / 25))) := by rw [kappa_eq]; exact sGlobal58_hz53

theorem sGlobal58_hz55 {c : ℝ} (hc : B (127 / 200) (16 / 25) c) : B (351231597616963347 / 500000000000000000) (706063354555865181 / 1000000000000000000) (kappa c) := bkappa (sGlobal58_hz38 hc) (by norm_num) (by norm_num) sGlobal58_hz46.1 sGlobal58_hz54.2

theorem sGlobal58_hz56 : B 24450 24450 ((2 : ℝ) * (12225 : ℝ)) := bmul (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal58_hz57 {c : ℝ} (hc : B (127 / 200) (16 / 25) c) : B (293936645444134819 / 1000000000000000000) (148768402383036653 / 500000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (sGlobal58_hz55 hc) (by norm_num) (by norm_num)

theorem sGlobal58_hz58 {c : ℝ} (hc : B (127 / 200) (16 / 25) c) : B (143735019622181926491 / 20000000000000000) (72747748765304923317 / 10000000000000000) (((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) := bmul sGlobal58_hz56 (sGlobal58_hz57 hc) (by norm_num) (by norm_num)

theorem sGlobal58_hz59 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (4 : ℝ)) sGlobal58_hz10 (by norm_num) (by norm_num)

theorem sGlobal58_hz60 {c : ℝ} (hc : B (127 / 200) (16 / 25) c) : B (718675032671236830819 / 100000000000000000) (454673388883360269709 / 62500000000000000) ((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bsub (sGlobal58_hz58 hc) sGlobal58_hz59 (by norm_num) (by norm_num)

theorem sGlobal58_hz61 {c : ℝ} (hc : B (127 / 200) (16 / 25) c) : B (42387351670965385721 / 500000000000000000) (17058457400519853941 / 200000000000000000) (√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) := bsqrt (sGlobal58_hz60 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal58_hz62 : B (30670756373515103 / 125000000000000000) (122683025494060423 / 500000000000000000) ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal58_hz7 (by norm_num) (by norm_num)

theorem sGlobal58_hz63 {c : ℝ} (hc : B (127 / 200) (16 / 25) c) : B (21132334322735662649 / 250000000000000000) (85046920951611148881 / 1000000000000000000) ((√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) - ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))))) := bsub (sGlobal58_hz61 hc) sGlobal58_hz62 (by norm_num) (by norm_num)

theorem sGlobal58_hz64 {c : ℝ} (hc : B (127 / 200) (16 / 25) c) : B (21132334322735662649 / 250000000000000000) (85046920951611148881 / 1000000000000000000) (s3dm 12225 46 c) := by
    convert (sGlobal58_hz63 hc) using 1 <;>
      norm_num [s3dm, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal58_hz65 : B (6126072185528622723889 / 500000000000000000) (2450428874211449090087 / 200000000000000000) ((s3ap 12225 46)^2) := bsq sGlobal58_hz9 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal58_hz66 : B (6126072185528622723889 / 250000000000000000) (2450428874211449090087 / 100000000000000000) ((2 : ℝ) * ((s3ap 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal58_hz65 (by norm_num) (by norm_num)

theorem sGlobal58_hz67 {c : ℝ} (hc : B (127 / 200) (16 / 25) c) : B (1786302215711486951113 / 250000000000000000) (1446595752669919081109 / 200000000000000000) ((s3dm 12225 46 c)^2) := bsq (sGlobal58_hz64 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal58_hz68 {c : ℝ} (hc : B (127 / 200) (16 / 25) c) : B (17271309978764895490011 / 1000000000000000000) (8679539939634271548209 / 500000000000000000) (((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) := bsub sGlobal58_hz66 (sGlobal58_hz67 hc) (by norm_num) (by norm_num)

theorem sGlobal58_hz69 : B (1524735695971823534271 / 125000000000000000) (609894278388729413841 / 50000000000000000) ((s3am 12225 46)^2) := bsq sGlobal58_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal58_hz70 : B (1524735695971823534271 / 62500000000000000) (609894278388729413841 / 25000000000000000) ((2 : ℝ) * ((s3am 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal58_hz69 (by norm_num) (by norm_num)

theorem sGlobal58_hz71 {c : ℝ} (hc : B (127 / 200) (16 / 25) c) : B (707963272929601479 / 1000000000000000000) (711561023540392813 / 1000000000000000000) ((((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) / ((2 : ℝ) * ((s3am 12225 46)^2))) := bdiv (sGlobal58_hz68 hc) sGlobal58_hz70 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal58_hz72 {c : ℝ} (hc : B (127 / 200) (16 / 25) c) : B (707963272929601479 / 1000000000000000000) (711561023540392813 / 1000000000000000000) (s3c1 12225 46 c) := by
    convert (sGlobal58_hz71 hc) using 1 <;>
      norm_num [s3c1] <;> ring

theorem sGlobal58_hz73 {c : ℝ} (hc : B (127 / 200) (16 / 25) c) : B (359499956852941657 / 500000000000000000) (721065663886429061 / 1000000000000000000) (kdot c) := bkdot (sGlobal58_hz38 hc) sGlobal58_hz39.1 sGlobal58_hz47.2

theorem sGlobal58_hz74 : B (750385790628427299 / 1000000000000000000) (750385790628427301 / 1000000000000000000) (kdot ((707963272929601479 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (413503769045976583 / 1000000000000000000)) (a := (196046541598339329 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (206751884522988291 / 500000000000000000)) (a := (765806803118513 / 1953125000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal58_hz75 : B (752011482438597161 / 1000000000000000000) (752011482438597163 / 1000000000000000000) (kdot ((711561023540392813 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (41051665254611963 / 100000000000000000)) (a := (389539452472763293 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (410516652546119629 / 1000000000000000000)) (a := (389539452472763291 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal58_hz76 {c : ℝ} (hc : B (127 / 200) (16 / 25) c) : B (750385790628427299 / 1000000000000000000) (752011482438597163 / 1000000000000000000) (kdot (s3c1 12225 46 c)) := bkdot (sGlobal58_hz72 hc) sGlobal58_hz74.1 sGlobal58_hz75.2

theorem sGlobal58_hz77 {c : ℝ} (hc : B (127 / 200) (16 / 25) c) : B (16129 / 40000) (256 / 625) (c^2) := bsq (sGlobal58_hz38 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal58_hz78 {c : ℝ} (hc : B (127 / 200) (16 / 25) c) : B (369 / 625) (23871 / 40000) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (sGlobal58_hz77 hc) (by norm_num) (by norm_num)

theorem sGlobal58_hz79 {c : ℝ} (hc : B (127 / 200) (16 / 25) c) : B (384187454245970921 / 500000000000000000) (772512135827004339 / 1000000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (sGlobal58_hz78 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal58_hz80 : B (39119999999999765769 / 1600000000000000) (3912000000000000489 / 160000000000000) ((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (149450625 : ℝ)) sGlobal58_hz10 (by norm_num) (by norm_num)

theorem sGlobal58_hz81 {c : ℝ} (hc : B (127 / 200) (16 / 25) c) : B (138115373224868043 / 250000000000000000) (111406395216084429 / 200000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (sGlobal58_hz79 hc) (sGlobal58_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal58_hz82 {c : ℝ} (hc : B (127 / 200) (16 / 25) c) : B (2701536700278402745629 / 200000000000000000) (13619431815166323147679 / 1000000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) := bmul sGlobal58_hz80 (sGlobal58_hz81 hc) (by norm_num) (by norm_num)

theorem sGlobal58_hz83 {c : ℝ} (hc : B (127 / 200) (16 / 25) c) : B (844230218837000858009 / 125000000000000000) (85121448844789519673 / 12500000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) / (2 : ℝ)) := bdiv (sGlobal58_hz82 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal58_hz84 {c : ℝ} (hc : B (127 / 200) (16 / 25) c) : B (844230218837000858009 / 125000000000000000) (85121448844789519673 / 12500000000000000) (s3Cpa 12225 c) := by
    convert (sGlobal58_hz83 hc) using 1 <;>
      norm_num [s3Cpa, mA] <;> ring

theorem sGlobal58_hz85 {c : ℝ} (hc : B (127 / 200) (16 / 25) c) : B (12229066483427529 / 50000000000000000) (30737281253836349 / 125000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (sGlobal58_hz79 hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal58_hz86 {c : ℝ} (hc : B (127 / 200) (16 / 25) c) : B (7133827268800561 / 15625000000000000) (2307410124436573 / 5000000000000000) (c * (kdot c)) := bmul (sGlobal58_hz38 hc) (sGlobal58_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal58_hz87 {c : ℝ} (hc : B (127 / 200) (16 / 25) c) : B (-10845034760938201 / 50000000000000000) (-26333336896568139 / 125000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (sGlobal58_hz85 hc) (sGlobal58_hz86 hc) (by norm_num) (by norm_num)

theorem sGlobal58_hz88 {c : ℝ} (hc : B (127 / 200) (16 / 25) c) : B (-5303221998098780951903 / 1000000000000000000) (-257540034848434857399 / 50000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) := bmul sGlobal58_hz80 (sGlobal58_hz87 hc) (by norm_num) (by norm_num)

theorem sGlobal58_hz89 {c : ℝ} (hc : B (127 / 200) (16 / 25) c) : B (-165725687440586904747 / 62500000000000000) (-257540034848434857399 / 100000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) / (2 : ℝ)) := bdiv (sGlobal58_hz88 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal58_hz90 {c : ℝ} (hc : B (127 / 200) (16 / 25) c) : B (-165725687440586904747 / 62500000000000000) (-257540034848434857399 / 100000000000000000) (s3Cpp 12225 c) := by
    convert (sGlobal58_hz89 hc) using 1 <;>
      norm_num [s3Cpp, mA] <;> ring

theorem sGlobal58_hz91 {c : ℝ} (hc : B (127 / 200) (16 / 25) c) : B (6868986860629744572473 / 1000000000000000000) (3462430508758449993033 / 500000000000000000) ((s3Cpa 12225 c) + (s3r1 12225 46)) := badd (sGlobal58_hz84 hc) sGlobal58_hz33 (by norm_num) (by norm_num)

theorem sGlobal58_hz92 {c : ℝ} (hc : B (127 / 200) (16 / 25) c) : B (31097137402392339689 / 500000000000000000) (31350089747362090121 / 500000000000000000) (((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) := bdiv (sGlobal58_hz91 hc) sGlobal58_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal58_hz93 {c : ℝ} (hc : B (127 / 200) (16 / 25) c) : B (6231695783027873979 / 100000000000000000) (12564572504043648133 / 200000000000000000) ((((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) + (s3e0 12225 46)) := badd (sGlobal58_hz92 hc) sGlobal58_hz16 (by norm_num) (by norm_num)

theorem sGlobal58_hz94 {c : ℝ} (hc : B (127 / 200) (16 / 25) c) : B (6231695783027873979 / 100000000000000000) (12564572504043648133 / 200000000000000000) (s3Lam 12225 46 c) := by
    convert (sGlobal58_hz93 hc) using 1 <;>
      norm_num [s3Lam] <;> ring

theorem sGlobal58_hz95 {c : ℝ} (hc : B (127 / 200) (16 / 25) c) : B (-160927974526681166897 / 62500000000000000) (-624659235465464074793 / 250000000000000000) ((s3Cpp 12225 c) + (s3rpp 12225 46)) := badd (sGlobal58_hz90 hc) sGlobal58_hz37 (by norm_num) (by norm_num)

theorem sGlobal58_hz96 {c : ℝ} (hc : B (127 / 200) (16 / 25) c) : B (-242039369379300611869 / 125000000000000000) (-624659235465464074793 / 500000000000000000) (if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) := bweaken (bfirst (sGlobal58_hz95 hc) (sGlobal58_hz76 hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem sGlobal58_hz97 {c : ℝ} (hc : B (127 / 200) (16 / 25) c) : B (1941701616610369370189 / 500000000000000000) (986678013808560439247 / 250000000000000000) ((s3Lam 12225 46 c)^2) := bsq (sGlobal58_hz94 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal58_hz98 {c : ℝ} (hc : B (127 / 200) (16 / 25) c) : B (250605997908596697 / 500000000000000000) (101263818044370291 / 200000000000000000) ((s3c1 12225 46 c)^2) := bsq (sGlobal58_hz72 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal58_hz99 {c : ℝ} (hc : B (127 / 200) (16 / 25) c) : B (98736181955629709 / 200000000000000000) (249394002091403303 / 500000000000000000) ((1 : ℝ) - ((s3c1 12225 46 c)^2)) := bsub (bpoint (1 : ℝ)) (sGlobal58_hz98 hc) (by norm_num) (by norm_num)

theorem sGlobal58_hz100 {c : ℝ} (hc : B (127 / 200) (16 / 25) c) : B (175656075503053079 / 250000000000000000) (706249250748492197 / 1000000000000000000) (√((1 : ℝ) - ((s3c1 12225 46 c)^2))) := bsqrt (sGlobal58_hz99 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal58_hz101 {c : ℝ} (hc : B (127 / 200) (16 / 25) c) : B (220735934543522239 / 100000000000000000) (221874745775475887 / 100000000000000000) (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))) := bmul pi_mem (sGlobal58_hz100 hc) (by norm_num) (by norm_num)

theorem sGlobal58_hz102 {c : ℝ} (hc : B (127 / 200) (16 / 25) c) : B (1750268251417181569187 / 1000000000000000000) (1787978954761474635671 / 1000000000000000000) (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2))))) := bdiv (sGlobal58_hz97 hc) (sGlobal58_hz101 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal58_hz103 {c : ℝ} (hc : B (127 / 200) (16 / 25) c) : B (-37209340723444665153 / 200000000000000000) (107732096766109297217 / 200000000000000000) ((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) := badd (sGlobal58_hz96 hc) (sGlobal58_hz102 hc) (by norm_num) (by norm_num)

theorem sGlobal58_hz104 : B (3762781186094069 / 250000000000000000) (376278118609407 / 25000000000000000) ((s3e0 12225 46)^2) := bsq sGlobal58_hz16 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal58_hz105 {c : ℝ} (hc : B (127 / 200) (16 / 25) c) : B (-186031652492478949489 / 1000000000000000000) (107735106991058172473 / 200000000000000000) (((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) := badd (sGlobal58_hz103 hc) sGlobal58_hz104 (by norm_num) (by norm_num)

theorem sGlobal58_hz106 {c : ℝ} (hc : B (127 / 200) (16 / 25) c) : B (-73767289520615839679 / 500000000000000000) (577172608409415132381 / 1000000000000000000) ((((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) + (s3rs 12225 46 maskSlack)) := badd (sGlobal58_hz105 hc) sGlobal58_hz29 (by norm_num) (by norm_num)

theorem sGlobal58_hz107 {c : ℝ} (hc : B (127 / 200) (16 / 25) c) : B (-73767289520615839679 / 500000000000000000) (577172608409415132381 / 1000000000000000000) (s3U 12225 46 maskSlack c) := by
    convert (sGlobal58_hz106 hc) using 1 <;>
      norm_num [s3U] <;> ring

theorem sGlobal58_hz108 {c : ℝ} (hc : B (127 / 200) (16 / 25) c) : B (-272837440567188275077 / 100000000000000000) (-265216375510684037959 / 100000000000000000) ((s3Cpp 12225 c) - (s3rpp 12225 46)) := bsub (sGlobal58_hz90 hc) sGlobal58_hz37 (by norm_num) (by norm_num)

theorem sGlobal58_hz109 {c : ℝ} (hc : B (127 / 200) (16 / 25) c) : B (-272837440567188275077 / 100000000000000000) (-265216375510684037959 / 100000000000000000) (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ)) := bweaken (bmin (sGlobal58_hz108 hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem sGlobal58_hz110 {c : ℝ} (hc : B (127 / 200) (16 / 25) c) : B (-2051768881456839027067 / 1000000000000000000) (-199014599625190505777 / 100000000000000000) ((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) := bmul (sGlobal58_hz76 hc) (sGlobal58_hz109 hc) (by norm_num) (by norm_num)

theorem sGlobal58_hz111 {c : ℝ} (hc : B (127 / 200) (16 / 25) c) : B (-2051783932581583403347 / 1000000000000000000) (-995080523688324717023 / 500000000000000000) (((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) := bsub (sGlobal58_hz110 hc) sGlobal58_hz104 (by norm_num) (by norm_num)

theorem sGlobal58_hz112 {c : ℝ} (hc : B (127 / 200) (16 / 25) c) : B (-2090281006035707673363 / 1000000000000000000) (-2028658120827896704177 / 1000000000000000000) ((((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) - (s3rs 12225 46 maskSlack)) := bsub (sGlobal58_hz111 hc) sGlobal58_hz29 (by norm_num) (by norm_num)

theorem sGlobal58_hz113 {c : ℝ} (hc : B (127 / 200) (16 / 25) c) : B (-2090281006035707673363 / 1000000000000000000) (-2028658120827896704177 / 1000000000000000000) (s3L 12225 46 maskSlack c) := by
    convert (sGlobal58_hz112 hc) using 1 <;>
      norm_num [s3L] <;> ring

theorem sGlobal58_hz114 {c : ℝ} (hc : B (127 / 200) (16 / 25) c) : B 0 (577172608409415132381 / 1000000000000000000) |(s3U 12225 46 maskSlack c)| := bweaken (babs (sGlobal58_hz107 hc)) (by norm_num) (by norm_num)

theorem sGlobal58_hz115 {c : ℝ} (hc : B (127 / 200) (16 / 25) c) : B 0 (2090281006035707673363 / 1000000000000000000) |(s3L 12225 46 maskSlack c)| := bweaken (babs (sGlobal58_hz113 hc)) (by norm_num) (by norm_num)

theorem sGlobal58_hz116 {c : ℝ} (hc : B (127 / 200) (16 / 25) c) : B 0 (2090281006035707673363 / 1000000000000000000) (max |(s3U 12225 46 maskSlack c)| |(s3L 12225 46 maskSlack c)|) := bweaken (bmax (sGlobal58_hz114 hc) (sGlobal58_hz115 hc)) (by norm_num) (by norm_num)

theorem sGlobal58_hz117 {c : ℝ} (hc : B (127 / 200) (16 / 25) c) : B 0 (2090281006035707673363 / 1000000000000000000) (s3nks 12225 46 maskSlack c) := by
    convert (sGlobal58_hz116 hc) using 1 <;>
      norm_num [s3nks] <;> ring

theorem sGlobal58 {c : ℝ} (hc : B (127 / 200) (16 / 25) c) :
    0 < s3am 12225 46 ∧ 0 ≤ s3dm 12225 46 c ∧
    s3dm 12225 46 c ^ 2 ≤ 2 * s3ap 12225 46 ^ 2 ∧ s3c1 12225 46 c < 1 ∧
    0 ≤ s3Cpa 12225 c - s3r1 12225 46 ∧
    s3e0 12225 46 ≤ (s3Cpa 12225 c - s3r1 12225 46) / s3ap 12225 46 ∧
    s3nks 12225 46 maskSlack c ≤ 12225 * (34197 / 200000) := by

  refine ⟨lt_of_lt_of_le (by norm_num) sGlobal58_hz14.1,
    le_trans (by norm_num) (sGlobal58_hz64 hc).1, ?_,
    lt_of_le_of_lt (sGlobal58_hz72 hc).2 (by norm_num), ?_, ?_,
    le_trans (sGlobal58_hz117 hc).2 (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (sGlobal58_hz64 hc).1) (sGlobal58_hz64 hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) sGlobal58_hz9.1 2
    nlinarith only [h1, h2]
  · linarith only [(sGlobal58_hz84 hc).1, sGlobal58_hz33.2]
  · have hap : 0 < s3ap 12225 46 := lt_of_lt_of_le (by norm_num) sGlobal58_hz9.1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul sGlobal58_hz16.2 sGlobal58_hz9.2 (le_trans (by norm_num) sGlobal58_hz9.1) (by norm_num)
    linarith only [h, (sGlobal58_hz84 hc).1, sGlobal58_hz33.2]

end BstLean.Part255
