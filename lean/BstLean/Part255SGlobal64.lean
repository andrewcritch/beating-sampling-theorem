import BstLean.Part255SGlobal60
import BstLean.Part255Numeric10
namespace BstLean.Part255
open Real BstLean.Part130 BstLean.Part182 BstLean.Part197 BstLean.Part246
theorem sGlobal64_hz0 : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal64_hz1 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) ((√(23 : ℝ)) / (12225 : ℝ)) := bdiv sGlobal64_hz0 (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal64_hz2 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) maskSlack := by
    convert sGlobal64_hz1 using 1 <;>
      norm_num [maskSlack] <;> ring

theorem sGlobal64_hz3 : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal64_hz4 : B (6395294793910793 / 500000000000000000) (12790589587821587 / 1000000000000000000) (√((2 / 12225) : ℝ)) := bsqrt (bpoint ((2 / 12225) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal64_hz5 : B (7230130686979 / 62500000000000000) (23136418198333 / 200000000000000000) (√((2 / 149450625) : ℝ)) := bsqrt (bpoint ((2 / 149450625) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal64_hz6 : B (2211334438749598093 / 20000000000000000) (110566721937479904651 / 1000000000000000000) (√(12225 : ℝ)) := bsqrt (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal64_hz7 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))) := bmul sGlobal64_hz3 sGlobal64_hz4 (by norm_num) (by norm_num)

theorem sGlobal64_hz8 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) ((√(12225 : ℝ)) + ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := badd sGlobal64_hz6 sGlobal64_hz7 (by norm_num) (by norm_num)

theorem sGlobal64_hz9 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) (s3ap 12225 46) := by
    convert sGlobal64_hz8 using 1 <;>
      norm_num [s3ap, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal64_hz10 : B (163599182004089 / 1000000000000000000) (16359918200409 / 100000000000000000) ((2 : ℝ) / (12225 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal64_hz11 : B (1222499983640081799591 / 100000000000000000) (12224999836400817995911 / 1000000000000000000) ((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ))) := bsub (bpoint (12225 : ℝ)) sGlobal64_hz10 (by norm_num) (by norm_num)

theorem sGlobal64_hz12 : B (110566721197658827907 / 1000000000000000000) (27641680299414706977 / 250000000000000000) (√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) := bsqrt sGlobal64_hz11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal64_hz13 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) ((√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) - ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bsub sGlobal64_hz12 sGlobal64_hz7 (by norm_num) (by norm_num)

theorem sGlobal64_hz14 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) (s3am 12225 46) := by
    convert sGlobal64_hz13 using 1 <;>
      norm_num [s3am, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal64_hz15 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√((2 / 12225) : ℝ)) * (√(92 : ℝ))) := bmul sGlobal64_hz4 sGlobal64_hz3 (by norm_num) (by norm_num)

theorem sGlobal64_hz16 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) (s3e0 12225 46) := by
    convert sGlobal64_hz15 using 1 <;>
      norm_num [s3e0, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal64_hz17 : B (250196148528560847 / 500000000000000000) (100078459411424339 / 200000000000000000) (((1 / 2) : ℝ) + maskSlack) := badd (bpoint ((1 / 2) : ℝ)) sGlobal64_hz2 (by norm_num) (by norm_num)

theorem sGlobal64_hz18 : B (59827153232297998295487 / 800000000000000) (23930861292919199366019 / 320000000000000) ((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack)) := bmul (bpoint (149450625 : ℝ)) sGlobal64_hz17 (by norm_num) (by norm_num)

theorem sGlobal64_hz19 : B (1729554180017180009583 / 200000000000000000) (8647770900085900056557 / 1000000000000000000) (√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) := bsqrt sGlobal64_hz18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal64_hz20 : B (4328681281566262743499 / 500000000000000000) (8657362563132525495641 / 1000000000000000000) ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))) := badd sGlobal64_hz19 sGlobal64_hz3 (by norm_num) (by norm_num)

theorem sGlobal64_hz21 : B (110732771457999278473 / 1000000000000000000) (55366385728999643621 / 500000000000000000) ((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ)))) := bmul sGlobal64_hz4 sGlobal64_hz20 (by norm_num) (by norm_num)

theorem sGlobal64_hz22 : B (209099159 / 15625000000000000) (13382346177 / 1000000000000000000) ((2 : ℝ) / (149450625 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (149450625 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal64_hz23 : B (2452349334953899930479 / 200000000000000000) (12261746674769501594427 / 1000000000000000000) (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2) := bsq sGlobal64_hz21 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal64_hz24 : B (82045469362091 / 500000000000000000) (32818187747289 / 200000000000000000) (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2)) := bmul sGlobal64_hz22 sGlobal64_hz23 (by norm_num) (by norm_num)

theorem sGlobal64_hz25 : B (82045469362091 / 250000000000000000) (32818187747289 / 100000000000000000) ((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) := bmul (bpoint (2 : ℝ)) sGlobal64_hz24 (by norm_num) (by norm_num)

theorem sGlobal64_hz26 : B (117258080744995992792057 / 1000000000000000000) (58629040372497996396029 / 500000000000000000) (√(13749457500 : ℝ)) := bsqrt (bpoint (13749457500 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal64_hz27 : B (117304080744995992792057 / 1000000000000000000) (58652040372497996396029 / 500000000000000000) ((√(13749457500 : ℝ)) + (46 : ℝ)) := badd sGlobal64_hz26 (bpoint (46 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal64_hz28 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal64_hz25 sGlobal64_hz27 (by norm_num) (by norm_num)

theorem sGlobal64_hz29 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (s3rs 12225 46 maskSlack) := by
    convert sGlobal64_hz28 using 1 <;>
      norm_num [s3rs, s3pp, s3K, mA, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal64_hz30 : B (490797546012267 / 1000000000000000000) (49079754601227 / 100000000000000000) ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (3 : ℝ)) sGlobal64_hz10 (by norm_num) (by norm_num)

theorem sGlobal64_hz31 : B (490797546012267 / 500000000000000000) (49079754601227 / 50000000000000000) ((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal64_hz30 (by norm_num) (by norm_num)

theorem sGlobal64_hz32 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal64_hz31 sGlobal64_hz27 (by norm_num) (by norm_num)

theorem sGlobal64_hz33 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (s3r1 12225 46) := by
    convert sGlobal64_hz32 using 1 <;>
      norm_num [s3r1, mA] <;> ring

theorem sGlobal64_hz34 : B (163599182004089 / 500000000000000000) (16359918200409 / 50000000000000000) ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (2 : ℝ)) sGlobal64_hz10 (by norm_num) (by norm_num)

theorem sGlobal64_hz35 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal64_hz34 (by norm_num) (by norm_num)

theorem sGlobal64_hz36 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal64_hz35 sGlobal64_hz27 (by norm_num) (by norm_num)

theorem sGlobal64_hz37 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (s3rpp 12225 46) := by
    convert sGlobal64_hz36 using 1 <;>
      norm_num [s3rpp, mA] <;> ring

theorem sGlobal64_hz38 {c : ℝ} (hc : B (133 / 200) (67 / 100) c) : B (133 / 200) (67 / 100) c := hc

theorem sGlobal64_hz39 : B (731568474407441717 / 1000000000000000000) (731568474407441719 / 1000000000000000000) (kdot ((133 / 200))) := by
    constructor
    · apply bkdot_lower (q := (448554568810976667 / 1000000000000000000)) (a := (84330250879348167 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (224277284405488333 / 500000000000000000)) (a := (421651254396740833 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal64_hz40 : B (17689 / 40000) (17689 / 40000) (((133 / 200) : ℝ)^2) := bsq (bpoint ((133 / 200) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal64_hz41 : B (22311 / 40000) (22311 / 40000) ((1 : ℝ) - (((133 / 200) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal64_hz40 (by norm_num) (by norm_num)

theorem sGlobal64_hz42 : B (746843357070276149 / 1000000000000000000) (14936867141405523 / 20000000000000000) (√((1 : ℝ) - (((133 / 200) : ℝ)^2))) := bsqrt sGlobal64_hz41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal64_hz43 : B (237727623986159737 / 1000000000000000000) (118863811993079869 / 500000000000000000) ((√((1 : ℝ) - (((133 / 200) : ℝ)^2))) / Real.pi) := bdiv sGlobal64_hz42 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal64_hz44 : B (486493035480948741 / 1000000000000000000) (60811629435118593 / 125000000000000000) (((133 / 200) : ℝ) * (kdot ((133 / 200)))) := bmul (bpoint ((133 / 200) : ℝ)) sGlobal64_hz39 (by norm_num) (by norm_num)

theorem sGlobal64_hz45 : B (362110329733554239 / 500000000000000000) (362110329733554241 / 500000000000000000) (((√((1 : ℝ) - (((133 / 200) : ℝ)^2))) / Real.pi) + (((133 / 200) : ℝ) * (kdot ((133 / 200))))) := badd sGlobal64_hz43 sGlobal64_hz44 (by norm_num) (by norm_num)

theorem sGlobal64_hz46 : B (362110329733554239 / 500000000000000000) (362110329733554241 / 500000000000000000) (kappa ((133 / 200))) := by rw [kappa_eq]; exact sGlobal64_hz45

theorem sGlobal64_hz47 : B (73370591556941763 / 100000000000000000) (22928309861544301 / 31250000000000000) (kdot ((67 / 100))) := by
    constructor
    · apply bkdot_lower (q := (222263801831945679 / 500000000000000000)) (a := (52286721208846107 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (444527603663891357 / 1000000000000000000)) (a := (209146884835384427 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal64_hz48 : B (4489 / 10000) (4489 / 10000) (((67 / 100) : ℝ)^2) := bsq (bpoint ((67 / 100) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal64_hz49 : B (5511 / 10000) (5511 / 10000) ((1 : ℝ) - (((67 / 100) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal64_hz48 (by norm_num) (by norm_num)

theorem sGlobal64_hz50 : B (371180549059349283 / 500000000000000000) (742361098118698567 / 1000000000000000000) (√((1 : ℝ) - (((67 / 100) : ℝ)^2))) := bsqrt sGlobal64_hz49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal64_hz51 : B (236300876649436799 / 1000000000000000000) (236300876649436801 / 1000000000000000000) ((√((1 : ℝ) - (((67 / 100) : ℝ)^2))) / Real.pi) := bdiv sGlobal64_hz50 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal64_hz52 : B (122895740857877453 / 250000000000000000) (245791481715754907 / 500000000000000000) (((67 / 100) : ℝ) * (kdot ((67 / 100)))) := bmul (bpoint ((67 / 100) : ℝ)) sGlobal64_hz47 (by norm_num) (by norm_num)

theorem sGlobal64_hz53 : B (727883840080946611 / 1000000000000000000) (145576768016189323 / 200000000000000000) (((√((1 : ℝ) - (((67 / 100) : ℝ)^2))) / Real.pi) + (((67 / 100) : ℝ) * (kdot ((67 / 100))))) := badd sGlobal64_hz51 sGlobal64_hz52 (by norm_num) (by norm_num)

theorem sGlobal64_hz54 : B (727883840080946611 / 1000000000000000000) (145576768016189323 / 200000000000000000) (kappa ((67 / 100))) := by rw [kappa_eq]; exact sGlobal64_hz53

theorem sGlobal64_hz55 {c : ℝ} (hc : B (133 / 200) (67 / 100) c) : B (362110329733554239 / 500000000000000000) (145576768016189323 / 200000000000000000) (kappa c) := bkappa (sGlobal64_hz38 hc) (by norm_num) (by norm_num) sGlobal64_hz46.1 sGlobal64_hz54.2

theorem sGlobal64_hz56 : B 24450 24450 ((2 : ℝ) * (12225 : ℝ)) := bmul (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal64_hz57 {c : ℝ} (hc : B (133 / 200) (67 / 100) c) : B (54423231983810677 / 200000000000000000) (137889670266445761 / 500000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (sGlobal64_hz55 hc) (by norm_num) (by norm_num)

theorem sGlobal64_hz58 {c : ℝ} (hc : B (133 / 200) (67 / 100) c) : B (26612960440083421053 / 4000000000000000) (67428048760291977129 / 10000000000000000) (((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) := bmul sGlobal64_hz56 (sGlobal64_hz57 hc) (by norm_num) (by norm_num)

theorem sGlobal64_hz59 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (4 : ℝ)) sGlobal64_hz10 (by norm_num) (by norm_num)

theorem sGlobal64_hz60 {c : ℝ} (hc : B (133 / 200) (67 / 100) c) : B (665323945562412724689 / 100000000000000000) (210712631926014678017 / 31250000000000000) ((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bsub (sGlobal64_hz58 hc) sGlobal64_hz59 (by norm_num) (by norm_num)

theorem sGlobal64_hz61 {c : ℝ} (hc : B (133 / 200) (67 / 100) c) : B (81567392109985515013 / 1000000000000000000) (41057289917968494967 / 500000000000000000) (√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) := bsqrt (sGlobal64_hz60 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal64_hz62 : B (30670756373515103 / 125000000000000000) (122683025494060423 / 500000000000000000) ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal64_hz7 (by norm_num) (by norm_num)

theorem sGlobal64_hz63 {c : ℝ} (hc : B (133 / 200) (67 / 100) c) : B (81322026058997394167 / 1000000000000000000) (8186921378494886911 / 100000000000000000) ((√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) - ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))))) := bsub (sGlobal64_hz61 hc) sGlobal64_hz62 (by norm_num) (by norm_num)

theorem sGlobal64_hz64 {c : ℝ} (hc : B (133 / 200) (67 / 100) c) : B (81322026058997394167 / 1000000000000000000) (8186921378494886911 / 100000000000000000) (s3dm 12225 46 c) := by
    convert (sGlobal64_hz63 hc) using 1 <;>
      norm_num [s3dm, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal64_hz65 : B (6126072185528622723889 / 500000000000000000) (2450428874211449090087 / 200000000000000000) ((s3ap 12225 46)^2) := bsq sGlobal64_hz9 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal64_hz66 : B (6126072185528622723889 / 250000000000000000) (2450428874211449090087 / 100000000000000000) ((2 : ℝ) * ((s3ap 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal64_hz65 (by norm_num) (by norm_num)

theorem sGlobal64_hz67 {c : ℝ} (hc : B (133 / 200) (67 / 100) c) : B (3306635961170125624121 / 500000000000000000) (6702568165765661934697 / 1000000000000000000) ((s3dm 12225 46 c)^2) := bsq (sGlobal64_hz64 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal64_hz68 {c : ℝ} (hc : B (133 / 200) (67 / 100) c) : B (17801720576348828960859 / 1000000000000000000) (4472754204943559913157 / 250000000000000000) (((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) := bsub sGlobal64_hz66 (sGlobal64_hz67 hc) (by norm_num) (by norm_num)

theorem sGlobal64_hz69 : B (1524735695971823534271 / 125000000000000000) (609894278388729413841 / 50000000000000000) ((s3am 12225 46)^2) := bsq sGlobal64_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal64_hz70 : B (1524735695971823534271 / 62500000000000000) (609894278388729413841 / 25000000000000000) ((2 : ℝ) * ((s3am 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal64_hz69 (by norm_num) (by norm_num)

theorem sGlobal64_hz71 {c : ℝ} (hc : B (133 / 200) (67 / 100) c) : B (729705180354328323 / 1000000000000000000) (733365496846447299 / 1000000000000000000) ((((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) / ((2 : ℝ) * ((s3am 12225 46)^2))) := bdiv (sGlobal64_hz68 hc) sGlobal64_hz70 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal64_hz72 {c : ℝ} (hc : B (133 / 200) (67 / 100) c) : B (729705180354328323 / 1000000000000000000) (733365496846447299 / 1000000000000000000) (s3c1 12225 46 c) := by
    convert (sGlobal64_hz71 hc) using 1 <;>
      norm_num [s3c1] <;> ring

theorem sGlobal64_hz73 {c : ℝ} (hc : B (133 / 200) (67 / 100) c) : B (731568474407441717 / 1000000000000000000) (22928309861544301 / 31250000000000000) (kdot c) := bkdot (sGlobal64_hz38 hc) sGlobal64_hz39.1 sGlobal64_hz47.2

theorem sGlobal64_hz74 : B (47521418047280081 / 62500000000000000) (380171344378240649 / 500000000000000000) (kdot ((729705180354328323 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (395305464717484951 / 1000000000000000000)) (a := (376452824190860457 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (7906109294349699 / 20000000000000000)) (a := (75290564838172091 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal64_hz75 : B (762051569853086559 / 1000000000000000000) (762051569853086561 / 1000000000000000000) (kdot ((733365496846447299 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (24512811033595607 / 62500000000000000)) (a := (14950740801655347 / 40000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (392204976537529711 / 1000000000000000000)) (a := (373768520041383673 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal64_hz76 {c : ℝ} (hc : B (133 / 200) (67 / 100) c) : B (47521418047280081 / 62500000000000000) (762051569853086561 / 1000000000000000000) (kdot (s3c1 12225 46 c)) := bkdot (sGlobal64_hz72 hc) sGlobal64_hz74.1 sGlobal64_hz75.2

theorem sGlobal64_hz77 {c : ℝ} (hc : B (133 / 200) (67 / 100) c) : B (17689 / 40000) (4489 / 10000) (c^2) := bsq (sGlobal64_hz38 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal64_hz78 {c : ℝ} (hc : B (133 / 200) (67 / 100) c) : B (5511 / 10000) (22311 / 40000) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (sGlobal64_hz77 hc) (by norm_num) (by norm_num)

theorem sGlobal64_hz79 {c : ℝ} (hc : B (133 / 200) (67 / 100) c) : B (371180549059349283 / 500000000000000000) (14936867141405523 / 20000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (sGlobal64_hz78 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal64_hz80 : B (39119999999999765769 / 1600000000000000) (3912000000000000489 / 160000000000000) ((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (149450625 : ℝ)) sGlobal64_hz10 (by norm_num) (by norm_num)

theorem sGlobal64_hz81 {c : ℝ} (hc : B (133 / 200) (67 / 100) c) : B (543087976010129461 / 1000000000000000000) (273981694543092229 / 500000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (sGlobal64_hz79 hc) (sGlobal64_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal64_hz82 {c : ℝ} (hc : B (133 / 200) (67 / 100) c) : B (531140040537903432657 / 40000000000000000) (6698852431578605836407 / 500000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) := bmul sGlobal64_hz80 (sGlobal64_hz81 hc) (by norm_num) (by norm_num)

theorem sGlobal64_hz83 {c : ℝ} (hc : B (133 / 200) (67 / 100) c) : B (1659812626680948227053 / 250000000000000000) (6698852431578605836407 / 1000000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) / (2 : ℝ)) := bdiv (sGlobal64_hz82 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal64_hz84 {c : ℝ} (hc : B (133 / 200) (67 / 100) c) : B (1659812626680948227053 / 250000000000000000) (6698852431578605836407 / 1000000000000000000) (s3Cpa 12225 c) := by
    convert (sGlobal64_hz83 hc) using 1 <;>
      norm_num [s3Cpa, mA] <;> ring

theorem sGlobal64_hz85 {c : ℝ} (hc : B (133 / 200) (67 / 100) c) : B (236300876649436799 / 1000000000000000000) (118863811993079869 / 500000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (sGlobal64_hz79 hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal64_hz86 {c : ℝ} (hc : B (133 / 200) (67 / 100) c) : B (486493035480948741 / 1000000000000000000) (245791481715754907 / 500000000000000000) (c * (kdot c)) := bmul (sGlobal64_hz38 hc) (sGlobal64_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal64_hz87 {c : ℝ} (hc : B (133 / 200) (67 / 100) c) : B (-51056417356414603 / 200000000000000000) (-248765411494789003 / 1000000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (sGlobal64_hz85 hc) (sGlobal64_hz86 hc) (by norm_num) (by norm_num)

theorem sGlobal64_hz88 {c : ℝ} (hc : B (133 / 200) (67 / 100) c) : B (-1560411755455421499239 / 250000000000000000) (-6082314311047554705493 / 1000000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) := bmul sGlobal64_hz80 (sGlobal64_hz87 hc) (by norm_num) (by norm_num)

theorem sGlobal64_hz89 {c : ℝ} (hc : B (133 / 200) (67 / 100) c) : B (-1560411755455421499239 / 500000000000000000) (-1520578577761888676373 / 500000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) / (2 : ℝ)) := bdiv (sGlobal64_hz88 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal64_hz90 {c : ℝ} (hc : B (133 / 200) (67 / 100) c) : B (-1560411755455421499239 / 500000000000000000) (-1520578577761888676373 / 500000000000000000) (s3Cpp 12225 c) := by
    convert (sGlobal64_hz89 hc) using 1 <;>
      norm_num [s3Cpp, mA] <;> ring

theorem sGlobal64_hz91 {c : ℝ} (hc : B (133 / 200) (67 / 100) c) : B (6754395616657530616613 / 1000000000000000000) (6813997541512344248633 / 1000000000000000000) ((s3Cpa 12225 c) + (s3r1 12225 46)) := badd (sGlobal64_hz84 hc) sGlobal64_hz33 (by norm_num) (by norm_num)

theorem sGlobal64_hz92 {c : ℝ} (hc : B (133 / 200) (67 / 100) c) : B (61156724513535962529 / 1000000000000000000) (1542409543847536847 / 25000000000000000) (((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) := bdiv (sGlobal64_hz91 hc) sGlobal64_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal64_hz93 {c : ℝ} (hc : B (133 / 200) (67 / 100) c) : B (61279407539030022941 / 1000000000000000000) (61819064779395534303 / 1000000000000000000) ((((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) + (s3e0 12225 46)) := badd (sGlobal64_hz92 hc) sGlobal64_hz16 (by norm_num) (by norm_num)

theorem sGlobal64_hz94 {c : ℝ} (hc : B (133 / 200) (67 / 100) c) : B (61279407539030022941 / 1000000000000000000) (61819064779395534303 / 1000000000000000000) (s3Lam 12225 46 c) := by
    convert (sGlobal64_hz93 hc) using 1 <;>
      norm_num [s3Lam] <;> ring

theorem sGlobal64_hz95 {c : ℝ} (hc : B (133 / 200) (67 / 100) c) : B (-1522030052144175596439 / 500000000000000000) (-370549218612660634741 / 125000000000000000) ((s3Cpp 12225 c) + (s3rpp 12225 46)) := badd (sGlobal64_hz90 hc) sGlobal64_hz37 (by norm_num) (by norm_num)

theorem sGlobal64_hz96 {c : ℝ} (hc : B (133 / 200) (67 / 100) c) : B (-2319730781200088420801 / 1000000000000000000) (-370549218612660634741 / 250000000000000000) (if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) := bweaken (bfirst (sGlobal64_hz95 hc) (sGlobal64_hz76 hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem sGlobal64_hz97 {c : ℝ} (hc : B (133 / 200) (67 / 100) c) : B (751033157666905922519 / 200000000000000000) (3821596770199101440241 / 1000000000000000000) ((s3Lam 12225 46 c)^2) := bsq (sGlobal64_hz94 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal64_hz98 {c : ℝ} (hc : B (133 / 200) (67 / 100) c) : B (21298786009437713 / 40000000000000000) (67228118995604563 / 125000000000000000) ((s3c1 12225 46 c)^2) := bsq (sGlobal64_hz72 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal64_hz99 {c : ℝ} (hc : B (133 / 200) (67 / 100) c) : B (57771881004395437 / 125000000000000000) (18701213990562287 / 40000000000000000) ((1 : ℝ) - ((s3c1 12225 46 c)^2)) := bsub (bpoint (1 : ℝ)) (sGlobal64_hz98 hc) (by norm_num) (by norm_num)

theorem sGlobal64_hz100 {c : ℝ} (hc : B (133 / 200) (67 / 100) c) : B (84979321752703049 / 125000000000000000) (341880955072104439 / 500000000000000000) (√((1 : ℝ) - ((s3c1 12225 46 c)^2))) := bsqrt (sGlobal64_hz99 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal64_hz101 {c : ℝ} (hc : B (133 / 200) (67 / 100) c) : B (266970412925335211 / 125000000000000000) (2148101393713570933 / 1000000000000000000) (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))) := bmul pi_mem (sGlobal64_hz100 hc) (by norm_num) (by norm_num)

theorem sGlobal64_hz102 {c : ℝ} (hc : B (133 / 200) (67 / 100) c) : B (1748132466802563587021 / 1000000000000000000) (223666918292781017889 / 125000000000000000) (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2))))) := bdiv (sGlobal64_hz97 hc) (sGlobal64_hz101 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal64_hz103 {c : ℝ} (hc : B (133 / 200) (67 / 100) c) : B (-28579915719876241689 / 50000000000000000) (76784617972901401037 / 250000000000000000) ((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) := badd (sGlobal64_hz96 hc) (sGlobal64_hz102 hc) (by norm_num) (by norm_num)

theorem sGlobal64_hz104 : B (3762781186094069 / 250000000000000000) (376278118609407 / 25000000000000000) ((s3e0 12225 46)^2) := bsq sGlobal64_hz16 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal64_hz105 {c : ℝ} (hc : B (133 / 200) (67 / 100) c) : B (-17861976977274389297 / 31250000000000000) (76788380754087495107 / 250000000000000000) (((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) := badd (sGlobal64_hz103 hc) sGlobal64_hz104 (by norm_num) (by norm_num)

theorem sGlobal64_hz106 {c : ℝ} (hc : B (133 / 200) (67 / 100) c) : B (-533086189821533187373 / 1000000000000000000) (86412649117618562611 / 250000000000000000) ((((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) + (s3rs 12225 46 maskSlack)) := badd (sGlobal64_hz105 hc) sGlobal64_hz29 (by norm_num) (by norm_num)

theorem sGlobal64_hz107 {c : ℝ} (hc : B (133 / 200) (67 / 100) c) : B (-533086189821533187373 / 1000000000000000000) (86412649117618562611 / 250000000000000000) (s3U 12225 46 maskSlack c) := by
    convert (sGlobal64_hz106 hc) using 1 <;>
      norm_num [s3U] <;> ring

theorem sGlobal64_hz108 {c : ℝ} (hc : B (133 / 200) (67 / 100) c) : B (-199849182345833454581 / 62500000000000000) (-1558960281073134579173 / 500000000000000000) ((s3Cpp 12225 c) - (s3rpp 12225 46)) := bsub (sGlobal64_hz90 hc) sGlobal64_hz37 (by norm_num) (by norm_num)

theorem sGlobal64_hz109 {c : ℝ} (hc : B (133 / 200) (67 / 100) c) : B (-199849182345833454581 / 62500000000000000) (-1558960281073134579173 / 500000000000000000) (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ)) := bweaken (bmin (sGlobal64_hz108 hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem sGlobal64_hz110 {c : ℝ} (hc : B (133 / 200) (67 / 100) c) : B (-609181532561992545449 / 250000000000000000) (-474137620710282785741 / 200000000000000000) ((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) := bmul (sGlobal64_hz76 hc) (sGlobal64_hz109 hc) (by norm_num) (by norm_num)

theorem sGlobal64_hz111 {c : ℝ} (hc : B (133 / 200) (67 / 100) c) : B (-609185295343178639519 / 250000000000000000) (-2370703154676158304981 / 1000000000000000000) (((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) := bsub (sGlobal64_hz110 hc) sGlobal64_hz104 (by norm_num) (by norm_num)

theorem sGlobal64_hz112 {c : ℝ} (hc : B (133 / 200) (67 / 100) c) : B (-618809563706709707023 / 250000000000000000) (-301150028515925696889 / 125000000000000000) ((((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) - (s3rs 12225 46 maskSlack)) := bsub (sGlobal64_hz111 hc) sGlobal64_hz29 (by norm_num) (by norm_num)

theorem sGlobal64_hz113 {c : ℝ} (hc : B (133 / 200) (67 / 100) c) : B (-618809563706709707023 / 250000000000000000) (-301150028515925696889 / 125000000000000000) (s3L 12225 46 maskSlack c) := by
    convert (sGlobal64_hz112 hc) using 1 <;>
      norm_num [s3L] <;> ring

theorem sGlobal64_hz114 {c : ℝ} (hc : B (133 / 200) (67 / 100) c) : B 0 (533086189821533187373 / 1000000000000000000) |(s3U 12225 46 maskSlack c)| := bweaken (babs (sGlobal64_hz107 hc)) (by norm_num) (by norm_num)

theorem sGlobal64_hz115 {c : ℝ} (hc : B (133 / 200) (67 / 100) c) : B 0 (618809563706709707023 / 250000000000000000) |(s3L 12225 46 maskSlack c)| := bweaken (babs (sGlobal64_hz113 hc)) (by norm_num) (by norm_num)

theorem sGlobal64_hz116 {c : ℝ} (hc : B (133 / 200) (67 / 100) c) : B 0 (618809563706709707023 / 250000000000000000) (max |(s3U 12225 46 maskSlack c)| |(s3L 12225 46 maskSlack c)|) := bweaken (bmax (sGlobal64_hz114 hc) (sGlobal64_hz115 hc)) (by norm_num) (by norm_num)

theorem sGlobal64_hz117 {c : ℝ} (hc : B (133 / 200) (67 / 100) c) : B 0 (618809563706709707023 / 250000000000000000) (s3nks 12225 46 maskSlack c) := by
    convert (sGlobal64_hz116 hc) using 1 <;>
      norm_num [s3nks] <;> ring

theorem sGlobal64 {c : ℝ} (hc : B (133 / 200) (67 / 100) c) :
    0 < s3am 12225 46 ∧ 0 ≤ s3dm 12225 46 c ∧
    s3dm 12225 46 c ^ 2 ≤ 2 * s3ap 12225 46 ^ 2 ∧ s3c1 12225 46 c < 1 ∧
    0 ≤ s3Cpa 12225 c - s3r1 12225 46 ∧
    s3e0 12225 46 ≤ (s3Cpa 12225 c - s3r1 12225 46) / s3ap 12225 46 ∧
    s3nks 12225 46 maskSlack c ≤ 12225 * (101237 / 500000) := by

  refine ⟨lt_of_lt_of_le (by norm_num) sGlobal64_hz14.1,
    le_trans (by norm_num) (sGlobal64_hz64 hc).1, ?_,
    lt_of_le_of_lt (sGlobal64_hz72 hc).2 (by norm_num), ?_, ?_,
    le_trans (sGlobal64_hz117 hc).2 (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (sGlobal64_hz64 hc).1) (sGlobal64_hz64 hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) sGlobal64_hz9.1 2
    nlinarith only [h1, h2]
  · linarith only [(sGlobal64_hz84 hc).1, sGlobal64_hz33.2]
  · have hap : 0 < s3ap 12225 46 := lt_of_lt_of_le (by norm_num) sGlobal64_hz9.1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul sGlobal64_hz16.2 sGlobal64_hz9.2 (le_trans (by norm_num) sGlobal64_hz9.1) (by norm_num)
    linarith only [h, (sGlobal64_hz84 hc).1, sGlobal64_hz33.2]

end BstLean.Part255
