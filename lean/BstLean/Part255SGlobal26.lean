import BstLean.Part255SGlobal22
import BstLean.Part255Numeric10
namespace BstLean.Part255
open Real BstLean.Part130 BstLean.Part182 BstLean.Part197 BstLean.Part246
theorem sGlobal26_hz0 : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal26_hz1 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) ((√(23 : ℝ)) / (12225 : ℝ)) := bdiv sGlobal26_hz0 (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal26_hz2 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) maskSlack := by
    convert sGlobal26_hz1 using 1 <;>
      norm_num [maskSlack] <;> ring

theorem sGlobal26_hz3 : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal26_hz4 : B (6395294793910793 / 500000000000000000) (12790589587821587 / 1000000000000000000) (√((2 / 12225) : ℝ)) := bsqrt (bpoint ((2 / 12225) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal26_hz5 : B (7230130686979 / 62500000000000000) (23136418198333 / 200000000000000000) (√((2 / 149450625) : ℝ)) := bsqrt (bpoint ((2 / 149450625) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal26_hz6 : B (2211334438749598093 / 20000000000000000) (110566721937479904651 / 1000000000000000000) (√(12225 : ℝ)) := bsqrt (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal26_hz7 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))) := bmul sGlobal26_hz3 sGlobal26_hz4 (by norm_num) (by norm_num)

theorem sGlobal26_hz8 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) ((√(12225 : ℝ)) + ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := badd sGlobal26_hz6 sGlobal26_hz7 (by norm_num) (by norm_num)

theorem sGlobal26_hz9 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) (s3ap 12225 46) := by
    convert sGlobal26_hz8 using 1 <;>
      norm_num [s3ap, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal26_hz10 : B (163599182004089 / 1000000000000000000) (16359918200409 / 100000000000000000) ((2 : ℝ) / (12225 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal26_hz11 : B (1222499983640081799591 / 100000000000000000) (12224999836400817995911 / 1000000000000000000) ((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ))) := bsub (bpoint (12225 : ℝ)) sGlobal26_hz10 (by norm_num) (by norm_num)

theorem sGlobal26_hz12 : B (110566721197658827907 / 1000000000000000000) (27641680299414706977 / 250000000000000000) (√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) := bsqrt sGlobal26_hz11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal26_hz13 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) ((√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) - ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bsub sGlobal26_hz12 sGlobal26_hz7 (by norm_num) (by norm_num)

theorem sGlobal26_hz14 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) (s3am 12225 46) := by
    convert sGlobal26_hz13 using 1 <;>
      norm_num [s3am, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal26_hz15 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√((2 / 12225) : ℝ)) * (√(92 : ℝ))) := bmul sGlobal26_hz4 sGlobal26_hz3 (by norm_num) (by norm_num)

theorem sGlobal26_hz16 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) (s3e0 12225 46) := by
    convert sGlobal26_hz15 using 1 <;>
      norm_num [s3e0, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal26_hz17 : B (250196148528560847 / 500000000000000000) (100078459411424339 / 200000000000000000) (((1 / 2) : ℝ) + maskSlack) := badd (bpoint ((1 / 2) : ℝ)) sGlobal26_hz2 (by norm_num) (by norm_num)

theorem sGlobal26_hz18 : B (59827153232297998295487 / 800000000000000) (23930861292919199366019 / 320000000000000) ((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack)) := bmul (bpoint (149450625 : ℝ)) sGlobal26_hz17 (by norm_num) (by norm_num)

theorem sGlobal26_hz19 : B (1729554180017180009583 / 200000000000000000) (8647770900085900056557 / 1000000000000000000) (√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) := bsqrt sGlobal26_hz18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal26_hz20 : B (4328681281566262743499 / 500000000000000000) (8657362563132525495641 / 1000000000000000000) ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))) := badd sGlobal26_hz19 sGlobal26_hz3 (by norm_num) (by norm_num)

theorem sGlobal26_hz21 : B (110732771457999278473 / 1000000000000000000) (55366385728999643621 / 500000000000000000) ((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ)))) := bmul sGlobal26_hz4 sGlobal26_hz20 (by norm_num) (by norm_num)

theorem sGlobal26_hz22 : B (209099159 / 15625000000000000) (13382346177 / 1000000000000000000) ((2 : ℝ) / (149450625 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (149450625 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal26_hz23 : B (2452349334953899930479 / 200000000000000000) (12261746674769501594427 / 1000000000000000000) (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2) := bsq sGlobal26_hz21 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal26_hz24 : B (82045469362091 / 500000000000000000) (32818187747289 / 200000000000000000) (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2)) := bmul sGlobal26_hz22 sGlobal26_hz23 (by norm_num) (by norm_num)

theorem sGlobal26_hz25 : B (82045469362091 / 250000000000000000) (32818187747289 / 100000000000000000) ((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) := bmul (bpoint (2 : ℝ)) sGlobal26_hz24 (by norm_num) (by norm_num)

theorem sGlobal26_hz26 : B (117258080744995992792057 / 1000000000000000000) (58629040372497996396029 / 500000000000000000) (√(13749457500 : ℝ)) := bsqrt (bpoint (13749457500 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal26_hz27 : B (117304080744995992792057 / 1000000000000000000) (58652040372497996396029 / 500000000000000000) ((√(13749457500 : ℝ)) + (46 : ℝ)) := badd sGlobal26_hz26 (bpoint (46 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal26_hz28 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal26_hz25 sGlobal26_hz27 (by norm_num) (by norm_num)

theorem sGlobal26_hz29 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (s3rs 12225 46 maskSlack) := by
    convert sGlobal26_hz28 using 1 <;>
      norm_num [s3rs, s3pp, s3K, mA, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal26_hz30 : B (490797546012267 / 1000000000000000000) (49079754601227 / 100000000000000000) ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (3 : ℝ)) sGlobal26_hz10 (by norm_num) (by norm_num)

theorem sGlobal26_hz31 : B (490797546012267 / 500000000000000000) (49079754601227 / 50000000000000000) ((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal26_hz30 (by norm_num) (by norm_num)

theorem sGlobal26_hz32 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal26_hz31 sGlobal26_hz27 (by norm_num) (by norm_num)

theorem sGlobal26_hz33 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (s3r1 12225 46) := by
    convert sGlobal26_hz32 using 1 <;>
      norm_num [s3r1, mA] <;> ring

theorem sGlobal26_hz34 : B (163599182004089 / 500000000000000000) (16359918200409 / 50000000000000000) ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (2 : ℝ)) sGlobal26_hz10 (by norm_num) (by norm_num)

theorem sGlobal26_hz35 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal26_hz34 (by norm_num) (by norm_num)

theorem sGlobal26_hz36 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal26_hz35 sGlobal26_hz27 (by norm_num) (by norm_num)

theorem sGlobal26_hz37 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (s3rpp 12225 46) := by
    convert sGlobal26_hz36 using 1 <;>
      norm_num [s3rpp, mA] <;> ring

theorem sGlobal26_hz38 {c : ℝ} (hc : B (19 / 40) (12 / 25) c) : B (19 / 40) (12 / 25) c := hc

theorem sGlobal26_hz39 : B (657551944600841127 / 1000000000000000000) (657551944601106109 / 1000000000000000000) (kdot ((19 / 40))) := by
    constructor
    · apply bkdot_lower (q := (23864021568539717 / 40000000000000000)) (a := (268958073769527011 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (149150134803373231 / 250000000000000000)) (a := (537916147538637791 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal26_hz40 : B (361 / 1600) (361 / 1600) (((19 / 40) : ℝ)^2) := bsq (bpoint ((19 / 40) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal26_hz41 : B (1239 / 1600) (1239 / 1600) ((1 : ℝ) - (((19 / 40) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal26_hz40 (by norm_num) (by norm_num)

theorem sGlobal26_hz42 : B (879985795339902063 / 1000000000000000000) (54999112208743879 / 62500000000000000) (√((1 : ℝ) - (((19 / 40) : ℝ)^2))) := bsqrt sGlobal26_hz41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal26_hz43 : B (280108178357996737 / 1000000000000000000) (140054089178998369 / 500000000000000000) ((√((1 : ℝ) - (((19 / 40) : ℝ)^2))) / Real.pi) := bdiv sGlobal26_hz42 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal26_hz44 : B (62467434737079907 / 200000000000000000) (156168586842762701 / 500000000000000000) (((19 / 40) : ℝ) * (kdot ((19 / 40)))) := bmul (bpoint ((19 / 40) : ℝ)) sGlobal26_hz39 (by norm_num) (by norm_num)

theorem sGlobal26_hz45 : B (37027834502712267 / 62500000000000000) (29622267602176107 / 50000000000000000) (((√((1 : ℝ) - (((19 / 40) : ℝ)^2))) / Real.pi) + (((19 / 40) : ℝ) * (kdot ((19 / 40))))) := badd sGlobal26_hz43 sGlobal26_hz44 (by norm_num) (by norm_num)

theorem sGlobal26_hz46 : B (37027834502712267 / 62500000000000000) (29622267602176107 / 50000000000000000) (kappa ((19 / 40))) := by rw [kappa_eq]; exact sGlobal26_hz45

theorem sGlobal26_hz47 : B (659363344522858571 / 1000000000000000000) (82420418065381437 / 125000000000000000) (kdot ((12 / 25))) := by
    constructor
    · apply bkdot_lower (q := (296374489181909579 / 500000000000000000)) (a := (535070807195192459 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (592748978363819157 / 1000000000000000000)) (a := (267535403597444707 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal26_hz48 : B (144 / 625) (144 / 625) (((12 / 25) : ℝ)^2) := bsq (bpoint ((12 / 25) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal26_hz49 : B (481 / 625) (481 / 625) ((1 : ℝ) - (((12 / 25) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal26_hz48 (by norm_num) (by norm_num)

theorem sGlobal26_hz50 : B (6853660062331659 / 7812500000000000) (877268487978452353 / 1000000000000000000) (√((1 : ℝ) - (((12 / 25) : ℝ)^2))) := bsqrt sGlobal26_hz49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal26_hz51 : B (279243232561047303 / 1000000000000000000) (34905404070130913 / 125000000000000000) ((√((1 : ℝ) - (((12 / 25) : ℝ)^2))) / Real.pi) := bdiv sGlobal26_hz50 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal26_hz52 : B (158247202685486057 / 500000000000000000) (316494405371064719 / 1000000000000000000) (((12 / 25) : ℝ) * (kdot ((12 / 25)))) := bmul (bpoint ((12 / 25) : ℝ)) sGlobal26_hz47 (by norm_num) (by norm_num)

theorem sGlobal26_hz53 : B (595737637932019417 / 1000000000000000000) (595737637932112023 / 1000000000000000000) (((√((1 : ℝ) - (((12 / 25) : ℝ)^2))) / Real.pi) + (((12 / 25) : ℝ) * (kdot ((12 / 25))))) := badd sGlobal26_hz51 sGlobal26_hz52 (by norm_num) (by norm_num)

theorem sGlobal26_hz54 : B (595737637932019417 / 1000000000000000000) (595737637932112023 / 1000000000000000000) (kappa ((12 / 25))) := by rw [kappa_eq]; exact sGlobal26_hz53

theorem sGlobal26_hz55 {c : ℝ} (hc : B (19 / 40) (12 / 25) c) : B (37027834502712267 / 62500000000000000) (595737637932112023 / 1000000000000000000) (kappa c) := bkappa (sGlobal26_hz38 hc) (by norm_num) (by norm_num) sGlobal26_hz46.1 sGlobal26_hz54.2

theorem sGlobal26_hz56 : B 24450 24450 ((2 : ℝ) * (12225 : ℝ)) := bmul (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal26_hz57 {c : ℝ} (hc : B (19 / 40) (12 / 25) c) : B (404262362067887977 / 1000000000000000000) (25472165497287733 / 62500000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (sGlobal26_hz55 hc) (by norm_num) (by norm_num)

theorem sGlobal26_hz58 {c : ℝ} (hc : B (19 / 40) (12 / 25) c) : B (197684295051197220753 / 20000000000000000) (12455888928173701437 / 1250000000000000) (((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) := bmul sGlobal26_hz56 (sGlobal26_hz57 hc) (by norm_num) (by norm_num)

theorem sGlobal26_hz59 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (4 : ℝ)) sGlobal26_hz10 (by norm_num) (by norm_num)

theorem sGlobal26_hz60 {c : ℝ} (hc : B (19 / 40) (12 / 25) c) : B (988421409816313302129 / 100000000000000000) (2491177622035558283311 / 250000000000000000) ((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bsub (sGlobal26_hz58 hc) sGlobal26_hz59 (by norm_num) (by norm_num)

theorem sGlobal26_hz61 {c : ℝ} (hc : B (19 / 40) (12 / 25) c) : B (99419384921468574841 / 1000000000000000000) (1996467929934486389 / 20000000000000000) (√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) := bsqrt (sGlobal26_hz60 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal26_hz62 : B (30670756373515103 / 125000000000000000) (122683025494060423 / 500000000000000000) ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal26_hz7 (by norm_num) (by norm_num)

theorem sGlobal26_hz63 {c : ℝ} (hc : B (19 / 40) (12 / 25) c) : B (19834803774096090799 / 200000000000000000) (49789015222868099313 / 500000000000000000) ((√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) - ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))))) := bsub (sGlobal26_hz61 hc) sGlobal26_hz62 (by norm_num) (by norm_num)

theorem sGlobal26_hz64 {c : ℝ} (hc : B (19 / 40) (12 / 25) c) : B (19834803774096090799 / 200000000000000000) (49789015222868099313 / 500000000000000000) (s3dm 12225 46 c) := by
    convert (sGlobal26_hz63 hc) using 1 <;>
      norm_num [s3dm, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal26_hz65 : B (6126072185528622723889 / 500000000000000000) (2450428874211449090087 / 200000000000000000) ((s3ap 12225 46)^2) := bsq sGlobal26_hz9 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal26_hz66 : B (6126072185528622723889 / 250000000000000000) (2450428874211449090087 / 100000000000000000) ((2 : ℝ) * ((s3ap 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal26_hz65 (by norm_num) (by norm_num)

theorem sGlobal26_hz67 {c : ℝ} (hc : B (19 / 40) (12 / 25) c) : B (307358938091325412001 / 31250000000000000) (9915784147451965316413 / 1000000000000000000) ((s3dm 12225 46 c)^2) := bsq (sGlobal26_hz64 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal26_hz68 {c : ℝ} (hc : B (19 / 40) (12 / 25) c) : B (14588504594662525579143 / 1000000000000000000) (7334401361596038858419 / 500000000000000000) (((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) := bsub sGlobal26_hz66 (sGlobal26_hz67 hc) (by norm_num) (by norm_num)

theorem sGlobal26_hz69 : B (1524735695971823534271 / 125000000000000000) (609894278388729413841 / 50000000000000000) ((s3am 12225 46)^2) := bsq sGlobal26_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal26_hz70 : B (1524735695971823534271 / 62500000000000000) (609894278388729413841 / 25000000000000000) ((2 : ℝ) * ((s3am 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal26_hz69 (by norm_num) (by norm_num)

theorem sGlobal26_hz71 {c : ℝ} (hc : B (19 / 40) (12 / 25) c) : B (597993173226828673 / 1000000000000000000) (300642325296635193 / 500000000000000000) ((((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) / ((2 : ℝ) * ((s3am 12225 46)^2))) := bdiv (sGlobal26_hz68 hc) sGlobal26_hz70 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal26_hz72 {c : ℝ} (hc : B (19 / 40) (12 / 25) c) : B (597993173226828673 / 1000000000000000000) (300642325296635193 / 500000000000000000) (s3c1 12225 46 c) := by
    convert (sGlobal26_hz71 hc) using 1 <;>
      norm_num [s3c1] <;> ring

theorem sGlobal26_hz73 {c : ℝ} (hc : B (19 / 40) (12 / 25) c) : B (657551944600841127 / 1000000000000000000) (82420418065381437 / 125000000000000000) (kdot c) := bkdot (sGlobal26_hz38 hc) sGlobal26_hz39.1 sGlobal26_hz47.2

theorem sGlobal26_hz74 : B (352017511296829771 / 500000000000000000) (352017511296829799 / 500000000000000000) (kdot ((597993173226828673 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (250783672897293751 / 500000000000000000)) (a := (464900699369814159 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (501567345794587501 / 1000000000000000000)) (a := (464900699369814073 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal26_hz75 : B (705344219322852141 / 1000000000000000000) (141068843864570437 / 200000000000000000) (kdot ((300642325296635193 / 500000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (62374520526880537 / 125000000000000000)) (a := (115711054489136633 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (99799232843008859 / 200000000000000000)) (a := (14463881811142077 / 31250000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal26_hz76 {c : ℝ} (hc : B (19 / 40) (12 / 25) c) : B (352017511296829771 / 500000000000000000) (141068843864570437 / 200000000000000000) (kdot (s3c1 12225 46 c)) := bkdot (sGlobal26_hz72 hc) sGlobal26_hz74.1 sGlobal26_hz75.2

theorem sGlobal26_hz77 {c : ℝ} (hc : B (19 / 40) (12 / 25) c) : B (361 / 1600) (144 / 625) (c^2) := bsq (sGlobal26_hz38 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal26_hz78 {c : ℝ} (hc : B (19 / 40) (12 / 25) c) : B (481 / 625) (1239 / 1600) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (sGlobal26_hz77 hc) (by norm_num) (by norm_num)

theorem sGlobal26_hz79 {c : ℝ} (hc : B (19 / 40) (12 / 25) c) : B (6853660062331659 / 7812500000000000) (54999112208743879 / 62500000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (sGlobal26_hz78 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal26_hz80 : B (39119999999999765769 / 1600000000000000) (3912000000000000489 / 160000000000000) ((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (149450625 : ℝ)) sGlobal26_hz10 (by norm_num) (by norm_num)

theorem sGlobal26_hz81 {c : ℝ} (hc : B (19 / 40) (12 / 25) c) : B (576849600207270961 / 1000000000000000000) (580230377148095329 / 1000000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (sGlobal26_hz79 hc) (sGlobal26_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal26_hz82 {c : ℝ} (hc : B (19 / 40) (12 / 25) c) : B (14103972725067690548913 / 1000000000000000000) (709331636063546628369 / 50000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) := bmul sGlobal26_hz80 (sGlobal26_hz81 hc) (by norm_num) (by norm_num)

theorem sGlobal26_hz83 {c : ℝ} (hc : B (19 / 40) (12 / 25) c) : B (881498295316730659307 / 125000000000000000) (709331636063546628369 / 100000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) / (2 : ℝ)) := bdiv (sGlobal26_hz82 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal26_hz84 {c : ℝ} (hc : B (19 / 40) (12 / 25) c) : B (881498295316730659307 / 125000000000000000) (709331636063546628369 / 100000000000000000) (s3Cpa 12225 c) := by
    convert (sGlobal26_hz83 hc) using 1 <;>
      norm_num [s3Cpa, mA] <;> ring

theorem sGlobal26_hz85 {c : ℝ} (hc : B (19 / 40) (12 / 25) c) : B (279243232561047303 / 1000000000000000000) (140054089178998369 / 500000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (sGlobal26_hz79 hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal26_hz86 {c : ℝ} (hc : B (19 / 40) (12 / 25) c) : B (62467434737079907 / 200000000000000000) (316494405371064719 / 1000000000000000000) (c * (kdot c)) := bmul (sGlobal26_hz38 hc) (sGlobal26_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal26_hz87 {c : ℝ} (hc : B (19 / 40) (12 / 25) c) : B (-4656396601252177 / 125000000000000000) (-32228995327402797 / 1000000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (sGlobal26_hz85 hc) (sGlobal26_hz86 hc) (by norm_num) (by norm_num)

theorem sGlobal26_hz88 {c : ℝ} (hc : B (19 / 40) (12 / 25) c) : B (-910791175204925935049 / 1000000000000000000) (-393999467877496834253 / 500000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) := bmul sGlobal26_hz80 (sGlobal26_hz87 hc) (by norm_num) (by norm_num)

theorem sGlobal26_hz89 {c : ℝ} (hc : B (19 / 40) (12 / 25) c) : B (-18215823504098518701 / 40000000000000000) (-393999467877496834253 / 1000000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) / (2 : ℝ)) := bdiv (sGlobal26_hz88 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal26_hz90 {c : ℝ} (hc : B (19 / 40) (12 / 25) c) : B (-18215823504098518701 / 40000000000000000) (-393999467877496834253 / 1000000000000000000) (s3Cpp 12225 c) := by
    convert (sGlobal26_hz89 hc) using 1 <;>
      norm_num [s3Cpp, mA] <;> ring

theorem sGlobal26_hz91 {c : ℝ} (hc : B (19 / 40) (12 / 25) c) : B (7167131472467582982857 / 1000000000000000000) (1802115367642301173979 / 250000000000000000) ((s3Cpa 12225 c) + (s3r1 12225 46)) := badd (sGlobal26_hz84 hc) sGlobal26_hz33 (by norm_num) (by norm_num)

theorem sGlobal26_hz92 {c : ℝ} (hc : B (19 / 40) (12 / 25) c) : B (64893783232510566851 / 1000000000000000000) (13053599976727317181 / 200000000000000000) (((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) := bdiv (sGlobal26_hz91 hc) sGlobal26_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal26_hz93 {c : ℝ} (hc : B (19 / 40) (12 / 25) c) : B (65016466258004627263 / 1000000000000000000) (8173835363641330791 / 125000000000000000) ((((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) + (s3e0 12225 46)) := badd (sGlobal26_hz92 hc) sGlobal26_hz16 (by norm_num) (by norm_num)

theorem sGlobal26_hz94 {c : ℝ} (hc : B (19 / 40) (12 / 25) c) : B (65016466258004627263 / 1000000000000000000) (8173835363641330791 / 125000000000000000) (s3Lam 12225 46 c) := by
    convert (sGlobal26_hz93 hc) using 1 <;>
      norm_num [s3Lam] <;> ring

theorem sGlobal26_hz95 {c : ℝ} (hc : B (19 / 40) (12 / 25) c) : B (-15145287239198846477 / 40000000000000000) (-63447212251000911887 / 200000000000000000) ((s3Cpp 12225 c) + (s3rpp 12225 46)) := badd (sGlobal26_hz90 hc) sGlobal26_hz37 (by norm_num) (by norm_num)

theorem sGlobal26_hz96 {c : ℝ} (hc : B (19 / 40) (12 / 25) c) : B (-33383252512978330099 / 125000000000000000) (-158618030627502279717 / 1000000000000000000) (if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) := bweaken (bfirst (sGlobal26_hz95 hc) (sGlobal26_hz76 hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem sGlobal26_hz97 {c : ℝ} (hc : B (19 / 40) (12 / 25) c) : B (4227140884678254219141 / 1000000000000000000) (534492676415308850937 / 125000000000000000) ((s3Lam 12225 46 c)^2) := bsq (sGlobal26_hz94 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal26_hz98 {c : ℝ} (hc : B (19 / 40) (12 / 25) c) : B (89398958806472981 / 250000000000000000) (180771615519535627 / 500000000000000000) ((s3c1 12225 46 c)^2) := bsq (sGlobal26_hz72 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal26_hz99 {c : ℝ} (hc : B (19 / 40) (12 / 25) c) : B (319228384480464373 / 500000000000000000) (160601041193527019 / 250000000000000000) ((1 : ℝ) - ((s3c1 12225 46 c)^2)) := bsub (bpoint (1 : ℝ)) (sGlobal26_hz98 hc) (by norm_num) (by norm_num)

theorem sGlobal26_hz100 {c : ℝ} (hc : B (19 / 40) (12 / 25) c) : B (3121230072119021 / 3906250000000000) (6261728081978523 / 7812500000000000) (√((1 : ℝ) - ((s3c1 12225 46 c)^2))) := bsqrt (sGlobal26_hz99 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal26_hz101 {c : ℝ} (hc : B (19 / 40) (12 / 25) c) : B (313780270871445021 / 125000000000000000) (2517990264463441209 / 1000000000000000000) (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))) := bmul pi_mem (sGlobal26_hz100 hc) (by norm_num) (by norm_num)

theorem sGlobal26_hz102 {c : ℝ} (hc : B (19 / 40) (12 / 25) c) : B (209846963287356875587 / 125000000000000000) (170339796995805750067 / 100000000000000000) (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2))))) := bdiv (sGlobal26_hz97 hc) (sGlobal26_hz101 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal26_hz103 {c : ℝ} (hc : B (19 / 40) (12 / 25) c) : B (11028981923398659093 / 7812500000000000) (1544779939330555220953 / 1000000000000000000) ((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) := badd (sGlobal26_hz96 hc) (sGlobal26_hz102 hc) (by norm_num) (by norm_num)

theorem sGlobal26_hz104 : B (3762781186094069 / 250000000000000000) (376278118609407 / 25000000000000000) ((s3e0 12225 46)^2) := bsq sGlobal26_hz16 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal26_hz105 {c : ℝ} (hc : B (19 / 40) (12 / 25) c) : B (70586236865988637009 / 50000000000000000) (1544794990455299597233 / 1000000000000000000) (((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) := badd (sGlobal26_hz103 hc) sGlobal26_hz104 (by norm_num) (by norm_num)

theorem sGlobal26_hz106 {c : ℝ} (hc : B (19 / 40) (12 / 25) c) : B (1450221810771020010311 / 1000000000000000000) (1583292063909423867249 / 1000000000000000000) ((((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) + (s3rs 12225 46 maskSlack)) := badd (sGlobal26_hz105 hc) sGlobal26_hz29 (by norm_num) (by norm_num)

theorem sGlobal26_hz107 {c : ℝ} (hc : B (19 / 40) (12 / 25) c) : B (1450221810771020010311 / 1000000000000000000) (1583292063909423867249 / 1000000000000000000) (s3U 12225 46 maskSlack c) := by
    convert (sGlobal26_hz106 hc) using 1 <;>
      norm_num [s3U] <;> ring

theorem sGlobal26_hz108 {c : ℝ} (hc : B (19 / 40) (12 / 25) c) : B (-532158994224955242343 / 1000000000000000000) (-470762874499988639853 / 1000000000000000000) ((s3Cpp 12225 c) - (s3rpp 12225 46)) := bsub (sGlobal26_hz90 hc) sGlobal26_hz37 (by norm_num) (by norm_num)

theorem sGlobal26_hz109 {c : ℝ} (hc : B (19 / 40) (12 / 25) c) : B (-532158994224955242343 / 1000000000000000000) (-470762874499988639853 / 1000000000000000000) (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ)) := bweaken (bmin (sGlobal26_hz108 hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem sGlobal26_hz110 {c : ℝ} (hc : B (19 / 40) (12 / 25) c) : B (-187677635168617629887 / 500000000000000000) (-82858387746213903381 / 250000000000000000) ((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) := bmul (sGlobal26_hz76 hc) (sGlobal26_hz109 hc) (by norm_num) (by norm_num)

theorem sGlobal26_hz111 {c : ℝ} (hc : B (19 / 40) (12 / 25) c) : B (-187685160730989818027 / 500000000000000000) (-1657243010547999949 / 5000000000000000) (((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) := bsub (sGlobal26_hz110 hc) sGlobal26_hz104 (by norm_num) (by norm_num)

theorem sGlobal26_hz112 {c : ℝ} (hc : B (19 / 40) (12 / 25) c) : B (-41386739491610390607 / 100000000000000000) (-369945675560847259931 / 1000000000000000000) ((((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) - (s3rs 12225 46 maskSlack)) := bsub (sGlobal26_hz111 hc) sGlobal26_hz29 (by norm_num) (by norm_num)

theorem sGlobal26_hz113 {c : ℝ} (hc : B (19 / 40) (12 / 25) c) : B (-41386739491610390607 / 100000000000000000) (-369945675560847259931 / 1000000000000000000) (s3L 12225 46 maskSlack c) := by
    convert (sGlobal26_hz112 hc) using 1 <;>
      norm_num [s3L] <;> ring

theorem sGlobal26_hz114 {c : ℝ} (hc : B (19 / 40) (12 / 25) c) : B 0 (1583292063909423867249 / 1000000000000000000) |(s3U 12225 46 maskSlack c)| := bweaken (babs (sGlobal26_hz107 hc)) (by norm_num) (by norm_num)

theorem sGlobal26_hz115 {c : ℝ} (hc : B (19 / 40) (12 / 25) c) : B 0 (41386739491610390607 / 100000000000000000) |(s3L 12225 46 maskSlack c)| := bweaken (babs (sGlobal26_hz113 hc)) (by norm_num) (by norm_num)

theorem sGlobal26_hz116 {c : ℝ} (hc : B (19 / 40) (12 / 25) c) : B 0 (1583292063909423867249 / 1000000000000000000) (max |(s3U 12225 46 maskSlack c)| |(s3L 12225 46 maskSlack c)|) := bweaken (bmax (sGlobal26_hz114 hc) (sGlobal26_hz115 hc)) (by norm_num) (by norm_num)

theorem sGlobal26_hz117 {c : ℝ} (hc : B (19 / 40) (12 / 25) c) : B 0 (1583292063909423867249 / 1000000000000000000) (s3nks 12225 46 maskSlack c) := by
    convert (sGlobal26_hz116 hc) using 1 <;>
      norm_num [s3nks] <;> ring

theorem sGlobal26 {c : ℝ} (hc : B (19 / 40) (12 / 25) c) :
    0 < s3am 12225 46 ∧ 0 ≤ s3dm 12225 46 c ∧
    s3dm 12225 46 c ^ 2 ≤ 2 * s3ap 12225 46 ^ 2 ∧ s3c1 12225 46 c < 1 ∧
    0 ≤ s3Cpa 12225 c - s3r1 12225 46 ∧
    s3e0 12225 46 ≤ (s3Cpa 12225 c - s3r1 12225 46) / s3ap 12225 46 ∧
    s3nks 12225 46 maskSlack c ≤ 12225 * (129513 / 1000000) := by

  refine ⟨lt_of_lt_of_le (by norm_num) sGlobal26_hz14.1,
    le_trans (by norm_num) (sGlobal26_hz64 hc).1, ?_,
    lt_of_le_of_lt (sGlobal26_hz72 hc).2 (by norm_num), ?_, ?_,
    le_trans (sGlobal26_hz117 hc).2 (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (sGlobal26_hz64 hc).1) (sGlobal26_hz64 hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) sGlobal26_hz9.1 2
    nlinarith only [h1, h2]
  · linarith only [(sGlobal26_hz84 hc).1, sGlobal26_hz33.2]
  · have hap : 0 < s3ap 12225 46 := lt_of_lt_of_le (by norm_num) sGlobal26_hz9.1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul sGlobal26_hz16.2 sGlobal26_hz9.2 (le_trans (by norm_num) sGlobal26_hz9.1) (by norm_num)
    linarith only [h, (sGlobal26_hz84 hc).1, sGlobal26_hz33.2]

end BstLean.Part255
