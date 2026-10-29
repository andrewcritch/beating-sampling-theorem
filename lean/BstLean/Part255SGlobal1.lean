import BstLean.Part255Numeric51W
import BstLean.Part255Numeric10
namespace BstLean.Part255
open Real BstLean.Part130 BstLean.Part182 BstLean.Part197 BstLean.Part246
theorem sGlobal1_hz0 : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal1_hz1 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) ((√(23 : ℝ)) / (12225 : ℝ)) := bdiv sGlobal1_hz0 (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal1_hz2 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) maskSlack := by
    convert sGlobal1_hz1 using 1 <;>
      norm_num [maskSlack] <;> ring

theorem sGlobal1_hz3 : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal1_hz4 : B (6395294793910793 / 500000000000000000) (12790589587821587 / 1000000000000000000) (√((2 / 12225) : ℝ)) := bsqrt (bpoint ((2 / 12225) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal1_hz5 : B (7230130686979 / 62500000000000000) (23136418198333 / 200000000000000000) (√((2 / 149450625) : ℝ)) := bsqrt (bpoint ((2 / 149450625) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal1_hz6 : B (2211334438749598093 / 20000000000000000) (110566721937479904651 / 1000000000000000000) (√(12225 : ℝ)) := bsqrt (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal1_hz7 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))) := bmul sGlobal1_hz3 sGlobal1_hz4 (by norm_num) (by norm_num)

theorem sGlobal1_hz8 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) ((√(12225 : ℝ)) + ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := badd sGlobal1_hz6 sGlobal1_hz7 (by norm_num) (by norm_num)

theorem sGlobal1_hz9 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) (s3ap 12225 46) := by
    convert sGlobal1_hz8 using 1 <;>
      norm_num [s3ap, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal1_hz10 : B (163599182004089 / 1000000000000000000) (16359918200409 / 100000000000000000) ((2 : ℝ) / (12225 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal1_hz11 : B (1222499983640081799591 / 100000000000000000) (12224999836400817995911 / 1000000000000000000) ((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ))) := bsub (bpoint (12225 : ℝ)) sGlobal1_hz10 (by norm_num) (by norm_num)

theorem sGlobal1_hz12 : B (110566721197658827907 / 1000000000000000000) (27641680299414706977 / 250000000000000000) (√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) := bsqrt sGlobal1_hz11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal1_hz13 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) ((√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) - ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bsub sGlobal1_hz12 sGlobal1_hz7 (by norm_num) (by norm_num)

theorem sGlobal1_hz14 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) (s3am 12225 46) := by
    convert sGlobal1_hz13 using 1 <;>
      norm_num [s3am, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal1_hz15 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√((2 / 12225) : ℝ)) * (√(92 : ℝ))) := bmul sGlobal1_hz4 sGlobal1_hz3 (by norm_num) (by norm_num)

theorem sGlobal1_hz16 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) (s3e0 12225 46) := by
    convert sGlobal1_hz15 using 1 <;>
      norm_num [s3e0, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal1_hz17 : B (250196148528560847 / 500000000000000000) (100078459411424339 / 200000000000000000) (((1 / 2) : ℝ) + maskSlack) := badd (bpoint ((1 / 2) : ℝ)) sGlobal1_hz2 (by norm_num) (by norm_num)

theorem sGlobal1_hz18 : B (59827153232297998295487 / 800000000000000) (23930861292919199366019 / 320000000000000) ((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack)) := bmul (bpoint (149450625 : ℝ)) sGlobal1_hz17 (by norm_num) (by norm_num)

theorem sGlobal1_hz19 : B (1729554180017180009583 / 200000000000000000) (8647770900085900056557 / 1000000000000000000) (√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) := bsqrt sGlobal1_hz18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal1_hz20 : B (4328681281566262743499 / 500000000000000000) (8657362563132525495641 / 1000000000000000000) ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))) := badd sGlobal1_hz19 sGlobal1_hz3 (by norm_num) (by norm_num)

theorem sGlobal1_hz21 : B (110732771457999278473 / 1000000000000000000) (55366385728999643621 / 500000000000000000) ((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ)))) := bmul sGlobal1_hz4 sGlobal1_hz20 (by norm_num) (by norm_num)

theorem sGlobal1_hz22 : B (209099159 / 15625000000000000) (13382346177 / 1000000000000000000) ((2 : ℝ) / (149450625 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (149450625 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal1_hz23 : B (2452349334953899930479 / 200000000000000000) (12261746674769501594427 / 1000000000000000000) (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2) := bsq sGlobal1_hz21 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal1_hz24 : B (82045469362091 / 500000000000000000) (32818187747289 / 200000000000000000) (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2)) := bmul sGlobal1_hz22 sGlobal1_hz23 (by norm_num) (by norm_num)

theorem sGlobal1_hz25 : B (82045469362091 / 250000000000000000) (32818187747289 / 100000000000000000) ((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) := bmul (bpoint (2 : ℝ)) sGlobal1_hz24 (by norm_num) (by norm_num)

theorem sGlobal1_hz26 : B (117258080744995992792057 / 1000000000000000000) (58629040372497996396029 / 500000000000000000) (√(13749457500 : ℝ)) := bsqrt (bpoint (13749457500 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal1_hz27 : B (117304080744995992792057 / 1000000000000000000) (58652040372497996396029 / 500000000000000000) ((√(13749457500 : ℝ)) + (46 : ℝ)) := badd sGlobal1_hz26 (bpoint (46 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal1_hz28 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal1_hz25 sGlobal1_hz27 (by norm_num) (by norm_num)

theorem sGlobal1_hz29 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (s3rs 12225 46 maskSlack) := by
    convert sGlobal1_hz28 using 1 <;>
      norm_num [s3rs, s3pp, s3K, mA, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal1_hz30 : B (490797546012267 / 1000000000000000000) (49079754601227 / 100000000000000000) ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (3 : ℝ)) sGlobal1_hz10 (by norm_num) (by norm_num)

theorem sGlobal1_hz31 : B (490797546012267 / 500000000000000000) (49079754601227 / 50000000000000000) ((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal1_hz30 (by norm_num) (by norm_num)

theorem sGlobal1_hz32 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal1_hz31 sGlobal1_hz27 (by norm_num) (by norm_num)

theorem sGlobal1_hz33 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (s3r1 12225 46) := by
    convert sGlobal1_hz32 using 1 <;>
      norm_num [s3r1, mA] <;> ring

theorem sGlobal1_hz34 : B (163599182004089 / 500000000000000000) (16359918200409 / 50000000000000000) ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (2 : ℝ)) sGlobal1_hz10 (by norm_num) (by norm_num)

theorem sGlobal1_hz35 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal1_hz34 (by norm_num) (by norm_num)

theorem sGlobal1_hz36 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal1_hz35 sGlobal1_hz27 (by norm_num) (by norm_num)

theorem sGlobal1_hz37 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (s3rpp 12225 46) := by
    convert sGlobal1_hz36 using 1 <;>
      norm_num [s3rpp, mA] <;> ring

theorem sGlobal1_hz38 {c : ℝ} (hc : B (7 / 20) (71 / 200) c) : B (7 / 20) (71 / 200) c := hc

theorem sGlobal1_hz39 : B (24552736689413483 / 40000000000000000) (122763683533952243 / 200000000000000000) (kdot ((7 / 20))) := by
    constructor
    · apply bkdot_lower (q := (2710502603471527 / 3906250000000000)) (a := (606612611682571879 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (693888666488710911 / 1000000000000000000)) (a := (606612611000180037 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal1_hz40 : B (49 / 400) (49 / 400) (((7 / 20) : ℝ)^2) := bsq (bpoint ((7 / 20) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal1_hz41 : B (351 / 400) (351 / 400) ((1 : ℝ) - (((7 / 20) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal1_hz40 (by norm_num) (by norm_num)

theorem sGlobal1_hz42 : B (93674969975975973 / 100000000000000000) (936749699759759731 / 1000000000000000000) (√((1 : ℝ) - (((7 / 20) : ℝ)^2))) := bsqrt sGlobal1_hz41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal1_hz43 : B (298176690313229203 / 1000000000000000000) (74544172578307301 / 250000000000000000) ((√((1 : ℝ) - (((7 / 20) : ℝ)^2))) / Real.pi) := bdiv sGlobal1_hz42 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal1_hz44 : B (26854555754045997 / 125000000000000000) (107418223092208213 / 500000000000000000) (((7 / 20) : ℝ) * (kdot ((7 / 20)))) := bmul (bpoint ((7 / 20) : ℝ)) sGlobal1_hz39 (by norm_num) (by norm_num)

theorem sGlobal1_hz45 : B (513013136345597179 / 1000000000000000000) (51301313649764563 / 100000000000000000) (((√((1 : ℝ) - (((7 / 20) : ℝ)^2))) / Real.pi) + (((7 / 20) : ℝ) * (kdot ((7 / 20))))) := badd sGlobal1_hz43 sGlobal1_hz44 (by norm_num) (by norm_num)

theorem sGlobal1_hz46 : B (513013136345597179 / 1000000000000000000) (51301313649764563 / 100000000000000000) (kappa ((7 / 20))) := by rw [kappa_eq]; exact sGlobal1_hz45

theorem sGlobal1_hz47 : B (153879783848994919 / 250000000000000000) (307759567862194061 / 500000000000000000) (kdot ((71 / 200))) := by
    constructor
    · apply bkdot_lower (q := (344969114613033683 / 500000000000000000)) (a := (150985282460730277 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (137987645845213473 / 200000000000000000)) (a := (60394112932705833 / 100000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal1_hz48 : B (5041 / 40000) (5041 / 40000) (((71 / 200) : ℝ)^2) := bsq (bpoint ((71 / 200) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal1_hz49 : B (34959 / 40000) (34959 / 40000) ((1 : ℝ) - (((71 / 200) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal1_hz48 (by norm_num) (by norm_num)

theorem sGlobal1_hz50 : B (934866300601321279 / 1000000000000000000) (2921457189379129 / 3125000000000000) (√((1 : ℝ) - (((71 / 200) : ℝ)^2))) := bsqrt sGlobal1_hz49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal1_hz51 : B (74394296435367003 / 250000000000000000) (148788592870734007 / 500000000000000000) ((√((1 : ℝ) - (((71 / 200) : ℝ)^2))) / Real.pi) := bdiv sGlobal1_hz50 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal1_hz52 : B (13656830816598299 / 62500000000000000) (27313661647769723 / 125000000000000000) (((71 / 200) : ℝ) * (kdot ((71 / 200)))) := bmul (bpoint ((71 / 200) : ℝ)) sGlobal1_hz47 (by norm_num) (by norm_num)

theorem sGlobal1_hz53 : B (129021619701760199 / 250000000000000000) (258043239461812899 / 500000000000000000) (((√((1 : ℝ) - (((71 / 200) : ℝ)^2))) / Real.pi) + (((71 / 200) : ℝ) * (kdot ((71 / 200))))) := badd sGlobal1_hz51 sGlobal1_hz52 (by norm_num) (by norm_num)

theorem sGlobal1_hz54 : B (129021619701760199 / 250000000000000000) (258043239461812899 / 500000000000000000) (kappa ((71 / 200))) := by rw [kappa_eq]; exact sGlobal1_hz53

theorem sGlobal1_hz55 {c : ℝ} (hc : B (7 / 20) (71 / 200) c) : B (513013136345597179 / 1000000000000000000) (258043239461812899 / 500000000000000000) (kappa c) := bkappa (sGlobal1_hz38 hc) (by norm_num) (by norm_num) sGlobal1_hz46.1 sGlobal1_hz54.2

theorem sGlobal1_hz56 : B 24450 24450 ((2 : ℝ) * (12225 : ℝ)) := bmul (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal1_hz57 {c : ℝ} (hc : B (7 / 20) (71 / 200) c) : B (241956760538187101 / 500000000000000000) (486986863654402821 / 1000000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (sGlobal1_hz55 hc) (by norm_num) (by norm_num)

theorem sGlobal1_hz58 {c : ℝ} (hc : B (7 / 20) (71 / 200) c) : B (118316855903173492389 / 10000000000000000) (238136576327002979469 / 20000000000000000) (((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) := bmul sGlobal1_hz56 (sGlobal1_hz57 hc) (by norm_num) (by norm_num)

theorem sGlobal1_hz59 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (4 : ℝ)) sGlobal1_hz10 (by norm_num) (by norm_num)

theorem sGlobal1_hz60 {c : ℝ} (hc : B (7 / 20) (71 / 200) c) : B (591584246796031061127 / 50000000000000000) (5953414080976710478547 / 500000000000000000) ((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bsub (sGlobal1_hz58 hc) sGlobal1_hz59 (by norm_num) (by norm_num)

theorem sGlobal1_hz61 {c : ℝ} (hc : B (7 / 20) (71 / 200) c) : B (108773548879866107007 / 1000000000000000000) (109118413487153582961 / 1000000000000000000) (√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) := bsqrt (sGlobal1_hz60 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal1_hz62 : B (30670756373515103 / 125000000000000000) (122683025494060423 / 500000000000000000) ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal1_hz7 (by norm_num) (by norm_num)

theorem sGlobal1_hz63 {c : ℝ} (hc : B (7 / 20) (71 / 200) c) : B (108528182828877986161 / 1000000000000000000) (108873047436165462137 / 1000000000000000000) ((√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) - ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))))) := bsub (sGlobal1_hz61 hc) sGlobal1_hz62 (by norm_num) (by norm_num)

theorem sGlobal1_hz64 {c : ℝ} (hc : B (7 / 20) (71 / 200) c) : B (108528182828877986161 / 1000000000000000000) (108873047436165462137 / 1000000000000000000) (s3dm 12225 46 c) := by
    convert (sGlobal1_hz63 hc) using 1 <;>
      norm_num [s3dm, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal1_hz65 : B (6126072185528622723889 / 500000000000000000) (2450428874211449090087 / 200000000000000000) ((s3ap 12225 46)^2) := bsq sGlobal1_hz9 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal1_hz66 : B (6126072185528622723889 / 250000000000000000) (2450428874211449090087 / 100000000000000000) ((2 : ℝ) * ((s3ap 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal1_hz65 (by norm_num) (by norm_num)

theorem sGlobal1_hz67 {c : ℝ} (hc : B (7 / 20) (71 / 200) c) : B (11778366468138366562787 / 1000000000000000000) (11853340458037534908277 / 1000000000000000000) ((s3dm 12225 46 c)^2) := bsq (sGlobal1_hz64 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal1_hz68 {c : ℝ} (hc : B (7 / 20) (71 / 200) c) : B (12650948284076955987279 / 1000000000000000000) (12725922273976124338083 / 1000000000000000000) (((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) := bsub sGlobal1_hz66 (sGlobal1_hz67 hc) (by norm_num) (by norm_num)

theorem sGlobal1_hz69 : B (1524735695971823534271 / 125000000000000000) (609894278388729413841 / 50000000000000000) ((s3am 12225 46)^2) := bsq sGlobal1_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal1_hz70 : B (1524735695971823534271 / 62500000000000000) (609894278388729413841 / 25000000000000000) ((2 : ℝ) * ((s3am 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal1_hz69 (by norm_num) (by norm_num)

theorem sGlobal1_hz71 {c : ℝ} (hc : B (7 / 20) (71 / 200) c) : B (1296428406975233 / 2500000000000000) (521644599929538131 / 1000000000000000000) ((((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) / ((2 : ℝ) * ((s3am 12225 46)^2))) := bdiv (sGlobal1_hz68 hc) sGlobal1_hz70 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal1_hz72 {c : ℝ} (hc : B (7 / 20) (71 / 200) c) : B (1296428406975233 / 2500000000000000) (521644599929538131 / 1000000000000000000) (s3c1 12225 46 c) := by
    convert (sGlobal1_hz71 hc) using 1 <;>
      norm_num [s3c1] <;> ring

theorem sGlobal1_hz73 {c : ℝ} (hc : B (7 / 20) (71 / 200) c) : B (24552736689413483 / 40000000000000000) (307759567862194061 / 500000000000000000) (kdot c) := bkdot (sGlobal1_hz38 hc) sGlobal1_hz39.1 sGlobal1_hz47.2

theorem sGlobal1_hz74 : B (673535944662875787 / 1000000000000000000) (336767972331445667 / 500000000000000000) (kdot ((1296428406975233 / 2500000000000000))) := by
    constructor
    · apply bkdot_lower (q := (563051807856315489 / 1000000000000000000)) (a := (256404269477060289 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (17595368995509859 / 31250000000000000)) (a := (512808538954096159 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal1_hz75 : B (674681293322719039 / 1000000000000000000) (674681293322731687 / 1000000000000000000) (kdot ((521644599929538131 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (280342363391244429 / 500000000000000000)) (a := (25550471474316967 / 50000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (560684726782488857 / 1000000000000000000)) (a := (20440377179452779 / 40000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal1_hz76 {c : ℝ} (hc : B (7 / 20) (71 / 200) c) : B (673535944662875787 / 1000000000000000000) (674681293322731687 / 1000000000000000000) (kdot (s3c1 12225 46 c)) := bkdot (sGlobal1_hz72 hc) sGlobal1_hz74.1 sGlobal1_hz75.2

theorem sGlobal1_hz77 {c : ℝ} (hc : B (7 / 20) (71 / 200) c) : B (49 / 400) (5041 / 40000) (c^2) := bsq (sGlobal1_hz38 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal1_hz78 {c : ℝ} (hc : B (7 / 20) (71 / 200) c) : B (34959 / 40000) (351 / 400) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (sGlobal1_hz77 hc) (by norm_num) (by norm_num)

theorem sGlobal1_hz79 {c : ℝ} (hc : B (7 / 20) (71 / 200) c) : B (934866300601321279 / 1000000000000000000) (936749699759759731 / 1000000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (sGlobal1_hz78 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal1_hz80 : B (39119999999999765769 / 1600000000000000) (3912000000000000489 / 160000000000000) ((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (149450625 : ℝ)) sGlobal1_hz10 (by norm_num) (by norm_num)

theorem sGlobal1_hz81 {c : ℝ} (hc : B (7 / 20) (71 / 200) c) : B (143459538240439469 / 250000000000000000) (288293682793103687 / 500000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (sGlobal1_hz79 hc) (sGlobal1_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal1_hz82 {c : ℝ} (hc : B (7 / 20) (71 / 200) c) : B (7015171419957448030761 / 500000000000000000) (881097568036423253531 / 62500000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) := bmul sGlobal1_hz80 (sGlobal1_hz81 hc) (by norm_num) (by norm_num)

theorem sGlobal1_hz83 {c : ℝ} (hc : B (7 / 20) (71 / 200) c) : B (7015171419957448030761 / 1000000000000000000) (881097568036423253531 / 125000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) / (2 : ℝ)) := bdiv (sGlobal1_hz82 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal1_hz84 {c : ℝ} (hc : B (7 / 20) (71 / 200) c) : B (7015171419957448030761 / 1000000000000000000) (881097568036423253531 / 125000000000000000) (s3Cpa 12225 c) := by
    convert (sGlobal1_hz83 hc) using 1 <;>
      norm_num [s3Cpa, mA] <;> ring

theorem sGlobal1_hz85 {c : ℝ} (hc : B (7 / 20) (71 / 200) c) : B (74394296435367003 / 250000000000000000) (74544172578307301 / 250000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (sGlobal1_hz79 hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal1_hz86 {c : ℝ} (hc : B (7 / 20) (71 / 200) c) : B (26854555754045997 / 125000000000000000) (27313661647769723 / 125000000000000000) (c * (kdot c)) := bmul (sGlobal1_hz38 hc) (sGlobal1_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal1_hz87 {c : ℝ} (hc : B (7 / 20) (71 / 200) c) : B (19766973139827557 / 250000000000000000) (20835061070215307 / 250000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (sGlobal1_hz85 hc) (sGlobal1_hz86 hc) (by norm_num) (by norm_num)

theorem sGlobal1_hz88 {c : ℝ} (hc : B (7 / 20) (71 / 200) c) : B (386641994615024699901 / 200000000000000000) (2037668972667057279309 / 1000000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) := bmul sGlobal1_hz80 (sGlobal1_hz87 hc) (by norm_num) (by norm_num)

theorem sGlobal1_hz89 {c : ℝ} (hc : B (7 / 20) (71 / 200) c) : B (120825623317195218719 / 125000000000000000) (203766897266705727931 / 200000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) / (2 : ℝ)) := bdiv (sGlobal1_hz88 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal1_hz90 {c : ℝ} (hc : B (7 / 20) (71 / 200) c) : B (120825623317195218719 / 125000000000000000) (203766897266705727931 / 200000000000000000) (s3Cpp 12225 c) := by
    convert (sGlobal1_hz89 hc) using 1 <;>
      norm_num [s3Cpp, mA] <;> ring

theorem sGlobal1_hz91 {c : ℝ} (hc : B (7 / 20) (71 / 200) c) : B (3565158264945592869581 / 500000000000000000) (3581962827112562220237 / 500000000000000000) ((s3Cpa 12225 c) + (s3r1 12225 46)) := badd (sGlobal1_hz84 hc) sGlobal1_hz33 (by norm_num) (by norm_num)

theorem sGlobal1_hz92 {c : ℝ} (hc : B (7 / 20) (71 / 200) c) : B (32280223758099786713 / 500000000000000000) (64864756602413420471 / 1000000000000000000) (((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) := bdiv (sGlobal1_hz91 hc) sGlobal1_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal1_hz93 {c : ℝ} (hc : B (7 / 20) (71 / 200) c) : B (32341565270846816919 / 500000000000000000) (32493719813953740447 / 500000000000000000) ((((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) + (s3e0 12225 46)) := badd (sGlobal1_hz92 hc) sGlobal1_hz16 (by norm_num) (by norm_num)

theorem sGlobal1_hz94 {c : ℝ} (hc : B (7 / 20) (71 / 200) c) : B (32341565270846816919 / 500000000000000000) (32493719813953740447 / 500000000000000000) (s3Lam 12225 46 c) := by
    convert (sGlobal1_hz93 hc) using 1 <;>
      norm_num [s3Lam] <;> ring

theorem sGlobal1_hz95 {c : ℝ} (hc : B (7 / 20) (71 / 200) c) : B (130421049145006694419 / 125000000000000000) (1095597892956020914473 / 1000000000000000000) ((s3Cpp 12225 c) + (s3rpp 12225 46)) := badd (sGlobal1_hz90 hc) sGlobal1_hz37 (by norm_num) (by norm_num)

theorem sGlobal1_hz96 {c : ℝ} (hc : B (7 / 20) (71 / 200) c) : B (130421049145006694419 / 250000000000000000) (36958970169061396949 / 50000000000000000) (if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) := bweaken (bfirst (sGlobal1_hz95 hc) (sGlobal1_hz76 hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem sGlobal1_hz97 {c : ℝ} (hc : B (7 / 20) (71 / 200) c) : B (4183907376673779768863 / 1000000000000000000) (4223367309390919618753 / 1000000000000000000) ((s3Lam 12225 46 c)^2) := bsq (sGlobal1_hz94 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal1_hz98 {c : ℝ} (hc : B (7 / 20) (71 / 200) c) : B (134458129152987229 / 500000000000000000) (136056544317823947 / 500000000000000000) ((s3c1 12225 46 c)^2) := bsq (sGlobal1_hz72 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal1_hz99 {c : ℝ} (hc : B (7 / 20) (71 / 200) c) : B (363943455682176053 / 500000000000000000) (365541870847012771 / 500000000000000000) ((1 : ℝ) - ((s3c1 12225 46 c)^2)) := bsub (bpoint (1 : ℝ)) (sGlobal1_hz98 hc) (by norm_num) (by norm_num)

theorem sGlobal1_hz100 {c : ℝ} (hc : B (7 / 20) (71 / 200) c) : B (17063257735430853 / 20000000000000000) (427517175588895359 / 500000000000000000) (√((1 : ℝ) - ((s3c1 12225 46 c)^2))) := bsqrt (sGlobal1_hz99 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal1_hz101 {c : ℝ} (hc : B (7 / 20) (71 / 200) c) : B (134014512869846949 / 50000000000000000) (335771204528382837 / 125000000000000000) (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))) := bmul pi_mem (sGlobal1_hz100 hc) (by norm_num) (by norm_num)

theorem sGlobal1_hz102 {c : ℝ} (hc : B (7 / 20) (71 / 200) c) : B (1557573773542615113017 / 1000000000000000000) (157571266684101439093 / 100000000000000000) (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2))))) := bdiv (sGlobal1_hz97 hc) (sGlobal1_hz101 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal1_hz103 {c : ℝ} (hc : B (7 / 20) (71 / 200) c) : B (2079257970122641890693 / 1000000000000000000) (231489207022224232991 / 100000000000000000) ((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) := badd (sGlobal1_hz96 hc) (sGlobal1_hz102 hc) (by norm_num) (by norm_num)

theorem sGlobal1_hz104 : B (3762781186094069 / 250000000000000000) (376278118609407 / 25000000000000000) ((s3e0 12225 46)^2) := bsq sGlobal1_hz16 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal1_hz105 {c : ℝ} (hc : B (7 / 20) (71 / 200) c) : B (2079273021247386266969 / 1000000000000000000) (231490712134698670619 / 100000000000000000) (((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) := badd (sGlobal1_hz103 hc) sGlobal1_hz104 (by norm_num) (by norm_num)

theorem sGlobal1_hz106 {c : ℝ} (hc : B (7 / 20) (71 / 200) c) : B (21177700946986335371 / 10000000000000000) (1176702097400555488103 / 500000000000000000) ((((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) + (s3rs 12225 46 maskSlack)) := badd (sGlobal1_hz105 hc) sGlobal1_hz29 (by norm_num) (by norm_num)

theorem sGlobal1_hz107 {c : ℝ} (hc : B (7 / 20) (71 / 200) c) : B (21177700946986335371 / 10000000000000000) (1176702097400555488103 / 500000000000000000) (s3U 12225 46 maskSlack c) := by
    convert (sGlobal1_hz106 hc) using 1 <;>
      norm_num [s3U] <;> ring

theorem sGlobal1_hz108 {c : ℝ} (hc : B (7 / 20) (71 / 200) c) : B (444920789957534737467 / 500000000000000000) (188414215942207366811 / 200000000000000000) ((s3Cpp 12225 c) - (s3rpp 12225 46)) := bsub (sGlobal1_hz90 hc) sGlobal1_hz37 (by norm_num) (by norm_num)

theorem sGlobal1_hz109 {c : ℝ} (hc : B (7 / 20) (71 / 200) c) : B 0 0 (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ)) := bweaken (bmin (sGlobal1_hz108 hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem sGlobal1_hz110 {c : ℝ} (hc : B (7 / 20) (71 / 200) c) : B 0 0 ((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) := bmul (sGlobal1_hz76 hc) (sGlobal1_hz109 hc) (by norm_num) (by norm_num)

theorem sGlobal1_hz111 {c : ℝ} (hc : B (7 / 20) (71 / 200) c) : B (-376278118609407 / 25000000000000000) (-3762781186094069 / 250000000000000000) (((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) := bsub (sGlobal1_hz110 hc) sGlobal1_hz104 (by norm_num) (by norm_num)

theorem sGlobal1_hz112 {c : ℝ} (hc : B (7 / 20) (71 / 200) c) : B (-4814015572358580787 / 125000000000000000) (-38512124575991646407 / 1000000000000000000) ((((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) - (s3rs 12225 46 maskSlack)) := bsub (sGlobal1_hz111 hc) sGlobal1_hz29 (by norm_num) (by norm_num)

theorem sGlobal1_hz113 {c : ℝ} (hc : B (7 / 20) (71 / 200) c) : B (-4814015572358580787 / 125000000000000000) (-38512124575991646407 / 1000000000000000000) (s3L 12225 46 maskSlack c) := by
    convert (sGlobal1_hz112 hc) using 1 <;>
      norm_num [s3L] <;> ring

theorem sGlobal1_hz114 {c : ℝ} (hc : B (7 / 20) (71 / 200) c) : B 0 (1176702097400555488103 / 500000000000000000) |(s3U 12225 46 maskSlack c)| := bweaken (babs (sGlobal1_hz107 hc)) (by norm_num) (by norm_num)

theorem sGlobal1_hz115 {c : ℝ} (hc : B (7 / 20) (71 / 200) c) : B 0 (4814015572358580787 / 125000000000000000) |(s3L 12225 46 maskSlack c)| := bweaken (babs (sGlobal1_hz113 hc)) (by norm_num) (by norm_num)

theorem sGlobal1_hz116 {c : ℝ} (hc : B (7 / 20) (71 / 200) c) : B 0 (1176702097400555488103 / 500000000000000000) (max |(s3U 12225 46 maskSlack c)| |(s3L 12225 46 maskSlack c)|) := bweaken (bmax (sGlobal1_hz114 hc) (sGlobal1_hz115 hc)) (by norm_num) (by norm_num)

theorem sGlobal1_hz117 {c : ℝ} (hc : B (7 / 20) (71 / 200) c) : B 0 (1176702097400555488103 / 500000000000000000) (s3nks 12225 46 maskSlack c) := by
    convert (sGlobal1_hz116 hc) using 1 <;>
      norm_num [s3nks] <;> ring

theorem sGlobal1 {c : ℝ} (hc : B (7 / 20) (71 / 200) c) :
    0 < s3am 12225 46 ∧ 0 ≤ s3dm 12225 46 c ∧
    s3dm 12225 46 c ^ 2 ≤ 2 * s3ap 12225 46 ^ 2 ∧ s3c1 12225 46 c < 1 ∧
    0 ≤ s3Cpa 12225 c - s3r1 12225 46 ∧
    s3e0 12225 46 ≤ (s3Cpa 12225 c - s3r1 12225 46) / s3ap 12225 46 ∧
    s3nks 12225 46 maskSlack c ≤ 12225 * (48127 / 250000) := by

  refine ⟨lt_of_lt_of_le (by norm_num) sGlobal1_hz14.1,
    le_trans (by norm_num) (sGlobal1_hz64 hc).1, ?_,
    lt_of_le_of_lt (sGlobal1_hz72 hc).2 (by norm_num), ?_, ?_,
    le_trans (sGlobal1_hz117 hc).2 (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (sGlobal1_hz64 hc).1) (sGlobal1_hz64 hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) sGlobal1_hz9.1 2
    nlinarith only [h1, h2]
  · linarith only [(sGlobal1_hz84 hc).1, sGlobal1_hz33.2]
  · have hap : 0 < s3ap 12225 46 := lt_of_lt_of_le (by norm_num) sGlobal1_hz9.1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul sGlobal1_hz16.2 sGlobal1_hz9.2 (le_trans (by norm_num) sGlobal1_hz9.1) (by norm_num)
    linarith only [h, (sGlobal1_hz84 hc).1, sGlobal1_hz33.2]

end BstLean.Part255
