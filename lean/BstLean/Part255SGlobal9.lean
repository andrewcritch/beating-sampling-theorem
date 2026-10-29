import BstLean.Part255SGlobal5
import BstLean.Part255Numeric10
namespace BstLean.Part255
open Real BstLean.Part130 BstLean.Part182 BstLean.Part197 BstLean.Part246
theorem sGlobal9_hz0 : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal9_hz1 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) ((√(23 : ℝ)) / (12225 : ℝ)) := bdiv sGlobal9_hz0 (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal9_hz2 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) maskSlack := by
    convert sGlobal9_hz1 using 1 <;>
      norm_num [maskSlack] <;> ring

theorem sGlobal9_hz3 : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal9_hz4 : B (6395294793910793 / 500000000000000000) (12790589587821587 / 1000000000000000000) (√((2 / 12225) : ℝ)) := bsqrt (bpoint ((2 / 12225) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal9_hz5 : B (7230130686979 / 62500000000000000) (23136418198333 / 200000000000000000) (√((2 / 149450625) : ℝ)) := bsqrt (bpoint ((2 / 149450625) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal9_hz6 : B (2211334438749598093 / 20000000000000000) (110566721937479904651 / 1000000000000000000) (√(12225 : ℝ)) := bsqrt (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal9_hz7 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))) := bmul sGlobal9_hz3 sGlobal9_hz4 (by norm_num) (by norm_num)

theorem sGlobal9_hz8 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) ((√(12225 : ℝ)) + ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := badd sGlobal9_hz6 sGlobal9_hz7 (by norm_num) (by norm_num)

theorem sGlobal9_hz9 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) (s3ap 12225 46) := by
    convert sGlobal9_hz8 using 1 <;>
      norm_num [s3ap, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal9_hz10 : B (163599182004089 / 1000000000000000000) (16359918200409 / 100000000000000000) ((2 : ℝ) / (12225 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal9_hz11 : B (1222499983640081799591 / 100000000000000000) (12224999836400817995911 / 1000000000000000000) ((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ))) := bsub (bpoint (12225 : ℝ)) sGlobal9_hz10 (by norm_num) (by norm_num)

theorem sGlobal9_hz12 : B (110566721197658827907 / 1000000000000000000) (27641680299414706977 / 250000000000000000) (√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) := bsqrt sGlobal9_hz11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal9_hz13 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) ((√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) - ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bsub sGlobal9_hz12 sGlobal9_hz7 (by norm_num) (by norm_num)

theorem sGlobal9_hz14 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) (s3am 12225 46) := by
    convert sGlobal9_hz13 using 1 <;>
      norm_num [s3am, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal9_hz15 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√((2 / 12225) : ℝ)) * (√(92 : ℝ))) := bmul sGlobal9_hz4 sGlobal9_hz3 (by norm_num) (by norm_num)

theorem sGlobal9_hz16 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) (s3e0 12225 46) := by
    convert sGlobal9_hz15 using 1 <;>
      norm_num [s3e0, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal9_hz17 : B (250196148528560847 / 500000000000000000) (100078459411424339 / 200000000000000000) (((1 / 2) : ℝ) + maskSlack) := badd (bpoint ((1 / 2) : ℝ)) sGlobal9_hz2 (by norm_num) (by norm_num)

theorem sGlobal9_hz18 : B (59827153232297998295487 / 800000000000000) (23930861292919199366019 / 320000000000000) ((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack)) := bmul (bpoint (149450625 : ℝ)) sGlobal9_hz17 (by norm_num) (by norm_num)

theorem sGlobal9_hz19 : B (1729554180017180009583 / 200000000000000000) (8647770900085900056557 / 1000000000000000000) (√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) := bsqrt sGlobal9_hz18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal9_hz20 : B (4328681281566262743499 / 500000000000000000) (8657362563132525495641 / 1000000000000000000) ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))) := badd sGlobal9_hz19 sGlobal9_hz3 (by norm_num) (by norm_num)

theorem sGlobal9_hz21 : B (110732771457999278473 / 1000000000000000000) (55366385728999643621 / 500000000000000000) ((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ)))) := bmul sGlobal9_hz4 sGlobal9_hz20 (by norm_num) (by norm_num)

theorem sGlobal9_hz22 : B (209099159 / 15625000000000000) (13382346177 / 1000000000000000000) ((2 : ℝ) / (149450625 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (149450625 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal9_hz23 : B (2452349334953899930479 / 200000000000000000) (12261746674769501594427 / 1000000000000000000) (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2) := bsq sGlobal9_hz21 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal9_hz24 : B (82045469362091 / 500000000000000000) (32818187747289 / 200000000000000000) (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2)) := bmul sGlobal9_hz22 sGlobal9_hz23 (by norm_num) (by norm_num)

theorem sGlobal9_hz25 : B (82045469362091 / 250000000000000000) (32818187747289 / 100000000000000000) ((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) := bmul (bpoint (2 : ℝ)) sGlobal9_hz24 (by norm_num) (by norm_num)

theorem sGlobal9_hz26 : B (117258080744995992792057 / 1000000000000000000) (58629040372497996396029 / 500000000000000000) (√(13749457500 : ℝ)) := bsqrt (bpoint (13749457500 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal9_hz27 : B (117304080744995992792057 / 1000000000000000000) (58652040372497996396029 / 500000000000000000) ((√(13749457500 : ℝ)) + (46 : ℝ)) := badd sGlobal9_hz26 (bpoint (46 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal9_hz28 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal9_hz25 sGlobal9_hz27 (by norm_num) (by norm_num)

theorem sGlobal9_hz29 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (s3rs 12225 46 maskSlack) := by
    convert sGlobal9_hz28 using 1 <;>
      norm_num [s3rs, s3pp, s3K, mA, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal9_hz30 : B (490797546012267 / 1000000000000000000) (49079754601227 / 100000000000000000) ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (3 : ℝ)) sGlobal9_hz10 (by norm_num) (by norm_num)

theorem sGlobal9_hz31 : B (490797546012267 / 500000000000000000) (49079754601227 / 50000000000000000) ((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal9_hz30 (by norm_num) (by norm_num)

theorem sGlobal9_hz32 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal9_hz31 sGlobal9_hz27 (by norm_num) (by norm_num)

theorem sGlobal9_hz33 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (s3r1 12225 46) := by
    convert sGlobal9_hz32 using 1 <;>
      norm_num [s3r1, mA] <;> ring

theorem sGlobal9_hz34 : B (163599182004089 / 500000000000000000) (16359918200409 / 50000000000000000) ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (2 : ℝ)) sGlobal9_hz10 (by norm_num) (by norm_num)

theorem sGlobal9_hz35 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal9_hz34 (by norm_num) (by norm_num)

theorem sGlobal9_hz36 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal9_hz35 sGlobal9_hz27 (by norm_num) (by norm_num)

theorem sGlobal9_hz37 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (s3rpp 12225 46) := by
    convert sGlobal9_hz36 using 1 <;>
      norm_num [s3rpp, mA] <;> ring

theorem sGlobal9_hz38 {c : ℝ} (hc : B (39 / 100) (79 / 200) c) : B (39 / 100) (79 / 200) c := hc

theorem sGlobal9_hz39 : B (627524996667760753 / 1000000000000000000) (627524996712576683 / 1000000000000000000) (kdot ((39 / 100))) := by
    constructor
    · apply bkdot_lower (q := (331228365657030253 / 500000000000000000)) (a := (585082367057198287 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (132491346262812101 / 200000000000000000)) (a := (58508236698680159 / 100000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal9_hz40 : B (1521 / 10000) (1521 / 10000) (((39 / 100) : ℝ)^2) := bsq (bpoint ((39 / 100) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal9_hz41 : B (8479 / 10000) (8479 / 10000) ((1 : ℝ) - (((39 / 100) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal9_hz40 (by norm_num) (by norm_num)

theorem sGlobal9_hz42 : B (460407428263272051 / 500000000000000000) (920814856526544103 / 1000000000000000000) (√((1 : ℝ) - (((39 / 100) : ℝ)^2))) := bsqrt sGlobal9_hz41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal9_hz43 : B (293104472177307789 / 1000000000000000000) (293104472177307791 / 1000000000000000000) ((√((1 : ℝ) - (((39 / 100) : ℝ)^2))) / Real.pi) := bdiv sGlobal9_hz42 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal9_hz44 : B (244734748700426693 / 1000000000000000000) (244734748717904907 / 1000000000000000000) (((39 / 100) : ℝ) * (kdot ((39 / 100)))) := bmul (bpoint ((39 / 100) : ℝ)) sGlobal9_hz39 (by norm_num) (by norm_num)

theorem sGlobal9_hz45 : B (268919610438867241 / 500000000000000000) (268919610447606349 / 500000000000000000) (((√((1 : ℝ) - (((39 / 100) : ℝ)^2))) / Real.pi) + (((39 / 100) : ℝ) * (kdot ((39 / 100))))) := badd sGlobal9_hz43 sGlobal9_hz44 (by norm_num) (by norm_num)

theorem sGlobal9_hz46 : B (268919610438867241 / 500000000000000000) (268919610447606349 / 500000000000000000) (kappa ((39 / 100))) := by rw [kappa_eq]; exact sGlobal9_hz45

theorem sGlobal9_hz47 : B (629255411448048649 / 1000000000000000000) (629255411481595569 / 1000000000000000000) (kdot ((79 / 200))) := by
    constructor
    · apply bkdot_lower (q := (164638193524543659 / 250000000000000000)) (a := (582364237876490461 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (131710554819634927 / 200000000000000000)) (a := (145591059455948771 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal9_hz48 : B (6241 / 40000) (6241 / 40000) (((79 / 200) : ℝ)^2) := bsq (bpoint ((79 / 200) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal9_hz49 : B (33759 / 40000) (33759 / 40000) ((1 : ℝ) - (((79 / 200) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal9_hz48 (by norm_num) (by norm_num)

theorem sGlobal9_hz50 : B (918681119866953617 / 1000000000000000000) (459340559933476809 / 500000000000000000) (√((1 : ℝ) - (((79 / 200) : ℝ)^2))) := bsqrt sGlobal9_hz49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal9_hz51 : B (228457252112537 / 781250000000000) (146212641352023681 / 500000000000000000) ((√((1 : ℝ) - (((79 / 200) : ℝ)^2))) / Real.pi) := bdiv sGlobal9_hz50 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal9_hz52 : B (15534742970123701 / 62500000000000000) (994223550140921 / 4000000000000000) (((79 / 200) : ℝ) * (kdot ((79 / 200)))) := bmul (bpoint ((79 / 200) : ℝ)) sGlobal9_hz47 (by norm_num) (by norm_num)

theorem sGlobal9_hz53 : B (33811323139126661 / 62500000000000000) (135245292559819403 / 250000000000000000) (((√((1 : ℝ) - (((79 / 200) : ℝ)^2))) / Real.pi) + (((79 / 200) : ℝ) * (kdot ((79 / 200))))) := badd sGlobal9_hz51 sGlobal9_hz52 (by norm_num) (by norm_num)

theorem sGlobal9_hz54 : B (33811323139126661 / 62500000000000000) (135245292559819403 / 250000000000000000) (kappa ((79 / 200))) := by rw [kappa_eq]; exact sGlobal9_hz53

theorem sGlobal9_hz55 {c : ℝ} (hc : B (39 / 100) (79 / 200) c) : B (268919610438867241 / 500000000000000000) (135245292559819403 / 250000000000000000) (kappa c) := bkappa (sGlobal9_hz38 hc) (by norm_num) (by norm_num) sGlobal9_hz46.1 sGlobal9_hz54.2

theorem sGlobal9_hz56 : B 24450 24450 ((2 : ℝ) * (12225 : ℝ)) := bmul (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal9_hz57 {c : ℝ} (hc : B (39 / 100) (79 / 200) c) : B (114754707440180597 / 250000000000000000) (231080389561132759 / 500000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (sGlobal9_hz55 hc) (by norm_num) (by norm_num)

theorem sGlobal9_hz58 {c : ℝ} (hc : B (39 / 100) (79 / 200) c) : B (56115051938248311933 / 5000000000000000) (112998310495393919151 / 10000000000000000) (((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) := bmul sGlobal9_hz56 (sGlobal9_hz57 hc) (by norm_num) (by norm_num)

theorem sGlobal9_hz59 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (4 : ℝ)) sGlobal9_hz10 (by norm_num) (by norm_num)

theorem sGlobal9_hz60 {c : ℝ} (hc : B (39 / 100) (79 / 200) c) : B (35071905416415419907 / 3125000000000000) (1412478799392832987343 / 125000000000000000) ((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bsub (sGlobal9_hz58 hc) sGlobal9_hz59 (by norm_num) (by norm_num)

theorem sGlobal9_hz61 {c : ℝ} (hc : B (39 / 100) (79 / 200) c) : B (52969353718100370953 / 500000000000000000) (106300660370209666439 / 1000000000000000000) (√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) := bsqrt (sGlobal9_hz60 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal9_hz62 : B (30670756373515103 / 125000000000000000) (122683025494060423 / 500000000000000000) ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal9_hz7 (by norm_num) (by norm_num)

theorem sGlobal9_hz63 {c : ℝ} (hc : B (39 / 100) (79 / 200) c) : B (5284667069260631053 / 50000000000000000) (21211058863844309123 / 200000000000000000) ((√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) - ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))))) := bsub (sGlobal9_hz61 hc) sGlobal9_hz62 (by norm_num) (by norm_num)

theorem sGlobal9_hz64 {c : ℝ} (hc : B (39 / 100) (79 / 200) c) : B (5284667069260631053 / 50000000000000000) (21211058863844309123 / 200000000000000000) (s3dm 12225 46 c) := by
    convert (sGlobal9_hz63 hc) using 1 <;>
      norm_num [s3dm, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal9_hz65 : B (6126072185528622723889 / 500000000000000000) (2450428874211449090087 / 200000000000000000) ((s3ap 12225 46)^2) := bsq sGlobal9_hz9 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal9_hz66 : B (6126072185528622723889 / 250000000000000000) (2450428874211449090087 / 100000000000000000) ((2 : ℝ) * ((s3ap 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal9_hz65 (by norm_num) (by norm_num)

theorem sGlobal9_hz67 {c : ℝ} (hc : B (39 / 100) (79 / 200) c) : B (2234216482634219795757 / 200000000000000000) (11247725453136705844569 / 1000000000000000000) ((s3dm 12225 46 c)^2) := bsq (sGlobal9_hz64 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal9_hz68 {c : ℝ} (hc : B (39 / 100) (79 / 200) c) : B (13256563288977785050987 / 1000000000000000000) (2666641265788678384417 / 200000000000000000) (((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) := bsub sGlobal9_hz66 (sGlobal9_hz67 hc) (by norm_num) (by norm_num)

theorem sGlobal9_hz69 : B (1524735695971823534271 / 125000000000000000) (609894278388729413841 / 50000000000000000) ((s3am 12225 46)^2) := bsq sGlobal9_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal9_hz70 : B (1524735695971823534271 / 62500000000000000) (609894278388729413841 / 25000000000000000) ((2 : ℝ) * ((s3am 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal9_hz69 (by norm_num) (by norm_num)

theorem sGlobal9_hz71 {c : ℝ} (hc : B (39 / 100) (79 / 200) c) : B (135848988082001089 / 250000000000000000) (136634401254019289 / 250000000000000000) ((((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) / ((2 : ℝ) * ((s3am 12225 46)^2))) := bdiv (sGlobal9_hz68 hc) sGlobal9_hz70 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal9_hz72 {c : ℝ} (hc : B (39 / 100) (79 / 200) c) : B (135848988082001089 / 250000000000000000) (136634401254019289 / 250000000000000000) (s3c1 12225 46 c) := by
    convert (sGlobal9_hz71 hc) using 1 <;>
      norm_num [s3c1] <;> ring

theorem sGlobal9_hz73 {c : ℝ} (hc : B (39 / 100) (79 / 200) c) : B (627524996667760753 / 1000000000000000000) (629255411481595569 / 1000000000000000000) (kdot c) := bkdot (sGlobal9_hz38 hc) sGlobal9_hz39.1 sGlobal9_hz47.2

theorem sGlobal9_hz74 : B (682861759134029287 / 1000000000000000000) (136572351826806429 / 200000000000000000) (kdot ((135848988082001089 / 250000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (108783041124503799 / 200000000000000000)) (a := (498159583838461969 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (271957602811259497 / 500000000000000000)) (a := (249079791919228741 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal9_hz75 : B (684054449606456049 / 1000000000000000000) (342027224803229173 / 500000000000000000) (kdot ((136634401254019289 / 250000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (54148994481903813 / 100000000000000000)) (a := (496286110025370741 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (541489944819038129 / 1000000000000000000)) (a := (99257222005073427 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal9_hz76 {c : ℝ} (hc : B (39 / 100) (79 / 200) c) : B (682861759134029287 / 1000000000000000000) (342027224803229173 / 500000000000000000) (kdot (s3c1 12225 46 c)) := bkdot (sGlobal9_hz72 hc) sGlobal9_hz74.1 sGlobal9_hz75.2

theorem sGlobal9_hz77 {c : ℝ} (hc : B (39 / 100) (79 / 200) c) : B (1521 / 10000) (6241 / 40000) (c^2) := bsq (sGlobal9_hz38 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal9_hz78 {c : ℝ} (hc : B (39 / 100) (79 / 200) c) : B (33759 / 40000) (8479 / 10000) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (sGlobal9_hz77 hc) (by norm_num) (by norm_num)

theorem sGlobal9_hz79 {c : ℝ} (hc : B (39 / 100) (79 / 200) c) : B (918681119866953617 / 1000000000000000000) (920814856526544103 / 1000000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (sGlobal9_hz78 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal9_hz80 : B (39119999999999765769 / 1600000000000000) (3912000000000000489 / 160000000000000) ((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (149450625 : ℝ)) sGlobal9_hz10 (by norm_num) (by norm_num)

theorem sGlobal9_hz81 {c : ℝ} (hc : B (39 / 100) (79 / 200) c) : B (115299073336648957 / 200000000000000000) (579427731441976897 / 1000000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (sGlobal9_hz79 hc) (sGlobal9_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal9_hz82 {c : ℝ} (hc : B (39 / 100) (79 / 200) c) : B (14095311715405250597571 / 1000000000000000000) (14167008033756336902527 / 1000000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) := bmul sGlobal9_hz80 (sGlobal9_hz81 hc) (by norm_num) (by norm_num)

theorem sGlobal9_hz83 {c : ℝ} (hc : B (39 / 100) (79 / 200) c) : B (1409531171540525059757 / 200000000000000000) (110679750263721382051 / 15625000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) / (2 : ℝ)) := bdiv (sGlobal9_hz82 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal9_hz84 {c : ℝ} (hc : B (39 / 100) (79 / 200) c) : B (1409531171540525059757 / 200000000000000000) (110679750263721382051 / 15625000000000000) (s3Cpa 12225 c) := by
    convert (sGlobal9_hz83 hc) using 1 <;>
      norm_num [s3Cpa, mA] <;> ring

theorem sGlobal9_hz85 {c : ℝ} (hc : B (39 / 100) (79 / 200) c) : B (228457252112537 / 781250000000000) (293104472177307791 / 1000000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (sGlobal9_hz79 hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal9_hz86 {c : ℝ} (hc : B (39 / 100) (79 / 200) c) : B (244734748700426693 / 1000000000000000000) (994223550140921 / 4000000000000000) (c * (kdot c)) := bmul (sGlobal9_hz38 hc) (sGlobal9_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal9_hz87 {c : ℝ} (hc : B (39 / 100) (79 / 200) c) : B (4386939516881711 / 100000000000000000) (24184861738440549 / 500000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (sGlobal9_hz85 hc) (sGlobal9_hz86 hc) (by norm_num) (by norm_num)

theorem sGlobal9_hz88 {c : ℝ} (hc : B (39 / 100) (79 / 200) c) : B (1072606711877571917267 / 1000000000000000000) (118263973900974299393 / 100000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) := bmul sGlobal9_hz80 (sGlobal9_hz87 hc) (by norm_num) (by norm_num)

theorem sGlobal9_hz89 {c : ℝ} (hc : B (39 / 100) (79 / 200) c) : B (536303355938785958633 / 1000000000000000000) (118263973900974299393 / 200000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) / (2 : ℝ)) := bdiv (sGlobal9_hz88 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal9_hz90 {c : ℝ} (hc : B (39 / 100) (79 / 200) c) : B (536303355938785958633 / 1000000000000000000) (118263973900974299393 / 200000000000000000) (s3Cpp 12225 c) := by
    convert (sGlobal9_hz89 hc) using 1 <;>
      norm_num [s3Cpp, mA] <;> ring

theorem sGlobal9_hz91 {c : ℝ} (hc : B (39 / 100) (79 / 200) c) : B (3581400483818181503593 / 500000000000000000) (719864912681190686349 / 100000000000000000) ((s3Cpa 12225 c) + (s3r1 12225 46)) := badd (sGlobal9_hz84 hc) sGlobal9_hz33 (by norm_num) (by norm_num)

theorem sGlobal9_hz92 {c : ℝ} (hc : B (39 / 100) (79 / 200) c) : B (12970914657196236299 / 200000000000000000) (32589577699025966117 / 500000000000000000) (((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) := bdiv (sGlobal9_hz91 hc) sGlobal9_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal9_hz93 {c : ℝ} (hc : B (39 / 100) (79 / 200) c) : B (64977256311475241907 / 1000000000000000000) (65301838423545992657 / 1000000000000000000) ((((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) + (s3e0 12225 46)) := badd (sGlobal9_hz92 hc) sGlobal9_hz16 (by norm_num) (by norm_num)

theorem sGlobal9_hz94 {c : ℝ} (hc : B (39 / 100) (79 / 200) c) : B (64977256311475241907 / 1000000000000000000) (65301838423545992657 / 1000000000000000000) (s3Lam 12225 46 c) := by
    convert (sGlobal9_hz93 hc) using 1 <;>
      norm_num [s3Lam] <;> ring

theorem sGlobal9_hz95 {c : ℝ} (hc : B (39 / 100) (79 / 200) c) : B (613066762561277764233 / 1000000000000000000) (668083276127363771783 / 1000000000000000000) ((s3Cpp 12225 c) + (s3rpp 12225 46)) := badd (sGlobal9_hz90 hc) sGlobal9_hz37 (by norm_num) (by norm_num)

theorem sGlobal9_hz96 {c : ℝ} (hc : B (39 / 100) (79 / 200) c) : B (76633345320159720529 / 250000000000000000) (457005337742583357361 / 1000000000000000000) (if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) := bweaken (bfirst (sGlobal9_hz95 hc) (sGlobal9_hz76 hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem sGlobal9_hz97 {c : ℝ} (hc : B (39 / 100) (79 / 200) c) : B (2111021918883574579561 / 500000000000000000) (852866020298981555093 / 200000000000000000) ((s3Lam 12225 46 c)^2) := bsq (sGlobal9_hz94 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal9_hz98 {c : ℝ} (hc : B (39 / 100) (79 / 200) c) : B (147639580503229391 / 500000000000000000) (149351676848354783 / 500000000000000000) ((s3c1 12225 46 c)^2) := bsq (sGlobal9_hz72 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal9_hz99 {c : ℝ} (hc : B (39 / 100) (79 / 200) c) : B (350648323151645217 / 500000000000000000) (352360419496770609 / 500000000000000000) ((1 : ℝ) - ((s3c1 12225 46 c)^2)) := bsub (bpoint (1 : ℝ)) (sGlobal9_hz98 hc) (by norm_num) (by norm_num)

theorem sGlobal9_hz100 {c : ℝ} (hc : B (39 / 100) (79 / 200) c) : B (167486912480144601 / 200000000000000000) (839476526767450013 / 1000000000000000000) (√((1 : ℝ) - ((s3c1 12225 46 c)^2))) := bsqrt (sGlobal9_hz99 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal9_hz101 {c : ℝ} (hc : B (39 / 100) (79 / 200) c) : B (657719567275073669 / 250000000000000000) (131864664467684819 / 50000000000000000) (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))) := bmul pi_mem (sGlobal9_hz100 hc) (by norm_num) (by norm_num)

theorem sGlobal9_hz102 {c : ℝ} (hc : B (39 / 100) (79 / 200) c) : B (400225095821805324513 / 250000000000000000) (1620877009620524727117 / 1000000000000000000) (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2))))) := bdiv (sGlobal9_hz97 hc) (sGlobal9_hz101 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal9_hz103 {c : ℝ} (hc : B (39 / 100) (79 / 200) c) : B (238429220570982522521 / 125000000000000000) (1038941173681554042239 / 500000000000000000) ((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) := badd (sGlobal9_hz96 hc) (sGlobal9_hz102 hc) (by norm_num) (by norm_num)

theorem sGlobal9_hz104 : B (3762781186094069 / 250000000000000000) (376278118609407 / 25000000000000000) ((s3e0 12225 46)^2) := bsq sGlobal9_hz16 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal9_hz105 {c : ℝ} (hc : B (39 / 100) (79 / 200) c) : B (476862203923151139111 / 250000000000000000) (1038948699243926230379 / 500000000000000000) (((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) := badd (sGlobal9_hz103 hc) sGlobal9_hz104 (by norm_num) (by norm_num)

theorem sGlobal9_hz106 {c : ℝ} (hc : B (39 / 100) (79 / 200) c) : B (77837835565754073063 / 40000000000000000) (1058197235970988365387 / 500000000000000000) ((((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) + (s3rs 12225 46 maskSlack)) := badd (sGlobal9_hz105 hc) sGlobal9_hz29 (by norm_num) (by norm_num)

theorem sGlobal9_hz107 {c : ℝ} (hc : B (39 / 100) (79 / 200) c) : B (77837835565754073063 / 40000000000000000) (1058197235970988365387 / 500000000000000000) (s3U 12225 46 maskSlack c) := by
    convert (sGlobal9_hz106 hc) using 1 <;>
      norm_num [s3U] <;> ring

theorem sGlobal9_hz108 {c : ℝ} (hc : B (39 / 100) (79 / 200) c) : B (91907989863258736763 / 200000000000000000) (102911292576475938273 / 200000000000000000) ((s3Cpp 12225 c) - (s3rpp 12225 46)) := bsub (sGlobal9_hz90 hc) sGlobal9_hz37 (by norm_num) (by norm_num)

theorem sGlobal9_hz109 {c : ℝ} (hc : B (39 / 100) (79 / 200) c) : B 0 0 (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ)) := bweaken (bmin (sGlobal9_hz108 hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem sGlobal9_hz110 {c : ℝ} (hc : B (39 / 100) (79 / 200) c) : B 0 0 ((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) := bmul (sGlobal9_hz76 hc) (sGlobal9_hz109 hc) (by norm_num) (by norm_num)

theorem sGlobal9_hz111 {c : ℝ} (hc : B (39 / 100) (79 / 200) c) : B (-376278118609407 / 25000000000000000) (-3762781186094069 / 250000000000000000) (((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) := bsub (sGlobal9_hz110 hc) sGlobal9_hz104 (by norm_num) (by norm_num)

theorem sGlobal9_hz112 {c : ℝ} (hc : B (39 / 100) (79 / 200) c) : B (-4814015572358580787 / 125000000000000000) (-38512124575991646407 / 1000000000000000000) ((((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) - (s3rs 12225 46 maskSlack)) := bsub (sGlobal9_hz111 hc) sGlobal9_hz29 (by norm_num) (by norm_num)

theorem sGlobal9_hz113 {c : ℝ} (hc : B (39 / 100) (79 / 200) c) : B (-4814015572358580787 / 125000000000000000) (-38512124575991646407 / 1000000000000000000) (s3L 12225 46 maskSlack c) := by
    convert (sGlobal9_hz112 hc) using 1 <;>
      norm_num [s3L] <;> ring

theorem sGlobal9_hz114 {c : ℝ} (hc : B (39 / 100) (79 / 200) c) : B 0 (1058197235970988365387 / 500000000000000000) |(s3U 12225 46 maskSlack c)| := bweaken (babs (sGlobal9_hz107 hc)) (by norm_num) (by norm_num)

theorem sGlobal9_hz115 {c : ℝ} (hc : B (39 / 100) (79 / 200) c) : B 0 (4814015572358580787 / 125000000000000000) |(s3L 12225 46 maskSlack c)| := bweaken (babs (sGlobal9_hz113 hc)) (by norm_num) (by norm_num)

theorem sGlobal9_hz116 {c : ℝ} (hc : B (39 / 100) (79 / 200) c) : B 0 (1058197235970988365387 / 500000000000000000) (max |(s3U 12225 46 maskSlack c)| |(s3L 12225 46 maskSlack c)|) := bweaken (bmax (sGlobal9_hz114 hc) (sGlobal9_hz115 hc)) (by norm_num) (by norm_num)

theorem sGlobal9_hz117 {c : ℝ} (hc : B (39 / 100) (79 / 200) c) : B 0 (1058197235970988365387 / 500000000000000000) (s3nks 12225 46 maskSlack c) := by
    convert (sGlobal9_hz116 hc) using 1 <;>
      norm_num [s3nks] <;> ring

theorem sGlobal9 {c : ℝ} (hc : B (39 / 100) (79 / 200) c) :
    0 < s3am 12225 46 ∧ 0 ≤ s3dm 12225 46 c ∧
    s3dm 12225 46 c ^ 2 ≤ 2 * s3ap 12225 46 ^ 2 ∧ s3c1 12225 46 c < 1 ∧
    0 ≤ s3Cpa 12225 c - s3r1 12225 46 ∧
    s3e0 12225 46 ≤ (s3Cpa 12225 c - s3r1 12225 46) / s3ap 12225 46 ∧
    s3nks 12225 46 maskSlack c ≤ 12225 * (173121 / 1000000) := by

  refine ⟨lt_of_lt_of_le (by norm_num) sGlobal9_hz14.1,
    le_trans (by norm_num) (sGlobal9_hz64 hc).1, ?_,
    lt_of_le_of_lt (sGlobal9_hz72 hc).2 (by norm_num), ?_, ?_,
    le_trans (sGlobal9_hz117 hc).2 (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (sGlobal9_hz64 hc).1) (sGlobal9_hz64 hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) sGlobal9_hz9.1 2
    nlinarith only [h1, h2]
  · linarith only [(sGlobal9_hz84 hc).1, sGlobal9_hz33.2]
  · have hap : 0 < s3ap 12225 46 := lt_of_lt_of_le (by norm_num) sGlobal9_hz9.1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul sGlobal9_hz16.2 sGlobal9_hz9.2 (le_trans (by norm_num) sGlobal9_hz9.1) (by norm_num)
    linarith only [h, (sGlobal9_hz84 hc).1, sGlobal9_hz33.2]

end BstLean.Part255
