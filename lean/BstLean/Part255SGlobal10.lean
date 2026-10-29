import BstLean.Part255SGlobal6
import BstLean.Part255Numeric10
namespace BstLean.Part255
open Real BstLean.Part130 BstLean.Part182 BstLean.Part197 BstLean.Part246
theorem sGlobal10_hz0 : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal10_hz1 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) ((√(23 : ℝ)) / (12225 : ℝ)) := bdiv sGlobal10_hz0 (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal10_hz2 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) maskSlack := by
    convert sGlobal10_hz1 using 1 <;>
      norm_num [maskSlack] <;> ring

theorem sGlobal10_hz3 : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal10_hz4 : B (6395294793910793 / 500000000000000000) (12790589587821587 / 1000000000000000000) (√((2 / 12225) : ℝ)) := bsqrt (bpoint ((2 / 12225) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal10_hz5 : B (7230130686979 / 62500000000000000) (23136418198333 / 200000000000000000) (√((2 / 149450625) : ℝ)) := bsqrt (bpoint ((2 / 149450625) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal10_hz6 : B (2211334438749598093 / 20000000000000000) (110566721937479904651 / 1000000000000000000) (√(12225 : ℝ)) := bsqrt (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal10_hz7 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))) := bmul sGlobal10_hz3 sGlobal10_hz4 (by norm_num) (by norm_num)

theorem sGlobal10_hz8 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) ((√(12225 : ℝ)) + ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := badd sGlobal10_hz6 sGlobal10_hz7 (by norm_num) (by norm_num)

theorem sGlobal10_hz9 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) (s3ap 12225 46) := by
    convert sGlobal10_hz8 using 1 <;>
      norm_num [s3ap, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal10_hz10 : B (163599182004089 / 1000000000000000000) (16359918200409 / 100000000000000000) ((2 : ℝ) / (12225 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal10_hz11 : B (1222499983640081799591 / 100000000000000000) (12224999836400817995911 / 1000000000000000000) ((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ))) := bsub (bpoint (12225 : ℝ)) sGlobal10_hz10 (by norm_num) (by norm_num)

theorem sGlobal10_hz12 : B (110566721197658827907 / 1000000000000000000) (27641680299414706977 / 250000000000000000) (√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) := bsqrt sGlobal10_hz11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal10_hz13 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) ((√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) - ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bsub sGlobal10_hz12 sGlobal10_hz7 (by norm_num) (by norm_num)

theorem sGlobal10_hz14 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) (s3am 12225 46) := by
    convert sGlobal10_hz13 using 1 <;>
      norm_num [s3am, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal10_hz15 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√((2 / 12225) : ℝ)) * (√(92 : ℝ))) := bmul sGlobal10_hz4 sGlobal10_hz3 (by norm_num) (by norm_num)

theorem sGlobal10_hz16 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) (s3e0 12225 46) := by
    convert sGlobal10_hz15 using 1 <;>
      norm_num [s3e0, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal10_hz17 : B (250196148528560847 / 500000000000000000) (100078459411424339 / 200000000000000000) (((1 / 2) : ℝ) + maskSlack) := badd (bpoint ((1 / 2) : ℝ)) sGlobal10_hz2 (by norm_num) (by norm_num)

theorem sGlobal10_hz18 : B (59827153232297998295487 / 800000000000000) (23930861292919199366019 / 320000000000000) ((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack)) := bmul (bpoint (149450625 : ℝ)) sGlobal10_hz17 (by norm_num) (by norm_num)

theorem sGlobal10_hz19 : B (1729554180017180009583 / 200000000000000000) (8647770900085900056557 / 1000000000000000000) (√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) := bsqrt sGlobal10_hz18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal10_hz20 : B (4328681281566262743499 / 500000000000000000) (8657362563132525495641 / 1000000000000000000) ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))) := badd sGlobal10_hz19 sGlobal10_hz3 (by norm_num) (by norm_num)

theorem sGlobal10_hz21 : B (110732771457999278473 / 1000000000000000000) (55366385728999643621 / 500000000000000000) ((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ)))) := bmul sGlobal10_hz4 sGlobal10_hz20 (by norm_num) (by norm_num)

theorem sGlobal10_hz22 : B (209099159 / 15625000000000000) (13382346177 / 1000000000000000000) ((2 : ℝ) / (149450625 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (149450625 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal10_hz23 : B (2452349334953899930479 / 200000000000000000) (12261746674769501594427 / 1000000000000000000) (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2) := bsq sGlobal10_hz21 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal10_hz24 : B (82045469362091 / 500000000000000000) (32818187747289 / 200000000000000000) (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2)) := bmul sGlobal10_hz22 sGlobal10_hz23 (by norm_num) (by norm_num)

theorem sGlobal10_hz25 : B (82045469362091 / 250000000000000000) (32818187747289 / 100000000000000000) ((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) := bmul (bpoint (2 : ℝ)) sGlobal10_hz24 (by norm_num) (by norm_num)

theorem sGlobal10_hz26 : B (117258080744995992792057 / 1000000000000000000) (58629040372497996396029 / 500000000000000000) (√(13749457500 : ℝ)) := bsqrt (bpoint (13749457500 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal10_hz27 : B (117304080744995992792057 / 1000000000000000000) (58652040372497996396029 / 500000000000000000) ((√(13749457500 : ℝ)) + (46 : ℝ)) := badd sGlobal10_hz26 (bpoint (46 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal10_hz28 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal10_hz25 sGlobal10_hz27 (by norm_num) (by norm_num)

theorem sGlobal10_hz29 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (s3rs 12225 46 maskSlack) := by
    convert sGlobal10_hz28 using 1 <;>
      norm_num [s3rs, s3pp, s3K, mA, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal10_hz30 : B (490797546012267 / 1000000000000000000) (49079754601227 / 100000000000000000) ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (3 : ℝ)) sGlobal10_hz10 (by norm_num) (by norm_num)

theorem sGlobal10_hz31 : B (490797546012267 / 500000000000000000) (49079754601227 / 50000000000000000) ((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal10_hz30 (by norm_num) (by norm_num)

theorem sGlobal10_hz32 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal10_hz31 sGlobal10_hz27 (by norm_num) (by norm_num)

theorem sGlobal10_hz33 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (s3r1 12225 46) := by
    convert sGlobal10_hz32 using 1 <;>
      norm_num [s3r1, mA] <;> ring

theorem sGlobal10_hz34 : B (163599182004089 / 500000000000000000) (16359918200409 / 50000000000000000) ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (2 : ℝ)) sGlobal10_hz10 (by norm_num) (by norm_num)

theorem sGlobal10_hz35 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal10_hz34 (by norm_num) (by norm_num)

theorem sGlobal10_hz36 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal10_hz35 sGlobal10_hz27 (by norm_num) (by norm_num)

theorem sGlobal10_hz37 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (s3rpp 12225 46) := by
    convert sGlobal10_hz36 using 1 <;>
      norm_num [s3rpp, mA] <;> ring

theorem sGlobal10_hz38 {c : ℝ} (hc : B (79 / 200) (2 / 5) c) : B (79 / 200) (2 / 5) c := hc

theorem sGlobal10_hz39 : B (629255411448048649 / 1000000000000000000) (629255411481595569 / 1000000000000000000) (kdot ((79 / 200))) := by
    constructor
    · apply bkdot_lower (q := (164638193524543659 / 250000000000000000)) (a := (582364237876490461 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (131710554819634927 / 200000000000000000)) (a := (145591059455948771 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal10_hz40 : B (6241 / 40000) (6241 / 40000) (((79 / 200) : ℝ)^2) := bsq (bpoint ((79 / 200) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal10_hz41 : B (33759 / 40000) (33759 / 40000) ((1 : ℝ) - (((79 / 200) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal10_hz40 (by norm_num) (by norm_num)

theorem sGlobal10_hz42 : B (918681119866953617 / 1000000000000000000) (459340559933476809 / 500000000000000000) (√((1 : ℝ) - (((79 / 200) : ℝ)^2))) := bsqrt sGlobal10_hz41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal10_hz43 : B (228457252112537 / 781250000000000) (146212641352023681 / 500000000000000000) ((√((1 : ℝ) - (((79 / 200) : ℝ)^2))) / Real.pi) := bdiv sGlobal10_hz42 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal10_hz44 : B (15534742970123701 / 62500000000000000) (994223550140921 / 4000000000000000) (((79 / 200) : ℝ) * (kdot ((79 / 200)))) := bmul (bpoint ((79 / 200) : ℝ)) sGlobal10_hz39 (by norm_num) (by norm_num)

theorem sGlobal10_hz45 : B (33811323139126661 / 62500000000000000) (135245292559819403 / 250000000000000000) (((√((1 : ℝ) - (((79 / 200) : ℝ)^2))) / Real.pi) + (((79 / 200) : ℝ) * (kdot ((79 / 200))))) := badd sGlobal10_hz43 sGlobal10_hz44 (by norm_num) (by norm_num)

theorem sGlobal10_hz46 : B (33811323139126661 / 62500000000000000) (135245292559819403 / 250000000000000000) (kappa ((79 / 200))) := by rw [kappa_eq]; exact sGlobal10_hz45

theorem sGlobal10_hz47 : B (315494940215399341 / 500000000000000000) (630989880455876101 / 1000000000000000000) (kdot ((2 / 5))) := by
    constructor
    · apply bkdot_lower (q := (81831708838497143 / 125000000000000000)) (a := (579639740369447029 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (654653670707977143 / 1000000000000000000)) (a := (579639740330055513 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal10_hz48 : B (4 / 25) (4 / 25) (((2 / 5) : ℝ)^2) := bsq (bpoint ((2 / 5) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal10_hz49 : B (21 / 25) (21 / 25) ((1 : ℝ) - (((2 / 5) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal10_hz48 (by norm_num) (by norm_num)

theorem sGlobal10_hz50 : B (916515138991168001 / 1000000000000000000) (458257569495584001 / 500000000000000000) (√((1 : ℝ) - (((2 / 5) : ℝ)^2))) := bsqrt sGlobal10_hz49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal10_hz51 : B (145867914788999887 / 500000000000000000) (11669433183119991 / 40000000000000000) ((√((1 : ℝ) - (((2 / 5) : ℝ)^2))) / Real.pi) := bdiv sGlobal10_hz50 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal10_hz52 : B (15774747010769967 / 62500000000000000) (252395952182350441 / 1000000000000000000) (((2 / 5) : ℝ) * (kdot ((2 / 5)))) := bmul (bpoint ((2 / 5) : ℝ)) sGlobal10_hz47 (by norm_num) (by norm_num)

theorem sGlobal10_hz53 : B (272065890875159623 / 500000000000000000) (68016472720043777 / 125000000000000000) (((√((1 : ℝ) - (((2 / 5) : ℝ)^2))) / Real.pi) + (((2 / 5) : ℝ) * (kdot ((2 / 5))))) := badd sGlobal10_hz51 sGlobal10_hz52 (by norm_num) (by norm_num)

theorem sGlobal10_hz54 : B (272065890875159623 / 500000000000000000) (68016472720043777 / 125000000000000000) (kappa ((2 / 5))) := by rw [kappa_eq]; exact sGlobal10_hz53

theorem sGlobal10_hz55 {c : ℝ} (hc : B (79 / 200) (2 / 5) c) : B (33811323139126661 / 62500000000000000) (68016472720043777 / 125000000000000000) (kappa c) := bkappa (sGlobal10_hz38 hc) (by norm_num) (by norm_num) sGlobal10_hz46.1 sGlobal10_hz54.2

theorem sGlobal10_hz56 : B 24450 24450 ((2 : ℝ) * (12225 : ℝ)) := bmul (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal10_hz57 {c : ℝ} (hc : B (79 / 200) (2 / 5) c) : B (56983527279956223 / 125000000000000000) (28688676860873339 / 62500000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (sGlobal10_hz55 hc) (by norm_num) (by norm_num)

theorem sGlobal10_hz58 {c : ℝ} (hc : B (79 / 200) (2 / 5) c) : B (27864944839898593047 / 2500000000000000) (14028762984967062771 / 1250000000000000) (((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) := bmul sGlobal10_hz56 (sGlobal10_hz57 hc) (by norm_num) (by norm_num)

theorem sGlobal10_hz59 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (4 : ℝ)) sGlobal10_hz10 (by norm_num) (by norm_num)

theorem sGlobal10_hz60 {c : ℝ} (hc : B (79 / 200) (2 / 5) c) : B (278649432039067730061 / 25000000000000000) (2805752433394230550111 / 250000000000000000) ((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bsub (sGlobal10_hz58 hc) sGlobal10_hz59 (by norm_num) (by norm_num)

theorem sGlobal10_hz61 {c : ℝ} (hc : B (79 / 200) (2 / 5) c) : B (105574510567478877621 / 1000000000000000000) (5296935371886493529 / 50000000000000000) (√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) := bsqrt (sGlobal10_hz60 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal10_hz62 : B (30670756373515103 / 125000000000000000) (122683025494060423 / 500000000000000000) ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal10_hz7 (by norm_num) (by norm_num)

theorem sGlobal10_hz63 {c : ℝ} (hc : B (79 / 200) (2 / 5) c) : B (4213165780659630271 / 40000000000000000) (26423335346685437439 / 250000000000000000) ((√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) - ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))))) := bsub (sGlobal10_hz61 hc) sGlobal10_hz62 (by norm_num) (by norm_num)

theorem sGlobal10_hz64 {c : ℝ} (hc : B (79 / 200) (2 / 5) c) : B (4213165780659630271 / 40000000000000000) (26423335346685437439 / 250000000000000000) (s3dm 12225 46 c) := by
    convert (sGlobal10_hz63 hc) using 1 <;>
      norm_num [s3dm, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal10_hz65 : B (6126072185528622723889 / 500000000000000000) (2450428874211449090087 / 200000000000000000) ((s3ap 12225 46)^2) := bsq sGlobal10_hz9 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal10_hz66 : B (6126072185528622723889 / 250000000000000000) (2450428874211449090087 / 100000000000000000) ((2 : ℝ) * ((s3ap 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal10_hz65 (by norm_num) (by norm_num)

theorem sGlobal10_hz67 {c : ℝ} (hc : B (79 / 200) (2 / 5) c) : B (1386778585571974357101 / 125000000000000000) (2234216482698867284273 / 200000000000000000) ((s3dm 12225 46 c)^2) := bsq (sGlobal10_hz64 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal10_hz68 {c : ℝ} (hc : B (79 / 200) (2 / 5) c) : B (13333206328620154474191 / 1000000000000000000) (6705030028769348022031 / 500000000000000000) (((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) := bsub sGlobal10_hz66 (sGlobal10_hz67 hc) (by norm_num) (by norm_num)

theorem sGlobal10_hz69 : B (1524735695971823534271 / 125000000000000000) (609894278388729413841 / 50000000000000000) ((s3am 12225 46)^2) := bsq sGlobal10_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal10_hz70 : B (1524735695971823534271 / 62500000000000000) (609894278388729413841 / 25000000000000000) ((2 : ℝ) * ((s3am 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal10_hz69 (by norm_num) (by norm_num)

theorem sGlobal10_hz71 {c : ℝ} (hc : B (79 / 200) (2 / 5) c) : B (273268802501413711 / 500000000000000000) (68710986747605531 / 125000000000000000) ((((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) / ((2 : ℝ) * ((s3am 12225 46)^2))) := bdiv (sGlobal10_hz68 hc) sGlobal10_hz70 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal10_hz72 {c : ℝ} (hc : B (79 / 200) (2 / 5) c) : B (273268802501413711 / 500000000000000000) (68710986747605531 / 125000000000000000) (s3c1 12225 46 c) := by
    convert (sGlobal10_hz71 hc) using 1 <;>
      norm_num [s3c1] <;> ring

theorem sGlobal10_hz73 {c : ℝ} (hc : B (79 / 200) (2 / 5) c) : B (629255411448048649 / 1000000000000000000) (630989880455876101 / 1000000000000000000) (kdot c) := bkdot (sGlobal10_hz38 hc) sGlobal10_hz39.1 sGlobal10_hz47.2

theorem sGlobal10_hz74 : B (684054449601419809 / 1000000000000000000) (342027224800711053 / 500000000000000000) (kdot ((273268802501413711 / 500000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (108297988965853721 / 200000000000000000)) (a := (31017881877080103 / 62500000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (135372486207317151 / 250000000000000000)) (a := (248143055016639021 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal10_hz75 : B (685253354599284423 / 1000000000000000000) (137050670919857253 / 200000000000000000) (kdot ((68710986747605531 / 125000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (21562280053022663 / 40000000000000000)) (a := (49440287446645987 / 100000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (269528500662783287 / 500000000000000000)) (a := (247201437233228489 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal10_hz76 {c : ℝ} (hc : B (79 / 200) (2 / 5) c) : B (684054449601419809 / 1000000000000000000) (137050670919857253 / 200000000000000000) (kdot (s3c1 12225 46 c)) := bkdot (sGlobal10_hz72 hc) sGlobal10_hz74.1 sGlobal10_hz75.2

theorem sGlobal10_hz77 {c : ℝ} (hc : B (79 / 200) (2 / 5) c) : B (6241 / 40000) (4 / 25) (c^2) := bsq (sGlobal10_hz38 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal10_hz78 {c : ℝ} (hc : B (79 / 200) (2 / 5) c) : B (21 / 25) (33759 / 40000) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (sGlobal10_hz77 hc) (by norm_num) (by norm_num)

theorem sGlobal10_hz79 {c : ℝ} (hc : B (79 / 200) (2 / 5) c) : B (916515138991168001 / 1000000000000000000) (459340559933476809 / 500000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (sGlobal10_hz78 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal10_hz80 : B (39119999999999765769 / 1600000000000000) (3912000000000000489 / 160000000000000) ((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (149450625 : ℝ)) sGlobal10_hz10 (by norm_num) (by norm_num)

theorem sGlobal10_hz81 {c : ℝ} (hc : B (79 / 200) (2 / 5) c) : B (115344422176850583 / 200000000000000000) (579678490001919447 / 1000000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (sGlobal10_hz79 hc) (sGlobal10_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal10_hz82 {c : ℝ} (hc : B (79 / 200) (2 / 5) c) : B (14100855611119899342877 / 1000000000000000000) (14173139080546932250793 / 1000000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) := bmul sGlobal10_hz80 (sGlobal10_hz81 hc) (by norm_num) (by norm_num)

theorem sGlobal10_hz83 {c : ℝ} (hc : B (79 / 200) (2 / 5) c) : B (3525213902779974835719 / 500000000000000000) (7086569540273466125397 / 1000000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) / (2 : ℝ)) := bdiv (sGlobal10_hz82 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal10_hz84 {c : ℝ} (hc : B (79 / 200) (2 / 5) c) : B (3525213902779974835719 / 500000000000000000) (7086569540273466125397 / 1000000000000000000) (s3Cpa 12225 c) := by
    convert (sGlobal10_hz83 hc) using 1 <;>
      norm_num [s3Cpa, mA] <;> ring

theorem sGlobal10_hz85 {c : ℝ} (hc : B (79 / 200) (2 / 5) c) : B (145867914788999887 / 500000000000000000) (146212641352023681 / 500000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (sGlobal10_hz79 hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal10_hz86 {c : ℝ} (hc : B (79 / 200) (2 / 5) c) : B (15534742970123701 / 62500000000000000) (252395952182350441 / 1000000000000000000) (c * (kdot c)) := bmul (sGlobal10_hz38 hc) (sGlobal10_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal10_hz87 {c : ℝ} (hc : B (79 / 200) (2 / 5) c) : B (39339877395649333 / 1000000000000000000) (21934697591034073 / 500000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (sGlobal10_hz85 hc) (sGlobal10_hz86 hc) (by norm_num) (by norm_num)

theorem sGlobal10_hz88 {c : ℝ} (hc : B (79 / 200) (2 / 5) c) : B (961860002323620432713 / 1000000000000000000) (33518959756298946993 / 31250000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) := bmul sGlobal10_hz80 (sGlobal10_hz87 hc) (by norm_num) (by norm_num)

theorem sGlobal10_hz89 {c : ℝ} (hc : B (79 / 200) (2 / 5) c) : B (120232500290452554089 / 250000000000000000) (33518959756298946993 / 62500000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) / (2 : ℝ)) := bdiv (sGlobal10_hz88 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal10_hz90 {c : ℝ} (hc : B (79 / 200) (2 / 5) c) : B (120232500290452554089 / 250000000000000000) (33518959756298946993 / 62500000000000000) (s3Cpp 12225 c) := by
    convert (sGlobal10_hz89 hc) using 1 <;>
      norm_num [s3Cpp, mA] <;> ring

theorem sGlobal10_hz91 {c : ℝ} (hc : B (79 / 200) (2 / 5) c) : B (7165572915493687379839 / 1000000000000000000) (7201714650207204537623 / 1000000000000000000) ((s3Cpa 12225 c) + (s3r1 12225 46)) := badd (sGlobal10_hz84 hc) sGlobal10_hz33 (by norm_num) (by norm_num)

theorem sGlobal10_hz92 {c : ℝ} (hc : B (79 / 200) (2 / 5) c) : B (64879671497738011183 / 1000000000000000000) (16301727937050055473 / 250000000000000000) (((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) := bdiv (sGlobal10_hz91 hc) sGlobal10_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal10_hz93 {c : ℝ} (hc : B (79 / 200) (2 / 5) c) : B (13000470904646414319 / 200000000000000000) (13065918954738856463 / 200000000000000000) ((((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) + (s3e0 12225 46)) := badd (sGlobal10_hz92 hc) sGlobal10_hz16 (by norm_num) (by norm_num)

theorem sGlobal10_hz94 {c : ℝ} (hc : B (79 / 200) (2 / 5) c) : B (13000470904646414319 / 200000000000000000) (13065918954738856463 / 200000000000000000) (s3Lam 12225 46 c) := by
    convert (sGlobal10_hz93 hc) using 1 <;>
      norm_num [s3Lam] <;> ring

theorem sGlobal10_hz95 {c : ℝ} (hc : B (79 / 200) (2 / 5) c) : B (139423351946075505489 / 250000000000000000) (306533381361637713353 / 500000000000000000) ((s3Cpp 12225 c) + (s3rpp 12225 46)) := badd (sGlobal10_hz90 hc) sGlobal10_hz37 (by norm_num) (by norm_num)

theorem sGlobal10_hz96 {c : ℝ} (hc : B (79 / 200) (2 / 5) c) : B (139423351946075505489 / 500000000000000000) (84021211149889830089 / 200000000000000000) (if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) := bweaken (bfirst (sGlobal10_hz95 hc) (sGlobal10_hz76 hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem sGlobal10_hz97 {c : ℝ} (hc : B (79 / 200) (2 / 5) c) : B (2112653046781974478857 / 500000000000000000) (1066988988323775821531 / 250000000000000000) ((s3Lam 12225 46 c)^2) := bsq (sGlobal10_hz94 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal10_hz98 {c : ℝ} (hc : B (79 / 200) (2 / 5) c) : B (298703353682226609 / 1000000000000000000) (302156780789095867 / 1000000000000000000) ((s3c1 12225 46 c)^2) := bsq (sGlobal10_hz72 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal10_hz99 {c : ℝ} (hc : B (79 / 200) (2 / 5) c) : B (697843219210904133 / 1000000000000000000) (701296646317773391 / 1000000000000000000) ((1 : ℝ) - ((s3c1 12225 46 c)^2)) := bsub (bpoint (1 : ℝ)) (sGlobal10_hz98 hc) (by norm_num) (by norm_num)

theorem sGlobal10_hz100 {c : ℝ} (hc : B (79 / 200) (2 / 5) c) : B (83537010911984643 / 100000000000000000) (52339660150585639 / 62500000000000000) (√((1 : ℝ) - ((s3c1 12225 46 c)^2))) := bsqrt (sGlobal10_hz99 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal10_hz101 {c : ℝ} (hc : B (79 / 200) (2 / 5) c) : B (1312196298919706741 / 500000000000000000) (2630878269127460717 / 1000000000000000000) (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))) := bmul pi_mem (sGlobal10_hz100 hc) (by norm_num) (by norm_num)

theorem sGlobal10_hz102 {c : ℝ} (hc : B (79 / 200) (2 / 5) c) : B (1606043937169805041233 / 1000000000000000000) (325252857122732930761 / 200000000000000000) (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2))))) := bdiv (sGlobal10_hz97 hc) (sGlobal10_hz101 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal10_hz103 {c : ℝ} (hc : B (79 / 200) (2 / 5) c) : B (1884890641061956052211 / 1000000000000000000) (8185481365452455217 / 4000000000000000) ((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) := badd (sGlobal10_hz96 hc) (sGlobal10_hz102 hc) (by norm_num) (by norm_num)

theorem sGlobal10_hz104 : B (3762781186094069 / 250000000000000000) (376278118609407 / 25000000000000000) ((s3e0 12225 46)^2) := bsq sGlobal10_hz16 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal10_hz105 {c : ℝ} (hc : B (79 / 200) (2 / 5) c) : B (1884905692186700428487 / 1000000000000000000) (204638539248785818053 / 100000000000000000) (((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) := badd (sGlobal10_hz103 hc) sGlobal10_hz104 (by norm_num) (by norm_num)

theorem sGlobal10_hz106 {c : ℝ} (hc : B (79 / 200) (2 / 5) c) : B (961701382818973849309 / 500000000000000000) (1042441232970991225273 / 500000000000000000) ((((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) + (s3rs 12225 46 maskSlack)) := badd (sGlobal10_hz105 hc) sGlobal10_hz29 (by norm_num) (by norm_num)

theorem sGlobal10_hz107 {c : ℝ} (hc : B (79 / 200) (2 / 5) c) : B (961701382818973849309 / 500000000000000000) (1042441232970991225273 / 500000000000000000) (s3U 12225 46 maskSlack c) := by
    convert (sGlobal10_hz106 hc) using 1 <;>
      norm_num [s3U] <;> ring

theorem sGlobal10_hz108 {c : ℝ} (hc : B (79 / 200) (2 / 5) c) : B (202083297269658970769 / 500000000000000000) (28721246842393209143 / 62500000000000000) ((s3Cpp 12225 c) - (s3rpp 12225 46)) := bsub (sGlobal10_hz90 hc) sGlobal10_hz37 (by norm_num) (by norm_num)

theorem sGlobal10_hz109 {c : ℝ} (hc : B (79 / 200) (2 / 5) c) : B 0 0 (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ)) := bweaken (bmin (sGlobal10_hz108 hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem sGlobal10_hz110 {c : ℝ} (hc : B (79 / 200) (2 / 5) c) : B 0 0 ((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) := bmul (sGlobal10_hz76 hc) (sGlobal10_hz109 hc) (by norm_num) (by norm_num)

theorem sGlobal10_hz111 {c : ℝ} (hc : B (79 / 200) (2 / 5) c) : B (-376278118609407 / 25000000000000000) (-3762781186094069 / 250000000000000000) (((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) := bsub (sGlobal10_hz110 hc) sGlobal10_hz104 (by norm_num) (by norm_num)

theorem sGlobal10_hz112 {c : ℝ} (hc : B (79 / 200) (2 / 5) c) : B (-4814015572358580787 / 125000000000000000) (-38512124575991646407 / 1000000000000000000) ((((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) - (s3rs 12225 46 maskSlack)) := bsub (sGlobal10_hz111 hc) sGlobal10_hz29 (by norm_num) (by norm_num)

theorem sGlobal10_hz113 {c : ℝ} (hc : B (79 / 200) (2 / 5) c) : B (-4814015572358580787 / 125000000000000000) (-38512124575991646407 / 1000000000000000000) (s3L 12225 46 maskSlack c) := by
    convert (sGlobal10_hz112 hc) using 1 <;>
      norm_num [s3L] <;> ring

theorem sGlobal10_hz114 {c : ℝ} (hc : B (79 / 200) (2 / 5) c) : B 0 (1042441232970991225273 / 500000000000000000) |(s3U 12225 46 maskSlack c)| := bweaken (babs (sGlobal10_hz107 hc)) (by norm_num) (by norm_num)

theorem sGlobal10_hz115 {c : ℝ} (hc : B (79 / 200) (2 / 5) c) : B 0 (4814015572358580787 / 125000000000000000) |(s3L 12225 46 maskSlack c)| := bweaken (babs (sGlobal10_hz113 hc)) (by norm_num) (by norm_num)

theorem sGlobal10_hz116 {c : ℝ} (hc : B (79 / 200) (2 / 5) c) : B 0 (1042441232970991225273 / 500000000000000000) (max |(s3U 12225 46 maskSlack c)| |(s3L 12225 46 maskSlack c)|) := bweaken (bmax (sGlobal10_hz114 hc) (sGlobal10_hz115 hc)) (by norm_num) (by norm_num)

theorem sGlobal10_hz117 {c : ℝ} (hc : B (79 / 200) (2 / 5) c) : B 0 (1042441232970991225273 / 500000000000000000) (s3nks 12225 46 maskSlack c) := by
    convert (sGlobal10_hz116 hc) using 1 <;>
      norm_num [s3nks] <;> ring

theorem sGlobal10 {c : ℝ} (hc : B (79 / 200) (2 / 5) c) :
    0 < s3am 12225 46 ∧ 0 ≤ s3dm 12225 46 c ∧
    s3dm 12225 46 c ^ 2 ≤ 2 * s3ap 12225 46 ^ 2 ∧ s3c1 12225 46 c < 1 ∧
    0 ≤ s3Cpa 12225 c - s3r1 12225 46 ∧
    s3e0 12225 46 ≤ (s3Cpa 12225 c - s3r1 12225 46) / s3ap 12225 46 ∧
    s3nks 12225 46 maskSlack c ≤ 12225 * (170543 / 1000000) := by

  refine ⟨lt_of_lt_of_le (by norm_num) sGlobal10_hz14.1,
    le_trans (by norm_num) (sGlobal10_hz64 hc).1, ?_,
    lt_of_le_of_lt (sGlobal10_hz72 hc).2 (by norm_num), ?_, ?_,
    le_trans (sGlobal10_hz117 hc).2 (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (sGlobal10_hz64 hc).1) (sGlobal10_hz64 hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) sGlobal10_hz9.1 2
    nlinarith only [h1, h2]
  · linarith only [(sGlobal10_hz84 hc).1, sGlobal10_hz33.2]
  · have hap : 0 < s3ap 12225 46 := lt_of_lt_of_le (by norm_num) sGlobal10_hz9.1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul sGlobal10_hz16.2 sGlobal10_hz9.2 (le_trans (by norm_num) sGlobal10_hz9.1) (by norm_num)
    linarith only [h, (sGlobal10_hz84 hc).1, sGlobal10_hz33.2]

end BstLean.Part255
