import BstLean.Part255SGlobal19
import BstLean.Part255Numeric10
namespace BstLean.Part255
open Real BstLean.Part130 BstLean.Part182 BstLean.Part197 BstLean.Part246
theorem sGlobal23_hz0 : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal23_hz1 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) ((√(23 : ℝ)) / (12225 : ℝ)) := bdiv sGlobal23_hz0 (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal23_hz2 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) maskSlack := by
    convert sGlobal23_hz1 using 1 <;>
      norm_num [maskSlack] <;> ring

theorem sGlobal23_hz3 : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal23_hz4 : B (6395294793910793 / 500000000000000000) (12790589587821587 / 1000000000000000000) (√((2 / 12225) : ℝ)) := bsqrt (bpoint ((2 / 12225) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal23_hz5 : B (7230130686979 / 62500000000000000) (23136418198333 / 200000000000000000) (√((2 / 149450625) : ℝ)) := bsqrt (bpoint ((2 / 149450625) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal23_hz6 : B (2211334438749598093 / 20000000000000000) (110566721937479904651 / 1000000000000000000) (√(12225 : ℝ)) := bsqrt (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal23_hz7 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))) := bmul sGlobal23_hz3 sGlobal23_hz4 (by norm_num) (by norm_num)

theorem sGlobal23_hz8 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) ((√(12225 : ℝ)) + ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := badd sGlobal23_hz6 sGlobal23_hz7 (by norm_num) (by norm_num)

theorem sGlobal23_hz9 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) (s3ap 12225 46) := by
    convert sGlobal23_hz8 using 1 <;>
      norm_num [s3ap, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal23_hz10 : B (163599182004089 / 1000000000000000000) (16359918200409 / 100000000000000000) ((2 : ℝ) / (12225 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal23_hz11 : B (1222499983640081799591 / 100000000000000000) (12224999836400817995911 / 1000000000000000000) ((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ))) := bsub (bpoint (12225 : ℝ)) sGlobal23_hz10 (by norm_num) (by norm_num)

theorem sGlobal23_hz12 : B (110566721197658827907 / 1000000000000000000) (27641680299414706977 / 250000000000000000) (√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) := bsqrt sGlobal23_hz11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal23_hz13 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) ((√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) - ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bsub sGlobal23_hz12 sGlobal23_hz7 (by norm_num) (by norm_num)

theorem sGlobal23_hz14 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) (s3am 12225 46) := by
    convert sGlobal23_hz13 using 1 <;>
      norm_num [s3am, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal23_hz15 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√((2 / 12225) : ℝ)) * (√(92 : ℝ))) := bmul sGlobal23_hz4 sGlobal23_hz3 (by norm_num) (by norm_num)

theorem sGlobal23_hz16 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) (s3e0 12225 46) := by
    convert sGlobal23_hz15 using 1 <;>
      norm_num [s3e0, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal23_hz17 : B (250196148528560847 / 500000000000000000) (100078459411424339 / 200000000000000000) (((1 / 2) : ℝ) + maskSlack) := badd (bpoint ((1 / 2) : ℝ)) sGlobal23_hz2 (by norm_num) (by norm_num)

theorem sGlobal23_hz18 : B (59827153232297998295487 / 800000000000000) (23930861292919199366019 / 320000000000000) ((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack)) := bmul (bpoint (149450625 : ℝ)) sGlobal23_hz17 (by norm_num) (by norm_num)

theorem sGlobal23_hz19 : B (1729554180017180009583 / 200000000000000000) (8647770900085900056557 / 1000000000000000000) (√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) := bsqrt sGlobal23_hz18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal23_hz20 : B (4328681281566262743499 / 500000000000000000) (8657362563132525495641 / 1000000000000000000) ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))) := badd sGlobal23_hz19 sGlobal23_hz3 (by norm_num) (by norm_num)

theorem sGlobal23_hz21 : B (110732771457999278473 / 1000000000000000000) (55366385728999643621 / 500000000000000000) ((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ)))) := bmul sGlobal23_hz4 sGlobal23_hz20 (by norm_num) (by norm_num)

theorem sGlobal23_hz22 : B (209099159 / 15625000000000000) (13382346177 / 1000000000000000000) ((2 : ℝ) / (149450625 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (149450625 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal23_hz23 : B (2452349334953899930479 / 200000000000000000) (12261746674769501594427 / 1000000000000000000) (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2) := bsq sGlobal23_hz21 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal23_hz24 : B (82045469362091 / 500000000000000000) (32818187747289 / 200000000000000000) (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2)) := bmul sGlobal23_hz22 sGlobal23_hz23 (by norm_num) (by norm_num)

theorem sGlobal23_hz25 : B (82045469362091 / 250000000000000000) (32818187747289 / 100000000000000000) ((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) := bmul (bpoint (2 : ℝ)) sGlobal23_hz24 (by norm_num) (by norm_num)

theorem sGlobal23_hz26 : B (117258080744995992792057 / 1000000000000000000) (58629040372497996396029 / 500000000000000000) (√(13749457500 : ℝ)) := bsqrt (bpoint (13749457500 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal23_hz27 : B (117304080744995992792057 / 1000000000000000000) (58652040372497996396029 / 500000000000000000) ((√(13749457500 : ℝ)) + (46 : ℝ)) := badd sGlobal23_hz26 (bpoint (46 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal23_hz28 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal23_hz25 sGlobal23_hz27 (by norm_num) (by norm_num)

theorem sGlobal23_hz29 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (s3rs 12225 46 maskSlack) := by
    convert sGlobal23_hz28 using 1 <;>
      norm_num [s3rs, s3pp, s3K, mA, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal23_hz30 : B (490797546012267 / 1000000000000000000) (49079754601227 / 100000000000000000) ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (3 : ℝ)) sGlobal23_hz10 (by norm_num) (by norm_num)

theorem sGlobal23_hz31 : B (490797546012267 / 500000000000000000) (49079754601227 / 50000000000000000) ((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal23_hz30 (by norm_num) (by norm_num)

theorem sGlobal23_hz32 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal23_hz31 sGlobal23_hz27 (by norm_num) (by norm_num)

theorem sGlobal23_hz33 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (s3r1 12225 46) := by
    convert sGlobal23_hz32 using 1 <;>
      norm_num [s3r1, mA] <;> ring

theorem sGlobal23_hz34 : B (163599182004089 / 500000000000000000) (16359918200409 / 50000000000000000) ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (2 : ℝ)) sGlobal23_hz10 (by norm_num) (by norm_num)

theorem sGlobal23_hz35 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal23_hz34 (by norm_num) (by norm_num)

theorem sGlobal23_hz36 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal23_hz35 sGlobal23_hz27 (by norm_num) (by norm_num)

theorem sGlobal23_hz37 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (s3rpp 12225 46) := by
    convert sGlobal23_hz36 using 1 <;>
      norm_num [s3rpp, mA] <;> ring

theorem sGlobal23_hz38 {c : ℝ} (hc : B (23 / 50) (93 / 200) c) : B (23 / 50) (93 / 200) c := hc

theorem sGlobal23_hz39 : B (163037649309219301 / 250000000000000000) (326075298618777983 / 500000000000000000) (kdot ((23 / 50))) := by
    constructor
    · apply bkdot_lower (q := (121632728111907469 / 200000000000000000)) (a := (10928011282762237 / 20000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (9502556883742771 / 15625000000000000)) (a := (273200282068522827 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal23_hz40 : B (529 / 2500) (529 / 2500) (((23 / 50) : ℝ)^2) := bsq (bpoint ((23 / 50) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal23_hz41 : B (1971 / 2500) (1971 / 2500) ((1 : ℝ) - (((23 / 50) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal23_hz40 (by norm_num) (by norm_num)

theorem sGlobal23_hz42 : B (887918915216924523 / 1000000000000000000) (221979728804231131 / 250000000000000000) (√((1 : ℝ) - (((23 / 50) : ℝ)^2))) := bsqrt sGlobal23_hz41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal23_hz43 : B (282633368843134123 / 1000000000000000000) (2261066950745073 / 8000000000000000) ((√((1 : ℝ) - (((23 / 50) : ℝ)^2))) / Real.pi) := bdiv sGlobal23_hz42 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal23_hz44 : B (299989274728963513 / 1000000000000000000) (59997854945855149 / 200000000000000000) (((23 / 50) : ℝ) * (kdot ((23 / 50)))) := bmul (bpoint ((23 / 50) : ℝ)) sGlobal23_hz39 (by norm_num) (by norm_num)

theorem sGlobal23_hz45 : B (145655660893024409 / 250000000000000000) (58262264357240987 / 100000000000000000) (((√((1 : ℝ) - (((23 / 50) : ℝ)^2))) / Real.pi) + (((23 / 50) : ℝ) * (kdot ((23 / 50))))) := badd sGlobal23_hz43 sGlobal23_hz44 (by norm_num) (by norm_num)

theorem sGlobal23_hz46 : B (145655660893024409 / 250000000000000000) (58262264357240987 / 100000000000000000) (kappa ((23 / 50))) := by rw [kappa_eq]; exact sGlobal23_hz45

theorem sGlobal23_hz47 : B (653945678051333057 / 1000000000000000000) (326972839025915031 / 500000000000000000) (kdot ((93 / 200))) := by
    constructor
    · apply bkdot_lower (q := (604307631352261019 / 1000000000000000000)) (a := (108716171557692921 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (302153815676130509 / 500000000000000000)) (a := (67947607223460489 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal23_hz48 : B (8649 / 40000) (8649 / 40000) (((93 / 200) : ℝ)^2) := bsq (bpoint ((93 / 200) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal23_hz49 : B (31351 / 40000) (31351 / 40000) ((1 : ℝ) - (((93 / 200) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal23_hz48 (by norm_num) (by norm_num)

theorem sGlobal23_hz50 : B (110663834991382799 / 125000000000000000) (885310679931062393 / 1000000000000000000) (√((1 : ℝ) - (((93 / 200) : ℝ)^2))) := bsqrt sGlobal23_hz49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal23_hz51 : B (140901570883075401 / 500000000000000000) (281803141766150803 / 1000000000000000000) ((√((1 : ℝ) - (((93 / 200) : ℝ)^2))) / Real.pi) := bdiv sGlobal23_hz50 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal23_hz52 : B (304084740293869871 / 1000000000000000000) (304084740294100979 / 1000000000000000000) (((93 / 200) : ℝ) * (kdot ((93 / 200)))) := bmul (bpoint ((93 / 200) : ℝ)) sGlobal23_hz47 (by norm_num) (by norm_num)

theorem sGlobal23_hz53 : B (585887882060020673 / 1000000000000000000) (292943941030125891 / 500000000000000000) (((√((1 : ℝ) - (((93 / 200) : ℝ)^2))) / Real.pi) + (((93 / 200) : ℝ) * (kdot ((93 / 200))))) := badd sGlobal23_hz51 sGlobal23_hz52 (by norm_num) (by norm_num)

theorem sGlobal23_hz54 : B (585887882060020673 / 1000000000000000000) (292943941030125891 / 500000000000000000) (kappa ((93 / 200))) := by rw [kappa_eq]; exact sGlobal23_hz53

theorem sGlobal23_hz55 {c : ℝ} (hc : B (23 / 50) (93 / 200) c) : B (145655660893024409 / 250000000000000000) (292943941030125891 / 500000000000000000) (kappa c) := bkappa (sGlobal23_hz38 hc) (by norm_num) (by norm_num) sGlobal23_hz46.1 sGlobal23_hz54.2

theorem sGlobal23_hz56 : B 24450 24450 ((2 : ℝ) * (12225 : ℝ)) := bmul (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal23_hz57 {c : ℝ} (hc : B (23 / 50) (93 / 200) c) : B (207056058969874109 / 500000000000000000) (104344339106975591 / 250000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (sGlobal23_hz55 hc) (by norm_num) (by norm_num)

theorem sGlobal23_hz58 {c : ℝ} (hc : B (23 / 50) (93 / 200) c) : B (101250412836268439301 / 10000000000000000) (51024381823311063999 / 5000000000000000) (((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) := bmul sGlobal23_hz56 (sGlobal23_hz57 hc) (by norm_num) (by norm_num)

theorem sGlobal23_hz59 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (4 : ℝ)) sGlobal23_hz10 (by norm_num) (by norm_num)

theorem sGlobal23_hz60 {c : ℝ} (hc : B (23 / 50) (93 / 200) c) : B (506252031461505795687 / 50000000000000000) (2551218927566371195861 / 250000000000000000) ((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bsub (sGlobal23_hz58 hc) sGlobal23_hz59 (by norm_num) (by norm_num)

theorem sGlobal23_hz61 {c : ℝ} (hc : B (23 / 50) (93 / 200) c) : B (50311630437777793989 / 500000000000000000) (20203836972481721927 / 200000000000000000) (√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) := bsqrt (sGlobal23_hz60 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal23_hz62 : B (30670756373515103 / 125000000000000000) (122683025494060423 / 500000000000000000) ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal23_hz7 (by norm_num) (by norm_num)

theorem sGlobal23_hz63 {c : ℝ} (hc : B (23 / 50) (93 / 200) c) : B (25094473706141866783 / 250000000000000000) (100773818811420488811 / 1000000000000000000) ((√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) - ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))))) := bsub (sGlobal23_hz61 hc) sGlobal23_hz62 (by norm_num) (by norm_num)

theorem sGlobal23_hz64 {c : ℝ} (hc : B (23 / 50) (93 / 200) c) : B (25094473706141866783 / 250000000000000000) (100773818811420488811 / 1000000000000000000) (s3dm 12225 46 c) := by
    convert (sGlobal23_hz63 hc) using 1 <;>
      norm_num [s3dm, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal23_hz65 : B (6126072185528622723889 / 500000000000000000) (2450428874211449090087 / 200000000000000000) ((s3ap 12225 46)^2) := bsq sGlobal23_hz9 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal23_hz66 : B (6126072185528622723889 / 250000000000000000) (2450428874211449090087 / 100000000000000000) ((2 : ℝ) * ((s3ap 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal23_hz65 (by norm_num) (by norm_num)

theorem sGlobal23_hz67 {c : ℝ} (hc : B (23 / 50) (93 / 200) c) : B (251893044235298207579 / 25000000000000000) (406214502313480239209 / 40000000000000000) ((s3dm 12225 46 c)^2) := bsq (sGlobal23_hz64 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal23_hz68 {c : ℝ} (hc : B (23 / 50) (93 / 200) c) : B (14348926184277484915331 / 1000000000000000000) (1442856697270256259771 / 100000000000000000) (((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) := bsub sGlobal23_hz66 (sGlobal23_hz67 hc) (by norm_num) (by norm_num)

theorem sGlobal23_hz69 : B (1524735695971823534271 / 125000000000000000) (609894278388729413841 / 50000000000000000) ((s3am 12225 46)^2) := bsq sGlobal23_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal23_hz70 : B (1524735695971823534271 / 62500000000000000) (609894278388729413841 / 25000000000000000) ((2 : ℝ) * ((s3am 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal23_hz69 (by norm_num) (by norm_num)

theorem sGlobal23_hz71 {c : ℝ} (hc : B (23 / 50) (93 / 200) c) : B (588172683886529429 / 1000000000000000000) (591437216414834151 / 1000000000000000000) ((((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) / ((2 : ℝ) * ((s3am 12225 46)^2))) := bdiv (sGlobal23_hz68 hc) sGlobal23_hz70 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal23_hz72 {c : ℝ} (hc : B (23 / 50) (93 / 200) c) : B (588172683886529429 / 1000000000000000000) (591437216414834151 / 1000000000000000000) (s3c1 12225 46 c) := by
    convert (sGlobal23_hz71 hc) using 1 <;>
      norm_num [s3c1] <;> ring

theorem sGlobal23_hz73 {c : ℝ} (hc : B (23 / 50) (93 / 200) c) : B (163037649309219301 / 250000000000000000) (326972839025915031 / 500000000000000000) (kdot c) := bkdot (sGlobal23_hz38 hc) sGlobal23_hz39.1 sGlobal23_hz47.2

theorem sGlobal23_hz74 : B (43759528907760421 / 62500000000000000) (700152462524166851 / 1000000000000000000) (kdot ((588172683886529429 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (254611911935936557 / 500000000000000000)) (a := (235499705232766999 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (509223823871873113 / 1000000000000000000)) (a := (470999410465533819 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal23_hz75 : B (701439243900241373 / 1000000000000000000) (87679905487530183 / 125000000000000000) (kdot ((591437216414834151 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (126670258127253161 / 250000000000000000)) (a := (3751825112052863 / 8000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (506681032509012643 / 1000000000000000000)) (a := (93795627801321547 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal23_hz76 {c : ℝ} (hc : B (23 / 50) (93 / 200) c) : B (43759528907760421 / 62500000000000000) (87679905487530183 / 125000000000000000) (kdot (s3c1 12225 46 c)) := bkdot (sGlobal23_hz72 hc) sGlobal23_hz74.1 sGlobal23_hz75.2

theorem sGlobal23_hz77 {c : ℝ} (hc : B (23 / 50) (93 / 200) c) : B (529 / 2500) (8649 / 40000) (c^2) := bsq (sGlobal23_hz38 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal23_hz78 {c : ℝ} (hc : B (23 / 50) (93 / 200) c) : B (31351 / 40000) (1971 / 2500) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (sGlobal23_hz77 hc) (by norm_num) (by norm_num)

theorem sGlobal23_hz79 {c : ℝ} (hc : B (23 / 50) (93 / 200) c) : B (110663834991382799 / 125000000000000000) (221979728804231131 / 250000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (sGlobal23_hz78 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal23_hz80 : B (39119999999999765769 / 1600000000000000) (3912000000000000489 / 160000000000000) ((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (149450625 : ℝ)) sGlobal23_hz10 (by norm_num) (by norm_num)

theorem sGlobal23_hz81 {c : ℝ} (hc : B (23 / 50) (93 / 200) c) : B (36084743041076761 / 62500000000000000) (290325368533288559 / 500000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (sGlobal23_hz79 hc) (sGlobal23_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal23_hz82 {c : ℝ} (hc : B (23 / 50) (93 / 200) c) : B (2823270295533828876309 / 200000000000000000) (7098455260638906154857 / 500000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) := bmul sGlobal23_hz80 (sGlobal23_hz81 hc) (by norm_num) (by norm_num)

theorem sGlobal23_hz83 {c : ℝ} (hc : B (23 / 50) (93 / 200) c) : B (1764543934708643047693 / 250000000000000000) (7098455260638906154857 / 1000000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) / (2 : ℝ)) := bdiv (sGlobal23_hz82 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal23_hz84 {c : ℝ} (hc : B (23 / 50) (93 / 200) c) : B (1764543934708643047693 / 250000000000000000) (7098455260638906154857 / 1000000000000000000) (s3Cpa 12225 c) := by
    convert (sGlobal23_hz83 hc) using 1 <;>
      norm_num [s3Cpa, mA] <;> ring

theorem sGlobal23_hz85 {c : ℝ} (hc : B (23 / 50) (93 / 200) c) : B (140901570883075401 / 500000000000000000) (2261066950745073 / 8000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (sGlobal23_hz79 hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal23_hz86 {c : ℝ} (hc : B (23 / 50) (93 / 200) c) : B (299989274728963513 / 1000000000000000000) (304084740294100979 / 1000000000000000000) (c * (kdot c)) := bmul (sGlobal23_hz38 hc) (sGlobal23_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal23_hz87 {c : ℝ} (hc : B (23 / 50) (93 / 200) c) : B (-22281598527950177 / 1000000000000000000) (-4338976471457347 / 250000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (sGlobal23_hz85 hc) (sGlobal23_hz86 hc) (by norm_num) (by norm_num)

theorem sGlobal23_hz88 {c : ℝ} (hc : B (23 / 50) (93 / 200) c) : B (-544785084008381895749 / 1000000000000000000) (-424351898908525995793 / 1000000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) := bmul sGlobal23_hz80 (sGlobal23_hz87 hc) (by norm_num) (by norm_num)

theorem sGlobal23_hz89 {c : ℝ} (hc : B (23 / 50) (93 / 200) c) : B (-2179140336033527583 / 8000000000000000) (-26521993681782874737 / 125000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) / (2 : ℝ)) := bdiv (sGlobal23_hz88 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal23_hz90 {c : ℝ} (hc : B (23 / 50) (93 / 200) c) : B (-2179140336033527583 / 8000000000000000) (-26521993681782874737 / 125000000000000000) (s3Cpp 12225 c) := by
    convert (sGlobal23_hz89 hc) using 1 <;>
      norm_num [s3Cpp, mA] <;> ring

theorem sGlobal23_hz91 {c : ℝ} (hc : B (23 / 50) (93 / 200) c) : B (7173320848768309899173 / 1000000000000000000) (7213600370572644567083 / 1000000000000000000) ((s3Cpa 12225 c) + (s3r1 12225 46)) := badd (sGlobal23_hz84 hc) sGlobal23_hz33 (by norm_num) (by norm_num)

theorem sGlobal23_hz92 {c : ℝ} (hc : B (23 / 50) (93 / 200) c) : B (4059364004321717291 / 62500000000000000) (65314529330481232601 / 1000000000000000000) (((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) := bdiv (sGlobal23_hz91 hc) sGlobal23_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal23_hz93 {c : ℝ} (hc : B (23 / 50) (93 / 200) c) : B (16268126773660384267 / 250000000000000000) (2044912886124227907 / 31250000000000000) ((((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) + (s3e0 12225 46)) := badd (sGlobal23_hz92 hc) sGlobal23_hz16 (by norm_num) (by norm_num)

theorem sGlobal23_hz94 {c : ℝ} (hc : B (23 / 50) (93 / 200) c) : B (16268126773660384267 / 250000000000000000) (2044912886124227907 / 31250000000000000) (s3Lam 12225 46 c) := by
    convert (sGlobal23_hz93 hc) using 1 <;>
      norm_num [s3Lam] <;> ring

theorem sGlobal23_hz95 {c : ℝ} (hc : B (23 / 50) (93 / 200) c) : B (-7825165415267965691 / 40000000000000000) (-67706271415885361539 / 500000000000000000) ((s3Cpp 12225 c) + (s3rpp 12225 46)) := badd (sGlobal23_hz90 hc) sGlobal23_hz37 (by norm_num) (by norm_num)

theorem sGlobal23_hz96 {c : ℝ} (hc : B (23 / 50) (93 / 200) c) : B (-137221952806997021649 / 1000000000000000000) (-67706271415885361539 / 1000000000000000000) (if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) := bweaken (bfirst (sGlobal23_hz95 hc) (sGlobal23_hz76 hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem sGlobal23_hz97 {c : ℝ} (hc : B (23 / 50) (93 / 200) c) : B (4234431179582173175653 / 1000000000000000000) (2141014380460502779733 / 500000000000000000) ((s3Lam 12225 46 c)^2) := bsq (sGlobal23_hz94 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal23_hz98 {c : ℝ} (hc : B (23 / 50) (93 / 200) c) : B (13837884242811331 / 40000000000000000) (349797980960527367 / 1000000000000000000) ((s3c1 12225 46 c)^2) := bsq (sGlobal23_hz72 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal23_hz99 {c : ℝ} (hc : B (23 / 50) (93 / 200) c) : B (650202019039472633 / 1000000000000000000) (26162115757188669 / 40000000000000000) ((1 : ℝ) - ((s3c1 12225 46 c)^2)) := bsub (bpoint (1 : ℝ)) (sGlobal23_hz98 hc) (by norm_num) (by norm_num)

theorem sGlobal23_hz100 {c : ℝ} (hc : B (23 / 50) (93 / 200) c) : B (201587762996584293 / 250000000000000000) (404367683528777039 / 500000000000000000) (√((1 : ℝ) - ((s3c1 12225 46 c)^2))) := bsqrt (sGlobal23_hz99 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal23_hz101 {c : ℝ} (hc : B (23 / 50) (93 / 200) c) : B (1266613270567339157 / 500000000000000000) (2540717087846256771 / 1000000000000000000) (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))) := bmul pi_mem (sGlobal23_hz100 hc) (by norm_num) (by norm_num)

theorem sGlobal23_hz102 {c : ℝ} (hc : B (23 / 50) (93 / 200) c) : B (66665134813127308771 / 40000000000000000) (1690345767103405948989 / 1000000000000000000) (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2))))) := bdiv (sGlobal23_hz97 hc) (sGlobal23_hz101 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal23_hz103 {c : ℝ} (hc : B (23 / 50) (93 / 200) c) : B (764703208760592848813 / 500000000000000000) (32452789913750411749 / 20000000000000000) ((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) := badd (sGlobal23_hz96 hc) (sGlobal23_hz102 hc) (by norm_num) (by norm_num)

theorem sGlobal23_hz104 : B (3762781186094069 / 250000000000000000) (376278118609407 / 25000000000000000) ((s3e0 12225 46)^2) := bsq sGlobal23_hz16 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal23_hz105 {c : ℝ} (hc : B (23 / 50) (93 / 200) c) : B (764710734322965036951 / 500000000000000000) (162265454681226496373 / 100000000000000000) (((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) := badd (sGlobal23_hz103 hc) sGlobal23_hz104 (by norm_num) (by norm_num)

theorem sGlobal23_hz106 {c : ℝ} (hc : B (23 / 50) (93 / 200) c) : B (1567918542097177344033 / 1000000000000000000) (830575810133194616873 / 500000000000000000) ((((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) + (s3rs 12225 46 maskSlack)) := badd (sGlobal23_hz105 hc) sGlobal23_hz29 (by norm_num) (by norm_num)

theorem sGlobal23_hz107 {c : ℝ} (hc : B (23 / 50) (93 / 200) c) : B (1567918542097177344033 / 1000000000000000000) (830575810133194616873 / 500000000000000000) (s3U 12225 46 maskSlack c) := by
    convert (sGlobal23_hz106 hc) using 1 <;>
      norm_num [s3U] <;> ring

theorem sGlobal23_hz108 {c : ℝ} (hc : B (23 / 50) (93 / 200) c) : B (-349155948626683222693 / 1000000000000000000) (-36117419509594350437 / 125000000000000000) ((s3Cpp 12225 c) - (s3rpp 12225 46)) := bsub (sGlobal23_hz90 hc) sGlobal23_hz37 (by norm_num) (by norm_num)

theorem sGlobal23_hz109 {c : ℝ} (hc : B (23 / 50) (93 / 200) c) : B (-349155948626683222693 / 1000000000000000000) (-36117419509594350437 / 125000000000000000) (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ)) := bweaken (bmin (sGlobal23_hz108 hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem sGlobal23_hz110 {c : ℝ} (hc : B (23 / 50) (93 / 200) c) : B (-244911684607972231683 / 1000000000000000000) (-101150800838643467907 / 500000000000000000) ((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) := bmul (sGlobal23_hz76 hc) (sGlobal23_hz109 hc) (by norm_num) (by norm_num)

theorem sGlobal23_hz111 {c : ℝ} (hc : B (23 / 50) (93 / 200) c) : B (-244926735732716607963 / 1000000000000000000) (-20231665280203131209 / 100000000000000000) (((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) := bsub (sGlobal23_hz110 hc) sGlobal23_hz104 (by norm_num) (by norm_num)

theorem sGlobal23_hz112 {c : ℝ} (hc : B (23 / 50) (93 / 200) c) : B (-283423809186840877979 / 1000000000000000000) (-240813726253278582221 / 1000000000000000000) ((((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) - (s3rs 12225 46 maskSlack)) := bsub (sGlobal23_hz111 hc) sGlobal23_hz29 (by norm_num) (by norm_num)

theorem sGlobal23_hz113 {c : ℝ} (hc : B (23 / 50) (93 / 200) c) : B (-283423809186840877979 / 1000000000000000000) (-240813726253278582221 / 1000000000000000000) (s3L 12225 46 maskSlack c) := by
    convert (sGlobal23_hz112 hc) using 1 <;>
      norm_num [s3L] <;> ring

theorem sGlobal23_hz114 {c : ℝ} (hc : B (23 / 50) (93 / 200) c) : B 0 (830575810133194616873 / 500000000000000000) |(s3U 12225 46 maskSlack c)| := bweaken (babs (sGlobal23_hz107 hc)) (by norm_num) (by norm_num)

theorem sGlobal23_hz115 {c : ℝ} (hc : B (23 / 50) (93 / 200) c) : B 0 (283423809186840877979 / 1000000000000000000) |(s3L 12225 46 maskSlack c)| := bweaken (babs (sGlobal23_hz113 hc)) (by norm_num) (by norm_num)

theorem sGlobal23_hz116 {c : ℝ} (hc : B (23 / 50) (93 / 200) c) : B 0 (830575810133194616873 / 500000000000000000) (max |(s3U 12225 46 maskSlack c)| |(s3L 12225 46 maskSlack c)|) := bweaken (bmax (sGlobal23_hz114 hc) (sGlobal23_hz115 hc)) (by norm_num) (by norm_num)

theorem sGlobal23_hz117 {c : ℝ} (hc : B (23 / 50) (93 / 200) c) : B 0 (830575810133194616873 / 500000000000000000) (s3nks 12225 46 maskSlack c) := by
    convert (sGlobal23_hz116 hc) using 1 <;>
      norm_num [s3nks] <;> ring

theorem sGlobal23 {c : ℝ} (hc : B (23 / 50) (93 / 200) c) :
    0 < s3am 12225 46 ∧ 0 ≤ s3dm 12225 46 c ∧
    s3dm 12225 46 c ^ 2 ≤ 2 * s3ap 12225 46 ^ 2 ∧ s3c1 12225 46 c < 1 ∧
    0 ≤ s3Cpa 12225 c - s3r1 12225 46 ∧
    s3e0 12225 46 ≤ (s3Cpa 12225 c - s3r1 12225 46) / s3ap 12225 46 ∧
    s3nks 12225 46 maskSlack c ≤ 12225 * (67941 / 500000) := by

  refine ⟨lt_of_lt_of_le (by norm_num) sGlobal23_hz14.1,
    le_trans (by norm_num) (sGlobal23_hz64 hc).1, ?_,
    lt_of_le_of_lt (sGlobal23_hz72 hc).2 (by norm_num), ?_, ?_,
    le_trans (sGlobal23_hz117 hc).2 (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (sGlobal23_hz64 hc).1) (sGlobal23_hz64 hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) sGlobal23_hz9.1 2
    nlinarith only [h1, h2]
  · linarith only [(sGlobal23_hz84 hc).1, sGlobal23_hz33.2]
  · have hap : 0 < s3ap 12225 46 := lt_of_lt_of_le (by norm_num) sGlobal23_hz9.1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul sGlobal23_hz16.2 sGlobal23_hz9.2 (le_trans (by norm_num) sGlobal23_hz9.1) (by norm_num)
    linarith only [h, (sGlobal23_hz84 hc).1, sGlobal23_hz33.2]

end BstLean.Part255
