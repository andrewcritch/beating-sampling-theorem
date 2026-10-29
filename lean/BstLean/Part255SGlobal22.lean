import BstLean.Part255SGlobal18
import BstLean.Part255Numeric10
namespace BstLean.Part255
open Real BstLean.Part130 BstLean.Part182 BstLean.Part197 BstLean.Part246
theorem sGlobal22_hz0 : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal22_hz1 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) ((√(23 : ℝ)) / (12225 : ℝ)) := bdiv sGlobal22_hz0 (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal22_hz2 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) maskSlack := by
    convert sGlobal22_hz1 using 1 <;>
      norm_num [maskSlack] <;> ring

theorem sGlobal22_hz3 : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal22_hz4 : B (6395294793910793 / 500000000000000000) (12790589587821587 / 1000000000000000000) (√((2 / 12225) : ℝ)) := bsqrt (bpoint ((2 / 12225) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal22_hz5 : B (7230130686979 / 62500000000000000) (23136418198333 / 200000000000000000) (√((2 / 149450625) : ℝ)) := bsqrt (bpoint ((2 / 149450625) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal22_hz6 : B (2211334438749598093 / 20000000000000000) (110566721937479904651 / 1000000000000000000) (√(12225 : ℝ)) := bsqrt (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal22_hz7 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))) := bmul sGlobal22_hz3 sGlobal22_hz4 (by norm_num) (by norm_num)

theorem sGlobal22_hz8 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) ((√(12225 : ℝ)) + ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := badd sGlobal22_hz6 sGlobal22_hz7 (by norm_num) (by norm_num)

theorem sGlobal22_hz9 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) (s3ap 12225 46) := by
    convert sGlobal22_hz8 using 1 <;>
      norm_num [s3ap, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal22_hz10 : B (163599182004089 / 1000000000000000000) (16359918200409 / 100000000000000000) ((2 : ℝ) / (12225 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal22_hz11 : B (1222499983640081799591 / 100000000000000000) (12224999836400817995911 / 1000000000000000000) ((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ))) := bsub (bpoint (12225 : ℝ)) sGlobal22_hz10 (by norm_num) (by norm_num)

theorem sGlobal22_hz12 : B (110566721197658827907 / 1000000000000000000) (27641680299414706977 / 250000000000000000) (√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) := bsqrt sGlobal22_hz11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal22_hz13 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) ((√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) - ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bsub sGlobal22_hz12 sGlobal22_hz7 (by norm_num) (by norm_num)

theorem sGlobal22_hz14 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) (s3am 12225 46) := by
    convert sGlobal22_hz13 using 1 <;>
      norm_num [s3am, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal22_hz15 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√((2 / 12225) : ℝ)) * (√(92 : ℝ))) := bmul sGlobal22_hz4 sGlobal22_hz3 (by norm_num) (by norm_num)

theorem sGlobal22_hz16 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) (s3e0 12225 46) := by
    convert sGlobal22_hz15 using 1 <;>
      norm_num [s3e0, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal22_hz17 : B (250196148528560847 / 500000000000000000) (100078459411424339 / 200000000000000000) (((1 / 2) : ℝ) + maskSlack) := badd (bpoint ((1 / 2) : ℝ)) sGlobal22_hz2 (by norm_num) (by norm_num)

theorem sGlobal22_hz18 : B (59827153232297998295487 / 800000000000000) (23930861292919199366019 / 320000000000000) ((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack)) := bmul (bpoint (149450625 : ℝ)) sGlobal22_hz17 (by norm_num) (by norm_num)

theorem sGlobal22_hz19 : B (1729554180017180009583 / 200000000000000000) (8647770900085900056557 / 1000000000000000000) (√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) := bsqrt sGlobal22_hz18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal22_hz20 : B (4328681281566262743499 / 500000000000000000) (8657362563132525495641 / 1000000000000000000) ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))) := badd sGlobal22_hz19 sGlobal22_hz3 (by norm_num) (by norm_num)

theorem sGlobal22_hz21 : B (110732771457999278473 / 1000000000000000000) (55366385728999643621 / 500000000000000000) ((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ)))) := bmul sGlobal22_hz4 sGlobal22_hz20 (by norm_num) (by norm_num)

theorem sGlobal22_hz22 : B (209099159 / 15625000000000000) (13382346177 / 1000000000000000000) ((2 : ℝ) / (149450625 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (149450625 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal22_hz23 : B (2452349334953899930479 / 200000000000000000) (12261746674769501594427 / 1000000000000000000) (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2) := bsq sGlobal22_hz21 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal22_hz24 : B (82045469362091 / 500000000000000000) (32818187747289 / 200000000000000000) (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2)) := bmul sGlobal22_hz22 sGlobal22_hz23 (by norm_num) (by norm_num)

theorem sGlobal22_hz25 : B (82045469362091 / 250000000000000000) (32818187747289 / 100000000000000000) ((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) := bmul (bpoint (2 : ℝ)) sGlobal22_hz24 (by norm_num) (by norm_num)

theorem sGlobal22_hz26 : B (117258080744995992792057 / 1000000000000000000) (58629040372497996396029 / 500000000000000000) (√(13749457500 : ℝ)) := bsqrt (bpoint (13749457500 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal22_hz27 : B (117304080744995992792057 / 1000000000000000000) (58652040372497996396029 / 500000000000000000) ((√(13749457500 : ℝ)) + (46 : ℝ)) := badd sGlobal22_hz26 (bpoint (46 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal22_hz28 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal22_hz25 sGlobal22_hz27 (by norm_num) (by norm_num)

theorem sGlobal22_hz29 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (s3rs 12225 46 maskSlack) := by
    convert sGlobal22_hz28 using 1 <;>
      norm_num [s3rs, s3pp, s3K, mA, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal22_hz30 : B (490797546012267 / 1000000000000000000) (49079754601227 / 100000000000000000) ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (3 : ℝ)) sGlobal22_hz10 (by norm_num) (by norm_num)

theorem sGlobal22_hz31 : B (490797546012267 / 500000000000000000) (49079754601227 / 50000000000000000) ((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal22_hz30 (by norm_num) (by norm_num)

theorem sGlobal22_hz32 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal22_hz31 sGlobal22_hz27 (by norm_num) (by norm_num)

theorem sGlobal22_hz33 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (s3r1 12225 46) := by
    convert sGlobal22_hz32 using 1 <;>
      norm_num [s3r1, mA] <;> ring

theorem sGlobal22_hz34 : B (163599182004089 / 500000000000000000) (16359918200409 / 50000000000000000) ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (2 : ℝ)) sGlobal22_hz10 (by norm_num) (by norm_num)

theorem sGlobal22_hz35 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal22_hz34 (by norm_num) (by norm_num)

theorem sGlobal22_hz36 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal22_hz35 sGlobal22_hz27 (by norm_num) (by norm_num)

theorem sGlobal22_hz37 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (s3rpp 12225 46) := by
    convert sGlobal22_hz36 using 1 <;>
      norm_num [s3rpp, mA] <;> ring

theorem sGlobal22_hz38 {c : ℝ} (hc : B (91 / 200) (23 / 50) c) : B (91 / 200) (23 / 50) c := hc

theorem sGlobal22_hz39 : B (130072149143123719 / 200000000000000000) (650360745716543903 / 1000000000000000000) (kdot ((91 / 200))) := by
    constructor
    · apply bkdot_lower (q := (153005401607139999 / 250000000000000000)) (a := (54921205633321313 / 100000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (122404321285711999 / 200000000000000000)) (a := (274606028165879831 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal22_hz40 : B (8281 / 40000) (8281 / 40000) (((91 / 200) : ℝ)^2) := bsq (bpoint ((91 / 200) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal22_hz41 : B (31719 / 40000) (31719 / 40000) ((1 : ℝ) - (((91 / 200) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal22_hz40 (by norm_num) (by norm_num)

theorem sGlobal22_hz42 : B (111311429669194349 / 125000000000000000) (890491437353554793 / 1000000000000000000) (√((1 : ℝ) - (((91 / 200) : ℝ)^2))) := bsqrt sGlobal22_hz41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal22_hz43 : B (141726114035825093 / 500000000000000000) (70863057017912547 / 250000000000000000) ((√((1 : ℝ) - (((91 / 200) : ℝ)^2))) / Real.pi) := bdiv sGlobal22_hz42 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal22_hz44 : B (14795706965030323 / 50000000000000000) (73978534825256869 / 250000000000000000) (((91 / 200) : ℝ) * (kdot ((91 / 200)))) := bmul (bpoint ((91 / 200) : ℝ)) sGlobal22_hz39 (by norm_num) (by norm_num)

theorem sGlobal22_hz45 : B (289683183686128323 / 500000000000000000) (18105198980396177 / 31250000000000000) (((√((1 : ℝ) - (((91 / 200) : ℝ)^2))) / Real.pi) + (((91 / 200) : ℝ) * (kdot ((91 / 200))))) := badd sGlobal22_hz43 sGlobal22_hz44 (by norm_num) (by norm_num)

theorem sGlobal22_hz46 : B (289683183686128323 / 500000000000000000) (18105198980396177 / 31250000000000000) (kappa ((91 / 200))) := by rw [kappa_eq]; exact sGlobal22_hz45

theorem sGlobal22_hz47 : B (163037649309219301 / 250000000000000000) (326075298618777983 / 500000000000000000) (kdot ((23 / 50))) := by
    constructor
    · apply bkdot_lower (q := (121632728111907469 / 200000000000000000)) (a := (10928011282762237 / 20000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (9502556883742771 / 15625000000000000)) (a := (273200282068522827 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal22_hz48 : B (529 / 2500) (529 / 2500) (((23 / 50) : ℝ)^2) := bsq (bpoint ((23 / 50) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal22_hz49 : B (1971 / 2500) (1971 / 2500) ((1 : ℝ) - (((23 / 50) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal22_hz48 (by norm_num) (by norm_num)

theorem sGlobal22_hz50 : B (887918915216924523 / 1000000000000000000) (221979728804231131 / 250000000000000000) (√((1 : ℝ) - (((23 / 50) : ℝ)^2))) := bsqrt sGlobal22_hz49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal22_hz51 : B (282633368843134123 / 1000000000000000000) (2261066950745073 / 8000000000000000) ((√((1 : ℝ) - (((23 / 50) : ℝ)^2))) / Real.pi) := bdiv sGlobal22_hz50 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal22_hz52 : B (299989274728963513 / 1000000000000000000) (59997854945855149 / 200000000000000000) (((23 / 50) : ℝ) * (kdot ((23 / 50)))) := bmul (bpoint ((23 / 50) : ℝ)) sGlobal22_hz47 (by norm_num) (by norm_num)

theorem sGlobal22_hz53 : B (145655660893024409 / 250000000000000000) (58262264357240987 / 100000000000000000) (((√((1 : ℝ) - (((23 / 50) : ℝ)^2))) / Real.pi) + (((23 / 50) : ℝ) * (kdot ((23 / 50))))) := badd sGlobal22_hz51 sGlobal22_hz52 (by norm_num) (by norm_num)

theorem sGlobal22_hz54 : B (145655660893024409 / 250000000000000000) (58262264357240987 / 100000000000000000) (kappa ((23 / 50))) := by rw [kappa_eq]; exact sGlobal22_hz53

theorem sGlobal22_hz55 {c : ℝ} (hc : B (91 / 200) (23 / 50) c) : B (289683183686128323 / 500000000000000000) (58262264357240987 / 100000000000000000) (kappa c) := bkappa (sGlobal22_hz38 hc) (by norm_num) (by norm_num) sGlobal22_hz46.1 sGlobal22_hz54.2

theorem sGlobal22_hz56 : B 24450 24450 ((2 : ℝ) * (12225 : ℝ)) := bmul (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal22_hz57 {c : ℝ} (hc : B (91 / 200) (23 / 50) c) : B (41737735642759013 / 100000000000000000) (210316816313871677 / 500000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (sGlobal22_hz55 hc) (by norm_num) (by norm_num)

theorem sGlobal22_hz58 {c : ℝ} (hc : B (91 / 200) (23 / 50) c) : B (20409752729309157357 / 2000000000000000) (102844923177483250053 / 10000000000000000) (((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) := bmul sGlobal22_hz56 (sGlobal22_hz57 hc) (by norm_num) (by norm_num)

theorem sGlobal22_hz59 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (4 : ℝ)) sGlobal22_hz10 (by norm_num) (by norm_num)

theorem sGlobal22_hz60 {c : ℝ} (hc : B (91 / 200) (23 / 50) c) : B (510243785512892533107 / 50000000000000000) (642780728959474811809 / 62500000000000000) ((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bsub (sGlobal22_hz58 hc) sGlobal22_hz59 (by norm_num) (by norm_num)

theorem sGlobal22_hz61 {c : ℝ} (hc : B (91 / 200) (23 / 50) c) : B (25254796215592706033 / 250000000000000000) (126765603473445707 / 1250000000000000) (√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) := bsqrt (sGlobal22_hz60 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal22_hz62 : B (30670756373515103 / 125000000000000000) (122683025494060423 / 500000000000000000) ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal22_hz7 (by norm_num) (by norm_num)

theorem sGlobal22_hz63 {c : ℝ} (hc : B (91 / 200) (23 / 50) c) : B (50386909405691351643 / 500000000000000000) (12645889590971055597 / 125000000000000000) ((√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) - ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))))) := bsub (sGlobal22_hz61 hc) sGlobal22_hz62 (by norm_num) (by norm_num)

theorem sGlobal22_hz64 {c : ℝ} (hc : B (91 / 200) (23 / 50) c) : B (50386909405691351643 / 500000000000000000) (12645889590971055597 / 125000000000000000) (s3dm 12225 46 c) := by
    convert (sGlobal22_hz63 hc) using 1 <;>
      norm_num [s3dm, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal22_hz65 : B (6126072185528622723889 / 500000000000000000) (2450428874211449090087 / 200000000000000000) ((s3ap 12225 46)^2) := bsq sGlobal22_hz9 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal22_hz66 : B (6126072185528622723889 / 250000000000000000) (2450428874211449090087 / 100000000000000000) ((2 : ℝ) * ((s3ap 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal22_hz65 (by norm_num) (by norm_num)

theorem sGlobal22_hz67 {c : ℝ} (hc : B (91 / 200) (23 / 50) c) : B (2538840639457347599231 / 250000000000000000) (5117392753504962938617 / 500000000000000000) ((s3dm 12225 46 c)^2) := bsq (sGlobal22_hz64 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal22_hz68 {c : ℝ} (hc : B (91 / 200) (23 / 50) c) : B (7134751617552282509161 / 500000000000000000) (7174463092142550251973 / 500000000000000000) (((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) := bsub sGlobal22_hz66 (sGlobal22_hz67 hc) (by norm_num) (by norm_num)

theorem sGlobal22_hz69 : B (1524735695971823534271 / 125000000000000000) (609894278388729413841 / 50000000000000000) ((s3am 12225 46)^2) := bsq sGlobal22_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal22_hz70 : B (1524735695971823534271 / 62500000000000000) (609894278388729413841 / 25000000000000000) ((2 : ℝ) * ((s3am 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal22_hz69 (by norm_num) (by norm_num)

theorem sGlobal22_hz71 {c : ℝ} (hc : B (91 / 200) (23 / 50) c) : B (146229270186004127 / 250000000000000000) (294086341943420799 / 500000000000000000) ((((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) / ((2 : ℝ) * ((s3am 12225 46)^2))) := bdiv (sGlobal22_hz68 hc) sGlobal22_hz70 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal22_hz72 {c : ℝ} (hc : B (91 / 200) (23 / 50) c) : B (146229270186004127 / 250000000000000000) (294086341943420799 / 500000000000000000) (s3c1 12225 46 c) := by
    convert (sGlobal22_hz71 hc) using 1 <;>
      norm_num [s3c1] <;> ring

theorem sGlobal22_hz73 {c : ℝ} (hc : B (91 / 200) (23 / 50) c) : B (130072149143123719 / 200000000000000000) (326075298618777983 / 500000000000000000) (kdot c) := bkdot (sGlobal22_hz38 hc) sGlobal22_hz39.1 sGlobal22_hz47.2

theorem sGlobal22_hz74 : B (698872957570754677 / 1000000000000000000) (698872957570754823 / 1000000000000000000) (kdot ((146229270186004127 / 250000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (511757431849926337 / 1000000000000000000)) (a := (14781539129577173 / 31250000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (7996209872655099 / 15625000000000000)) (a := (118252313036617327 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal22_hz75 : B (350076231262144801 / 500000000000000000) (700152462524289717 / 1000000000000000000) (kdot ((294086341943420799 / 500000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (50922382387163007 / 100000000000000000)) (a := (470999410465341 / 1000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (509223823871630069 / 1000000000000000000)) (a := (470999410465340821 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal22_hz76 {c : ℝ} (hc : B (91 / 200) (23 / 50) c) : B (698872957570754677 / 1000000000000000000) (700152462524289717 / 1000000000000000000) (kdot (s3c1 12225 46 c)) := bkdot (sGlobal22_hz72 hc) sGlobal22_hz74.1 sGlobal22_hz75.2

theorem sGlobal22_hz77 {c : ℝ} (hc : B (91 / 200) (23 / 50) c) : B (8281 / 40000) (529 / 2500) (c^2) := bsq (sGlobal22_hz38 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal22_hz78 {c : ℝ} (hc : B (91 / 200) (23 / 50) c) : B (1971 / 2500) (31719 / 40000) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (sGlobal22_hz77 hc) (by norm_num) (by norm_num)

theorem sGlobal22_hz79 {c : ℝ} (hc : B (91 / 200) (23 / 50) c) : B (887918915216924523 / 1000000000000000000) (890491437353554793 / 1000000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (sGlobal22_hz78 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal22_hz80 : B (39119999999999765769 / 1600000000000000) (3912000000000000489 / 160000000000000) ((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (149450625 : ℝ)) sGlobal22_hz10 (by norm_num) (by norm_num)

theorem sGlobal22_hz81 {c : ℝ} (hc : B (91 / 200) (23 / 50) c) : B (115493521567096431 / 200000000000000000) (145183630676262603 / 250000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (sGlobal22_hz79 hc) (sGlobal22_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal22_hz82 {c : ℝ} (hc : B (91 / 200) (23 / 50) c) : B (705954150578872707587 / 50000000000000000) (1419895908013848434827 / 100000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) := bmul sGlobal22_hz80 (sGlobal22_hz81 hc) (by norm_num) (by norm_num)

theorem sGlobal22_hz83 {c : ℝ} (hc : B (91 / 200) (23 / 50) c) : B (705954150578872707587 / 100000000000000000) (1419895908013848434827 / 200000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) / (2 : ℝ)) := bdiv (sGlobal22_hz82 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal22_hz84 {c : ℝ} (hc : B (91 / 200) (23 / 50) c) : B (705954150578872707587 / 100000000000000000) (1419895908013848434827 / 200000000000000000) (s3Cpa 12225 c) := by
    convert (sGlobal22_hz83 hc) using 1 <;>
      norm_num [s3Cpa, mA] <;> ring

theorem sGlobal22_hz85 {c : ℝ} (hc : B (91 / 200) (23 / 50) c) : B (282633368843134123 / 1000000000000000000) (70863057017912547 / 250000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (sGlobal22_hz79 hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal22_hz86 {c : ℝ} (hc : B (91 / 200) (23 / 50) c) : B (14795706965030323 / 50000000000000000) (59997854945855149 / 200000000000000000) (c * (kdot c)) := bmul (sGlobal22_hz38 hc) (sGlobal22_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal22_hz87 {c : ℝ} (hc : B (91 / 200) (23 / 50) c) : B (-8677952943070811 / 500000000000000000) (-778869451809767 / 62500000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (sGlobal22_hz85 hc) (sGlobal22_hz86 hc) (by norm_num) (by norm_num)

theorem sGlobal22_hz88 {c : ℝ} (hc : B (91 / 200) (23 / 50) c) : B (-13260996841130084717 / 31250000000000000) (-152346864773989513023 / 500000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) := bmul sGlobal22_hz80 (sGlobal22_hz87 hc) (by norm_num) (by norm_num)

theorem sGlobal22_hz89 {c : ℝ} (hc : B (91 / 200) (23 / 50) c) : B (-13260996841130084717 / 62500000000000000) (-152346864773989513023 / 1000000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) / (2 : ℝ)) := bdiv (sGlobal22_hz88 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal22_hz90 {c : ℝ} (hc : B (91 / 200) (23 / 50) c) : B (-13260996841130084717 / 62500000000000000) (-152346864773989513023 / 1000000000000000000) (s3Cpp 12225 c) := by
    convert (sGlobal22_hz89 hc) using 1 <;>
      norm_num [s3Cpp, mA] <;> ring

theorem sGlobal22_hz91 {c : ℝ} (hc : B (91 / 200) (23 / 50) c) : B (7174686615722464784271 / 1000000000000000000) (7214624650002980586361 / 1000000000000000000) ((s3Cpa 12225 c) + (s3r1 12225 46)) := badd (sGlobal22_hz84 hc) sGlobal22_hz33 (by norm_num) (by norm_num)

theorem sGlobal22_hz92 {c : ℝ} (hc : B (91 / 200) (23 / 50) c) : B (64962190213819096419 / 1000000000000000000) (13064760704885714413 / 200000000000000000) (((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) := bdiv (sGlobal22_hz91 hc) sGlobal22_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal22_hz93 {c : ℝ} (hc : B (91 / 200) (23 / 50) c) : B (65084873239313156831 / 1000000000000000000) (8180810818740329061 / 125000000000000000) ((((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) + (s3e0 12225 46)) := badd (sGlobal22_hz92 hc) sGlobal22_hz16 (by norm_num) (by norm_num)

theorem sGlobal22_hz94 {c : ℝ} (hc : B (91 / 200) (23 / 50) c) : B (65084873239313156831 / 1000000000000000000) (8180810818740329061 / 125000000000000000) (s3Lam 12225 46 c) := by
    convert (sGlobal22_hz93 hc) using 1 <;>
      norm_num [s3Lam] <;> ring

theorem sGlobal22_hz95 {c : ℝ} (hc : B (91 / 200) (23 / 50) c) : B (-8463283927224346867 / 62500000000000000) (-15116691630299447641 / 200000000000000000) ((s3Cpp 12225 c) + (s3rpp 12225 46)) := badd (sGlobal22_hz90 hc) sGlobal22_hz37 (by norm_num) (by norm_num)

theorem sGlobal22_hz96 {c : ℝ} (hc : B (91 / 200) (23 / 50) c) : B (-47404712661506944163 / 500000000000000000) (-18895864537874309551 / 500000000000000000) (if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) := bweaken (bfirst (sGlobal22_hz95 hc) (sGlobal22_hz76 hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem sGlobal22_hz97 {c : ℝ} (hc : B (91 / 200) (23 / 50) c) : B (211802036228873094821 / 50000000000000000) (4283242601729204038833 / 1000000000000000000) ((s3Lam 12225 46 c)^2) := bsq (sGlobal22_hz94 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal22_hz98 {c : ℝ} (hc : B (91 / 200) (23 / 50) c) : B (342127991346102327 / 1000000000000000000) (172973553035325247 / 500000000000000000) ((s3c1 12225 46 c)^2) := bsq (sGlobal22_hz72 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal22_hz99 {c : ℝ} (hc : B (91 / 200) (23 / 50) c) : B (327026446964674753 / 500000000000000000) (657872008653897673 / 1000000000000000000) ((1 : ℝ) - ((s3c1 12225 46 c)^2)) := bsub (bpoint (1 : ℝ)) (sGlobal22_hz98 hc) (by norm_num) (by norm_num)

theorem sGlobal22_hz100 {c : ℝ} (hc : B (91 / 200) (23 / 50) c) : B (202183841764331761 / 250000000000000000) (405546547468320113 / 500000000000000000) (√((1 : ℝ) - ((s3c1 12225 46 c)^2))) := bsqrt (sGlobal22_hz99 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal22_hz101 {c : ℝ} (hc : B (91 / 200) (23 / 50) c) : B (1270358543922771761 / 500000000000000000) (1274062054215178829 / 500000000000000000) (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))) := bmul pi_mem (sGlobal22_hz100 hc) (by norm_num) (by norm_num)

theorem sGlobal22_hz102 {c : ℝ} (hc : B (91 / 200) (23 / 50) c) : B (1662415386504411465683 / 1000000000000000000) (842920020930247105531 / 500000000000000000) (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2))))) := bdiv (sGlobal22_hz97 hc) (sGlobal22_hz101 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal22_hz103 {c : ℝ} (hc : B (91 / 200) (23 / 50) c) : B (1567605961181397577357 / 1000000000000000000) (41201207819618639799 / 25000000000000000) ((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) := badd (sGlobal22_hz96 hc) (sGlobal22_hz102 hc) (by norm_num) (by norm_num)

theorem sGlobal22_hz104 : B (3762781186094069 / 250000000000000000) (376278118609407 / 25000000000000000) ((s3e0 12225 46)^2) := bsq sGlobal22_hz16 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal22_hz105 {c : ℝ} (hc : B (91 / 200) (23 / 50) c) : B (1567621012306141953633 / 1000000000000000000) (20600792048868624603 / 12500000000000000) (((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) := badd (sGlobal22_hz103 hc) sGlobal22_hz104 (by norm_num) (by norm_num)

theorem sGlobal22_hz106 {c : ℝ} (hc : B (91 / 200) (23 / 50) c) : B (401529521439347305941 / 250000000000000000) (105410027335225889891 / 62500000000000000) ((((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) + (s3rs 12225 46 maskSlack)) := badd (sGlobal22_hz105 hc) sGlobal22_hz29 (by norm_num) (by norm_num)

theorem sGlobal22_hz107 {c : ℝ} (hc : B (91 / 200) (23 / 50) c) : B (401529521439347305941 / 250000000000000000) (105410027335225889891 / 62500000000000000) (s3U 12225 46 maskSlack c) := by
    convert (sGlobal22_hz106 hc) using 1 <;>
      norm_num [s3U] <;> ring

theorem sGlobal22_hz108 {c : ℝ} (hc : B (91 / 200) (23 / 50) c) : B (-28893935608057363029 / 100000000000000000) (-229110271396481318623 / 1000000000000000000) ((s3Cpp 12225 c) - (s3rpp 12225 46)) := bsub (sGlobal22_hz90 hc) sGlobal22_hz37 (by norm_num) (by norm_num)

theorem sGlobal22_hz109 {c : ℝ} (hc : B (91 / 200) (23 / 50) c) : B (-28893935608057363029 / 100000000000000000) (-229110271396481318623 / 1000000000000000000) (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ)) := bweaken (bmin (sGlobal22_hz108 hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem sGlobal22_hz110 {c : ℝ} (hc : B (91 / 200) (23 / 50) c) : B (-4046032033599924617 / 20000000000000000) (-160118972980697177489 / 1000000000000000000) ((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) := bmul (sGlobal22_hz76 hc) (sGlobal22_hz109 hc) (by norm_num) (by norm_num)

theorem sGlobal22_hz111 {c : ℝ} (hc : B (91 / 200) (23 / 50) c) : B (-20231665280474060713 / 100000000000000000) (-32026804821088310753 / 200000000000000000) (((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) := bsub (sGlobal22_hz110 hc) sGlobal22_hz104 (by norm_num) (by norm_num)

theorem sGlobal22_hz112 {c : ℝ} (hc : B (91 / 200) (23 / 50) c) : B (-120406863129432438573 / 500000000000000000) (-24828887194586102987 / 125000000000000000) ((((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) - (s3rs 12225 46 maskSlack)) := bsub (sGlobal22_hz111 hc) sGlobal22_hz29 (by norm_num) (by norm_num)

theorem sGlobal22_hz113 {c : ℝ} (hc : B (91 / 200) (23 / 50) c) : B (-120406863129432438573 / 500000000000000000) (-24828887194586102987 / 125000000000000000) (s3L 12225 46 maskSlack c) := by
    convert (sGlobal22_hz112 hc) using 1 <;>
      norm_num [s3L] <;> ring

theorem sGlobal22_hz114 {c : ℝ} (hc : B (91 / 200) (23 / 50) c) : B 0 (105410027335225889891 / 62500000000000000) |(s3U 12225 46 maskSlack c)| := bweaken (babs (sGlobal22_hz107 hc)) (by norm_num) (by norm_num)

theorem sGlobal22_hz115 {c : ℝ} (hc : B (91 / 200) (23 / 50) c) : B 0 (120406863129432438573 / 500000000000000000) |(s3L 12225 46 maskSlack c)| := bweaken (babs (sGlobal22_hz113 hc)) (by norm_num) (by norm_num)

theorem sGlobal22_hz116 {c : ℝ} (hc : B (91 / 200) (23 / 50) c) : B 0 (105410027335225889891 / 62500000000000000) (max |(s3U 12225 46 maskSlack c)| |(s3L 12225 46 maskSlack c)|) := bweaken (bmax (sGlobal22_hz114 hc) (sGlobal22_hz115 hc)) (by norm_num) (by norm_num)

theorem sGlobal22_hz117 {c : ℝ} (hc : B (91 / 200) (23 / 50) c) : B 0 (105410027335225889891 / 62500000000000000) (s3nks 12225 46 maskSlack c) := by
    convert (sGlobal22_hz116 hc) using 1 <;>
      norm_num [s3nks] <;> ring

theorem sGlobal22 {c : ℝ} (hc : B (91 / 200) (23 / 50) c) :
    0 < s3am 12225 46 ∧ 0 ≤ s3dm 12225 46 c ∧
    s3dm 12225 46 c ^ 2 ≤ 2 * s3ap 12225 46 ^ 2 ∧ s3c1 12225 46 c < 1 ∧
    0 ≤ s3Cpa 12225 c - s3r1 12225 46 ∧
    s3e0 12225 46 ≤ (s3Cpa 12225 c - s3r1 12225 46) / s3ap 12225 46 ∧
    s3nks 12225 46 maskSlack c ≤ 12225 * (3449 / 25000) := by

  refine ⟨lt_of_lt_of_le (by norm_num) sGlobal22_hz14.1,
    le_trans (by norm_num) (sGlobal22_hz64 hc).1, ?_,
    lt_of_le_of_lt (sGlobal22_hz72 hc).2 (by norm_num), ?_, ?_,
    le_trans (sGlobal22_hz117 hc).2 (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (sGlobal22_hz64 hc).1) (sGlobal22_hz64 hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) sGlobal22_hz9.1 2
    nlinarith only [h1, h2]
  · linarith only [(sGlobal22_hz84 hc).1, sGlobal22_hz33.2]
  · have hap : 0 < s3ap 12225 46 := lt_of_lt_of_le (by norm_num) sGlobal22_hz9.1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul sGlobal22_hz16.2 sGlobal22_hz9.2 (le_trans (by norm_num) sGlobal22_hz9.1) (by norm_num)
    linarith only [h, (sGlobal22_hz84 hc).1, sGlobal22_hz33.2]

end BstLean.Part255
