import BstLean.Part255SGlobal17
import BstLean.Part255Numeric10
namespace BstLean.Part255
open Real BstLean.Part130 BstLean.Part182 BstLean.Part197 BstLean.Part246
theorem sGlobal21_hz0 : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal21_hz1 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) ((√(23 : ℝ)) / (12225 : ℝ)) := bdiv sGlobal21_hz0 (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal21_hz2 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) maskSlack := by
    convert sGlobal21_hz1 using 1 <;>
      norm_num [maskSlack] <;> ring

theorem sGlobal21_hz3 : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal21_hz4 : B (6395294793910793 / 500000000000000000) (12790589587821587 / 1000000000000000000) (√((2 / 12225) : ℝ)) := bsqrt (bpoint ((2 / 12225) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal21_hz5 : B (7230130686979 / 62500000000000000) (23136418198333 / 200000000000000000) (√((2 / 149450625) : ℝ)) := bsqrt (bpoint ((2 / 149450625) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal21_hz6 : B (2211334438749598093 / 20000000000000000) (110566721937479904651 / 1000000000000000000) (√(12225 : ℝ)) := bsqrt (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal21_hz7 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))) := bmul sGlobal21_hz3 sGlobal21_hz4 (by norm_num) (by norm_num)

theorem sGlobal21_hz8 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) ((√(12225 : ℝ)) + ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := badd sGlobal21_hz6 sGlobal21_hz7 (by norm_num) (by norm_num)

theorem sGlobal21_hz9 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) (s3ap 12225 46) := by
    convert sGlobal21_hz8 using 1 <;>
      norm_num [s3ap, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal21_hz10 : B (163599182004089 / 1000000000000000000) (16359918200409 / 100000000000000000) ((2 : ℝ) / (12225 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal21_hz11 : B (1222499983640081799591 / 100000000000000000) (12224999836400817995911 / 1000000000000000000) ((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ))) := bsub (bpoint (12225 : ℝ)) sGlobal21_hz10 (by norm_num) (by norm_num)

theorem sGlobal21_hz12 : B (110566721197658827907 / 1000000000000000000) (27641680299414706977 / 250000000000000000) (√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) := bsqrt sGlobal21_hz11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal21_hz13 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) ((√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) - ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bsub sGlobal21_hz12 sGlobal21_hz7 (by norm_num) (by norm_num)

theorem sGlobal21_hz14 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) (s3am 12225 46) := by
    convert sGlobal21_hz13 using 1 <;>
      norm_num [s3am, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal21_hz15 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√((2 / 12225) : ℝ)) * (√(92 : ℝ))) := bmul sGlobal21_hz4 sGlobal21_hz3 (by norm_num) (by norm_num)

theorem sGlobal21_hz16 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) (s3e0 12225 46) := by
    convert sGlobal21_hz15 using 1 <;>
      norm_num [s3e0, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal21_hz17 : B (250196148528560847 / 500000000000000000) (100078459411424339 / 200000000000000000) (((1 / 2) : ℝ) + maskSlack) := badd (bpoint ((1 / 2) : ℝ)) sGlobal21_hz2 (by norm_num) (by norm_num)

theorem sGlobal21_hz18 : B (59827153232297998295487 / 800000000000000) (23930861292919199366019 / 320000000000000) ((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack)) := bmul (bpoint (149450625 : ℝ)) sGlobal21_hz17 (by norm_num) (by norm_num)

theorem sGlobal21_hz19 : B (1729554180017180009583 / 200000000000000000) (8647770900085900056557 / 1000000000000000000) (√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) := bsqrt sGlobal21_hz18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal21_hz20 : B (4328681281566262743499 / 500000000000000000) (8657362563132525495641 / 1000000000000000000) ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))) := badd sGlobal21_hz19 sGlobal21_hz3 (by norm_num) (by norm_num)

theorem sGlobal21_hz21 : B (110732771457999278473 / 1000000000000000000) (55366385728999643621 / 500000000000000000) ((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ)))) := bmul sGlobal21_hz4 sGlobal21_hz20 (by norm_num) (by norm_num)

theorem sGlobal21_hz22 : B (209099159 / 15625000000000000) (13382346177 / 1000000000000000000) ((2 : ℝ) / (149450625 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (149450625 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal21_hz23 : B (2452349334953899930479 / 200000000000000000) (12261746674769501594427 / 1000000000000000000) (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2) := bsq sGlobal21_hz21 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal21_hz24 : B (82045469362091 / 500000000000000000) (32818187747289 / 200000000000000000) (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2)) := bmul sGlobal21_hz22 sGlobal21_hz23 (by norm_num) (by norm_num)

theorem sGlobal21_hz25 : B (82045469362091 / 250000000000000000) (32818187747289 / 100000000000000000) ((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) := bmul (bpoint (2 : ℝ)) sGlobal21_hz24 (by norm_num) (by norm_num)

theorem sGlobal21_hz26 : B (117258080744995992792057 / 1000000000000000000) (58629040372497996396029 / 500000000000000000) (√(13749457500 : ℝ)) := bsqrt (bpoint (13749457500 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal21_hz27 : B (117304080744995992792057 / 1000000000000000000) (58652040372497996396029 / 500000000000000000) ((√(13749457500 : ℝ)) + (46 : ℝ)) := badd sGlobal21_hz26 (bpoint (46 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal21_hz28 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal21_hz25 sGlobal21_hz27 (by norm_num) (by norm_num)

theorem sGlobal21_hz29 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (s3rs 12225 46 maskSlack) := by
    convert sGlobal21_hz28 using 1 <;>
      norm_num [s3rs, s3pp, s3K, mA, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal21_hz30 : B (490797546012267 / 1000000000000000000) (49079754601227 / 100000000000000000) ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (3 : ℝ)) sGlobal21_hz10 (by norm_num) (by norm_num)

theorem sGlobal21_hz31 : B (490797546012267 / 500000000000000000) (49079754601227 / 50000000000000000) ((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal21_hz30 (by norm_num) (by norm_num)

theorem sGlobal21_hz32 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal21_hz31 sGlobal21_hz27 (by norm_num) (by norm_num)

theorem sGlobal21_hz33 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (s3r1 12225 46) := by
    convert sGlobal21_hz32 using 1 <;>
      norm_num [s3r1, mA] <;> ring

theorem sGlobal21_hz34 : B (163599182004089 / 500000000000000000) (16359918200409 / 50000000000000000) ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (2 : ℝ)) sGlobal21_hz10 (by norm_num) (by norm_num)

theorem sGlobal21_hz35 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal21_hz34 (by norm_num) (by norm_num)

theorem sGlobal21_hz36 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal21_hz35 sGlobal21_hz27 (by norm_num) (by norm_num)

theorem sGlobal21_hz37 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (s3rpp 12225 46) := by
    convert sGlobal21_hz36 using 1 <;>
      norm_num [s3rpp, mA] <;> ring

theorem sGlobal21_hz38 {c : ℝ} (hc : B (9 / 20) (91 / 200) c) : B (9 / 20) (91 / 200) c := hc

theorem sGlobal21_hz39 : B (32428801097325763 / 50000000000000000) (64857602194777443 / 100000000000000000) (kdot ((9 / 20))) := by
    constructor
    · apply bkdot_lower (q := (307940881025719857 / 500000000000000000)) (a := (552015493874064193 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (615881762051439713 / 1000000000000000000)) (a := (276007746936043147 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal21_hz40 : B (81 / 400) (81 / 400) (((9 / 20) : ℝ)^2) := bsq (bpoint ((9 / 20) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal21_hz41 : B (319 / 400) (319 / 400) ((1 : ℝ) - (((9 / 20) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal21_hz40 (by norm_num) (by norm_num)

theorem sGlobal21_hz42 : B (13953571171477931 / 15625000000000000) (178605710994917517 / 200000000000000000) (√((1 : ℝ) - (((9 / 20) : ℝ)^2))) := bsqrt sGlobal21_hz41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal21_hz43 : B (35532477211604503 / 125000000000000000) (11370392707713441 / 40000000000000000) ((√((1 : ℝ) - (((9 / 20) : ℝ)^2))) / Real.pi) := bdiv sGlobal21_hz42 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal21_hz44 : B (291859209875931867 / 1000000000000000000) (145929604938249247 / 500000000000000000) (((9 / 20) : ℝ) * (kdot ((9 / 20)))) := bmul (bpoint ((9 / 20) : ℝ)) sGlobal21_hz39 (by norm_num) (by norm_num)

theorem sGlobal21_hz45 : B (576119027568767891 / 1000000000000000000) (576119027569334519 / 1000000000000000000) (((√((1 : ℝ) - (((9 / 20) : ℝ)^2))) / Real.pi) + (((9 / 20) : ℝ) * (kdot ((9 / 20))))) := badd sGlobal21_hz43 sGlobal21_hz44 (by norm_num) (by norm_num)

theorem sGlobal21_hz46 : B (576119027568767891 / 1000000000000000000) (576119027569334519 / 1000000000000000000) (kappa ((9 / 20))) := by rw [kappa_eq]; exact sGlobal21_hz45

theorem sGlobal21_hz47 : B (130072149143123719 / 200000000000000000) (650360745716543903 / 1000000000000000000) (kdot ((91 / 200))) := by
    constructor
    · apply bkdot_lower (q := (153005401607139999 / 250000000000000000)) (a := (54921205633321313 / 100000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (122404321285711999 / 200000000000000000)) (a := (274606028165879831 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal21_hz48 : B (8281 / 40000) (8281 / 40000) (((91 / 200) : ℝ)^2) := bsq (bpoint ((91 / 200) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal21_hz49 : B (31719 / 40000) (31719 / 40000) ((1 : ℝ) - (((91 / 200) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal21_hz48 (by norm_num) (by norm_num)

theorem sGlobal21_hz50 : B (111311429669194349 / 125000000000000000) (890491437353554793 / 1000000000000000000) (√((1 : ℝ) - (((91 / 200) : ℝ)^2))) := bsqrt sGlobal21_hz49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal21_hz51 : B (141726114035825093 / 500000000000000000) (70863057017912547 / 250000000000000000) ((√((1 : ℝ) - (((91 / 200) : ℝ)^2))) / Real.pi) := bdiv sGlobal21_hz50 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal21_hz52 : B (14795706965030323 / 50000000000000000) (73978534825256869 / 250000000000000000) (((91 / 200) : ℝ) * (kdot ((91 / 200)))) := bmul (bpoint ((91 / 200) : ℝ)) sGlobal21_hz47 (by norm_num) (by norm_num)

theorem sGlobal21_hz53 : B (289683183686128323 / 500000000000000000) (18105198980396177 / 31250000000000000) (((√((1 : ℝ) - (((91 / 200) : ℝ)^2))) / Real.pi) + (((91 / 200) : ℝ) * (kdot ((91 / 200))))) := badd sGlobal21_hz51 sGlobal21_hz52 (by norm_num) (by norm_num)

theorem sGlobal21_hz54 : B (289683183686128323 / 500000000000000000) (18105198980396177 / 31250000000000000) (kappa ((91 / 200))) := by rw [kappa_eq]; exact sGlobal21_hz53

theorem sGlobal21_hz55 {c : ℝ} (hc : B (9 / 20) (91 / 200) c) : B (576119027568767891 / 1000000000000000000) (18105198980396177 / 31250000000000000) (kappa c) := bkappa (sGlobal21_hz38 hc) (by norm_num) (by norm_num) sGlobal21_hz46.1 sGlobal21_hz54.2

theorem sGlobal21_hz56 : B 24450 24450 ((2 : ℝ) * (12225 : ℝ)) := bmul (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal21_hz57 {c : ℝ} (hc : B (9 / 20) (91 / 200) c) : B (13144801019603823 / 31250000000000000) (423880972431232109 / 1000000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (sGlobal21_hz55 hc) (by norm_num) (by norm_num)

theorem sGlobal21_hz58 {c : ℝ} (hc : B (9 / 20) (91 / 200) c) : B (6427807698586269447 / 625000000000000) (207277795518872501301 / 20000000000000000) (((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) := bmul sGlobal21_hz56 (sGlobal21_hz57 hc) (by norm_num) (by norm_num)

theorem sGlobal21_hz59 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (4 : ℝ)) sGlobal21_hz10 (by norm_num) (by norm_num)

theorem sGlobal21_hz60 {c : ℝ} (hc : B (9 / 20) (91 / 200) c) : B (257112291583532577471 / 25000000000000000) (5181944560773448524347 / 500000000000000000) ((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bsub (sGlobal21_hz58 hc) sGlobal21_hz59 (by norm_num) (by norm_num)

theorem sGlobal21_hz61 {c : ℝ} (hc : B (9 / 20) (91 / 200) c) : B (5070624138935290651 / 50000000000000000) (101803188169854960829 / 1000000000000000000) (√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) := bsqrt (sGlobal21_hz60 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal21_hz62 : B (30670756373515103 / 125000000000000000) (122683025494060423 / 500000000000000000) ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal21_hz7 (by norm_num) (by norm_num)

theorem sGlobal21_hz63 {c : ℝ} (hc : B (9 / 20) (91 / 200) c) : B (50583558363858846087 / 500000000000000000) (20311564423773368001 / 200000000000000000) ((√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) - ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))))) := bsub (sGlobal21_hz61 hc) sGlobal21_hz62 (by norm_num) (by norm_num)

theorem sGlobal21_hz64 {c : ℝ} (hc : B (9 / 20) (91 / 200) c) : B (50583558363858846087 / 500000000000000000) (20311564423773368001 / 200000000000000000) (s3dm 12225 46 c) := by
    convert (sGlobal21_hz63 hc) using 1 <;>
      norm_num [s3dm, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal21_hz65 : B (6126072185528622723889 / 500000000000000000) (2450428874211449090087 / 200000000000000000) ((s3ap 12225 46)^2) := bsq sGlobal21_hz9 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal21_hz66 : B (6126072185528622723889 / 250000000000000000) (2450428874211449090087 / 100000000000000000) ((2 : ℝ) * ((s3ap 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal21_hz65 (by norm_num) (by norm_num)

theorem sGlobal21_hz67 {c : ℝ} (hc : B (9 / 20) (91 / 200) c) : B (10234785506999656888411 / 1000000000000000000) (1031399123352739877199 / 100000000000000000) ((s3dm 12225 46 c)^2) := bsq (sGlobal21_hz64 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal21_hz68 {c : ℝ} (hc : B (9 / 20) (91 / 200) c) : B (7095148754293546061783 / 500000000000000000) (14269503235114834012459 / 1000000000000000000) (((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) := bsub sGlobal21_hz66 (sGlobal21_hz67 hc) (by norm_num) (by norm_num)

theorem sGlobal21_hz69 : B (1524735695971823534271 / 125000000000000000) (609894278388729413841 / 50000000000000000) ((s3am 12225 46)^2) := bsq sGlobal21_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal21_hz70 : B (1524735695971823534271 / 62500000000000000) (609894278388729413841 / 25000000000000000) ((2 : ℝ) * ((s3am 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal21_hz69 (by norm_num) (by norm_num)

theorem sGlobal21_hz71 {c : ℝ} (hc : B (9 / 20) (91 / 200) c) : B (3635439885703487 / 6250000000000000) (584917080744437443 / 1000000000000000000) ((((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) / ((2 : ℝ) * ((s3am 12225 46)^2))) := bdiv (sGlobal21_hz68 hc) sGlobal21_hz70 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal21_hz72 {c : ℝ} (hc : B (9 / 20) (91 / 200) c) : B (3635439885703487 / 6250000000000000) (584917080744437443 / 1000000000000000000) (s3c1 12225 46 c) := by
    convert (sGlobal21_hz71 hc) using 1 <;>
      norm_num [s3c1] <;> ring

theorem sGlobal21_hz73 {c : ℝ} (hc : B (9 / 20) (91 / 200) c) : B (32428801097325763 / 50000000000000000) (650360745716543903 / 1000000000000000000) (kdot c) := bkdot (sGlobal21_hz38 hc) sGlobal21_hz39.1 sGlobal21_hz47.2

theorem sGlobal21_hz74 : B (17440015882284823 / 25000000000000000) (139520127058278621 / 200000000000000000) (kdot ((3635439885703487 / 6250000000000000))) := by
    constructor
    · apply bkdot_lower (q := (257140995212456921 / 500000000000000000)) (a := (237503905654695147 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (514281990424913841 / 1000000000000000000)) (a := (118751952827347501 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal21_hz75 : B (698872957570919871 / 1000000000000000000) (698872957570920017 / 1000000000000000000) (kdot ((584917080744437443 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (127939357962399723 / 250000000000000000)) (a := (473009252146210049 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (511757431849598891 / 1000000000000000000)) (a := (473009252146209821 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal21_hz76 {c : ℝ} (hc : B (9 / 20) (91 / 200) c) : B (17440015882284823 / 25000000000000000) (698872957570920017 / 1000000000000000000) (kdot (s3c1 12225 46 c)) := bkdot (sGlobal21_hz72 hc) sGlobal21_hz74.1 sGlobal21_hz75.2

theorem sGlobal21_hz77 {c : ℝ} (hc : B (9 / 20) (91 / 200) c) : B (81 / 400) (8281 / 40000) (c^2) := bsq (sGlobal21_hz38 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal21_hz78 {c : ℝ} (hc : B (9 / 20) (91 / 200) c) : B (31719 / 40000) (319 / 400) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (sGlobal21_hz77 hc) (by norm_num) (by norm_num)

theorem sGlobal21_hz79 {c : ℝ} (hc : B (9 / 20) (91 / 200) c) : B (111311429669194349 / 125000000000000000) (178605710994917517 / 200000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (sGlobal21_hz78 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal21_hz80 : B (39119999999999765769 / 1600000000000000) (3912000000000000489 / 160000000000000) ((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (149450625 : ℝ)) sGlobal21_hz10 (by norm_num) (by norm_num)

theorem sGlobal21_hz81 {c : ℝ} (hc : B (9 / 20) (91 / 200) c) : B (577551394016203071 / 1000000000000000000) (116158143391888081 / 200000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (sGlobal21_hz79 hc) (sGlobal21_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal21_hz82 {c : ℝ} (hc : B (9 / 20) (91 / 200) c) : B (7060565791848040267837 / 500000000000000000) (3550083257414579919323 / 250000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) := bmul sGlobal21_hz80 (sGlobal21_hz81 hc) (by norm_num) (by norm_num)

theorem sGlobal21_hz83 {c : ℝ} (hc : B (9 / 20) (91 / 200) c) : B (7060565791848040267837 / 1000000000000000000) (3550083257414579919323 / 500000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) / (2 : ℝ)) := bdiv (sGlobal21_hz82 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal21_hz84 {c : ℝ} (hc : B (9 / 20) (91 / 200) c) : B (7060565791848040267837 / 1000000000000000000) (3550083257414579919323 / 500000000000000000) (s3Cpa 12225 c) := by
    convert (sGlobal21_hz83 hc) using 1 <;>
      norm_num [s3Cpa, mA] <;> ring

theorem sGlobal21_hz85 {c : ℝ} (hc : B (9 / 20) (91 / 200) c) : B (141726114035825093 / 500000000000000000) (11370392707713441 / 40000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (sGlobal21_hz79 hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal21_hz86 {c : ℝ} (hc : B (9 / 20) (91 / 200) c) : B (291859209875931867 / 1000000000000000000) (73978534825256869 / 250000000000000000) (c * (kdot c)) := bmul (sGlobal21_hz38 hc) (sGlobal21_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal21_hz87 {c : ℝ} (hc : B (9 / 20) (91 / 200) c) : B (-1246191122937729 / 100000000000000000) (-3799696091547921 / 500000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (sGlobal21_hz85 hc) (sGlobal21_hz86 hc) (by norm_num) (by norm_num)

theorem sGlobal21_hz88 {c : ℝ} (hc : B (9 / 20) (91 / 200) c) : B (-304693729558274778587 / 1000000000000000000) (-185805138876692224391 / 1000000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) := bmul sGlobal21_hz80 (sGlobal21_hz87 hc) (by norm_num) (by norm_num)

theorem sGlobal21_hz89 {c : ℝ} (hc : B (9 / 20) (91 / 200) c) : B (-76173432389568694647 / 500000000000000000) (-18580513887669222439 / 200000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) / (2 : ℝ)) := bdiv (sGlobal21_hz88 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal21_hz90 {c : ℝ} (hc : B (9 / 20) (91 / 200) c) : B (-76173432389568694647 / 500000000000000000) (-18580513887669222439 / 200000000000000000) (s3Cpp 12225 c) := by
    convert (sGlobal21_hz89 hc) using 1 <;>
      norm_num [s3Cpp, mA] <;> ring

theorem sGlobal21_hz91 {c : ℝ} (hc : B (9 / 20) (91 / 200) c) : B (3587855450890888988119 / 500000000000000000) (901913953095362281359 / 125000000000000000) ((s3Cpa 12225 c) + (s3r1 12225 46)) := badd (sGlobal21_hz84 hc) sGlobal21_hz33 (by norm_num) (by norm_num)

theorem sGlobal21_hz92 {c : ℝ} (hc : B (9 / 20) (91 / 200) c) : B (64971464467787576747 / 1000000000000000000) (16332505910177265343 / 250000000000000000) (((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) := bdiv (sGlobal21_hz91 hc) sGlobal21_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal21_hz93 {c : ℝ} (hc : B (9 / 20) (91 / 200) c) : B (65094147493281637159 / 1000000000000000000) (13090541333240624359 / 200000000000000000) ((((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) + (s3e0 12225 46)) := badd (sGlobal21_hz92 hc) sGlobal21_hz16 (by norm_num) (by norm_num)

theorem sGlobal21_hz94 {c : ℝ} (hc : B (9 / 20) (91 / 200) c) : B (65094147493281637159 / 1000000000000000000) (13090541333240624359 / 200000000000000000) (s3Lam 12225 46 c) := by
    convert (sGlobal21_hz93 hc) using 1 <;>
      norm_num [s3Lam] <;> ring

theorem sGlobal21_hz95 {c : ℝ} (hc : B (9 / 20) (91 / 200) c) : B (-37791729078322791847 / 500000000000000000) (-16139162815853837377 / 1000000000000000000) ((s3Cpp 12225 c) + (s3rpp 12225 46)) := badd (sGlobal21_hz90 hc) sGlobal21_hz37 (by norm_num) (by norm_num)

theorem sGlobal21_hz96 {c : ℝ} (hc : B (9 / 20) (91 / 200) c) : B (-52823234945372777493 / 1000000000000000000) (-252174418997716209 / 31250000000000000) (if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) := bweaken (bfirst (sGlobal21_hz95 hc) (sGlobal21_hz76 hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem sGlobal21_hz97 {c : ℝ} (hc : B (9 / 20) (91 / 200) c) : B (4237248037877104046583 / 1000000000000000000) (535507101241503822261 / 125000000000000000) ((s3Lam 12225 46 c)^2) := bsq (sGlobal21_hz94 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal21_hz98 {c : ℝ} (hc : B (9 / 20) (91 / 200) c) : B (67668086592326567 / 200000000000000000) (5345749864790543 / 15625000000000000) ((s3c1 12225 46 c)^2) := bsq (sGlobal21_hz72 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal21_hz99 {c : ℝ} (hc : B (9 / 20) (91 / 200) c) : B (10279250135209457 / 15625000000000000) (132331913407673433 / 200000000000000000) ((1 : ℝ) - ((s3c1 12225 46 c)^2)) := bsub (bpoint (1 : ℝ)) (sGlobal21_hz98 hc) (by norm_num) (by norm_num)

theorem sGlobal21_hz100 {c : ℝ} (hc : B (9 / 20) (91 / 200) c) : B (202773273734084167 / 250000000000000000) (813424592103267533 / 1000000000000000000) (√((1 : ℝ) - ((s3c1 12225 46 c)^2))) := bsqrt (sGlobal21_hz99 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal21_hz101 {c : ℝ} (hc : B (9 / 20) (91 / 200) c) : B (1274062054214702001 / 500000000000000000) (79857772587528107 / 31250000000000000) (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))) := bmul pi_mem (sGlobal21_hz100 hc) (by norm_num) (by norm_num)

theorem sGlobal21_hz102 {c : ℝ} (hc : B (9 / 20) (91 / 200) c) : B (1658122896409703177729 / 1000000000000000000) (1681259086148911863793 / 1000000000000000000) (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2))))) := bdiv (sGlobal21_hz97 hc) (sGlobal21_hz101 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal21_hz103 {c : ℝ} (hc : B (9 / 20) (91 / 200) c) : B (401324915366082600059 / 250000000000000000) (334637900948196989021 / 200000000000000000) ((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) := badd (sGlobal21_hz96 hc) (sGlobal21_hz102 hc) (by norm_num) (by norm_num)

theorem sGlobal21_hz104 : B (3762781186094069 / 250000000000000000) (376278118609407 / 25000000000000000) ((s3e0 12225 46)^2) := bsq sGlobal21_hz16 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal21_hz105 {c : ℝ} (hc : B (9 / 20) (91 / 200) c) : B (25083042384204293383 / 15625000000000000) (334640911173145864277 / 200000000000000000) (((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) := badd (sGlobal21_hz103 hc) sGlobal21_hz104 (by norm_num) (by norm_num)

theorem sGlobal21_hz106 {c : ℝ} (hc : B (9 / 20) (91 / 200) c) : B (1643811786040322046643 / 1000000000000000000) (1711701629319853591401 / 1000000000000000000) ((((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) + (s3rs 12225 46 maskSlack)) := badd (sGlobal21_hz105 hc) sGlobal21_hz29 (by norm_num) (by norm_num)

theorem sGlobal21_hz107 {c : ℝ} (hc : B (9 / 20) (91 / 200) c) : B (1643811786040322046643 / 1000000000000000000) (1711701629319853591401 / 1000000000000000000) (s3U 12225 46 maskSlack c) := by
    convert (sGlobal21_hz106 hc) using 1 <;>
      norm_num [s3U] <;> ring

theorem sGlobal21_hz108 {c : ℝ} (hc : B (9 / 20) (91 / 200) c) : B (-14319391962601854007 / 62500000000000000) (-33933195212167583559 / 200000000000000000) ((s3Cpp 12225 c) - (s3rpp 12225 46)) := bsub (sGlobal21_hz90 hc) sGlobal21_hz37 (by norm_num) (by norm_num)

theorem sGlobal21_hz109 {c : ℝ} (hc : B (9 / 20) (91 / 200) c) : B (-14319391962601854007 / 62500000000000000) (-33933195212167583559 / 200000000000000000) (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ)) := bweaken (bmin (sGlobal21_hz108 hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem sGlobal21_hz110 {c : ℝ} (hc : B (9 / 20) (91 / 200) c) : B (-160118972984333098021 / 1000000000000000000) (-59179546343687397137 / 500000000000000000) ((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) := bmul (sGlobal21_hz76 hc) (sGlobal21_hz109 hc) (by norm_num) (by norm_num)

theorem sGlobal21_hz111 {c : ℝ} (hc : B (9 / 20) (91 / 200) c) : B (-160134024109077474301 / 1000000000000000000) (-2367482876242383411 / 20000000000000000) (((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) := bsub (sGlobal21_hz110 hc) sGlobal21_hz104 (by norm_num) (by norm_num)

theorem sGlobal21_hz112 {c : ℝ} (hc : B (9 / 20) (91 / 200) c) : B (-198631097563201744317 / 1000000000000000000) (-156871217263366440681 / 1000000000000000000) ((((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) - (s3rs 12225 46 maskSlack)) := bsub (sGlobal21_hz111 hc) sGlobal21_hz29 (by norm_num) (by norm_num)

theorem sGlobal21_hz113 {c : ℝ} (hc : B (9 / 20) (91 / 200) c) : B (-198631097563201744317 / 1000000000000000000) (-156871217263366440681 / 1000000000000000000) (s3L 12225 46 maskSlack c) := by
    convert (sGlobal21_hz112 hc) using 1 <;>
      norm_num [s3L] <;> ring

theorem sGlobal21_hz114 {c : ℝ} (hc : B (9 / 20) (91 / 200) c) : B 0 (1711701629319853591401 / 1000000000000000000) |(s3U 12225 46 maskSlack c)| := bweaken (babs (sGlobal21_hz107 hc)) (by norm_num) (by norm_num)

theorem sGlobal21_hz115 {c : ℝ} (hc : B (9 / 20) (91 / 200) c) : B 0 (198631097563201744317 / 1000000000000000000) |(s3L 12225 46 maskSlack c)| := bweaken (babs (sGlobal21_hz113 hc)) (by norm_num) (by norm_num)

theorem sGlobal21_hz116 {c : ℝ} (hc : B (9 / 20) (91 / 200) c) : B 0 (1711701629319853591401 / 1000000000000000000) (max |(s3U 12225 46 maskSlack c)| |(s3L 12225 46 maskSlack c)|) := bweaken (bmax (sGlobal21_hz114 hc) (sGlobal21_hz115 hc)) (by norm_num) (by norm_num)

theorem sGlobal21_hz117 {c : ℝ} (hc : B (9 / 20) (91 / 200) c) : B 0 (1711701629319853591401 / 1000000000000000000) (s3nks 12225 46 maskSlack c) := by
    convert (sGlobal21_hz116 hc) using 1 <;>
      norm_num [s3nks] <;> ring

theorem sGlobal21 {c : ℝ} (hc : B (9 / 20) (91 / 200) c) :
    0 < s3am 12225 46 ∧ 0 ≤ s3dm 12225 46 c ∧
    s3dm 12225 46 c ^ 2 ≤ 2 * s3ap 12225 46 ^ 2 ∧ s3c1 12225 46 c < 1 ∧
    0 ≤ s3Cpa 12225 c - s3r1 12225 46 ∧
    s3e0 12225 46 ≤ (s3Cpa 12225 c - s3r1 12225 46) / s3ap 12225 46 ∧
    s3nks 12225 46 maskSlack c ≤ 12225 * (140017 / 1000000) := by

  refine ⟨lt_of_lt_of_le (by norm_num) sGlobal21_hz14.1,
    le_trans (by norm_num) (sGlobal21_hz64 hc).1, ?_,
    lt_of_le_of_lt (sGlobal21_hz72 hc).2 (by norm_num), ?_, ?_,
    le_trans (sGlobal21_hz117 hc).2 (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (sGlobal21_hz64 hc).1) (sGlobal21_hz64 hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) sGlobal21_hz9.1 2
    nlinarith only [h1, h2]
  · linarith only [(sGlobal21_hz84 hc).1, sGlobal21_hz33.2]
  · have hap : 0 < s3ap 12225 46 := lt_of_lt_of_le (by norm_num) sGlobal21_hz9.1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul sGlobal21_hz16.2 sGlobal21_hz9.2 (le_trans (by norm_num) sGlobal21_hz9.1) (by norm_num)
    linarith only [h, (sGlobal21_hz84 hc).1, sGlobal21_hz33.2]

end BstLean.Part255
