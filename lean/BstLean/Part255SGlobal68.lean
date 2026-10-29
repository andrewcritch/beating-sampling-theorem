import BstLean.Part255SGlobal64
import BstLean.Part255Numeric10
namespace BstLean.Part255
open Real BstLean.Part130 BstLean.Part182 BstLean.Part197 BstLean.Part246
theorem sGlobal68_hz0 : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal68_hz1 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) ((√(23 : ℝ)) / (12225 : ℝ)) := bdiv sGlobal68_hz0 (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal68_hz2 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) maskSlack := by
    convert sGlobal68_hz1 using 1 <;>
      norm_num [maskSlack] <;> ring

theorem sGlobal68_hz3 : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal68_hz4 : B (6395294793910793 / 500000000000000000) (12790589587821587 / 1000000000000000000) (√((2 / 12225) : ℝ)) := bsqrt (bpoint ((2 / 12225) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal68_hz5 : B (7230130686979 / 62500000000000000) (23136418198333 / 200000000000000000) (√((2 / 149450625) : ℝ)) := bsqrt (bpoint ((2 / 149450625) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal68_hz6 : B (2211334438749598093 / 20000000000000000) (110566721937479904651 / 1000000000000000000) (√(12225 : ℝ)) := bsqrt (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal68_hz7 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))) := bmul sGlobal68_hz3 sGlobal68_hz4 (by norm_num) (by norm_num)

theorem sGlobal68_hz8 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) ((√(12225 : ℝ)) + ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := badd sGlobal68_hz6 sGlobal68_hz7 (by norm_num) (by norm_num)

theorem sGlobal68_hz9 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) (s3ap 12225 46) := by
    convert sGlobal68_hz8 using 1 <;>
      norm_num [s3ap, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal68_hz10 : B (163599182004089 / 1000000000000000000) (16359918200409 / 100000000000000000) ((2 : ℝ) / (12225 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal68_hz11 : B (1222499983640081799591 / 100000000000000000) (12224999836400817995911 / 1000000000000000000) ((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ))) := bsub (bpoint (12225 : ℝ)) sGlobal68_hz10 (by norm_num) (by norm_num)

theorem sGlobal68_hz12 : B (110566721197658827907 / 1000000000000000000) (27641680299414706977 / 250000000000000000) (√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) := bsqrt sGlobal68_hz11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal68_hz13 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) ((√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) - ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bsub sGlobal68_hz12 sGlobal68_hz7 (by norm_num) (by norm_num)

theorem sGlobal68_hz14 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) (s3am 12225 46) := by
    convert sGlobal68_hz13 using 1 <;>
      norm_num [s3am, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal68_hz15 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√((2 / 12225) : ℝ)) * (√(92 : ℝ))) := bmul sGlobal68_hz4 sGlobal68_hz3 (by norm_num) (by norm_num)

theorem sGlobal68_hz16 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) (s3e0 12225 46) := by
    convert sGlobal68_hz15 using 1 <;>
      norm_num [s3e0, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal68_hz17 : B (250196148528560847 / 500000000000000000) (100078459411424339 / 200000000000000000) (((1 / 2) : ℝ) + maskSlack) := badd (bpoint ((1 / 2) : ℝ)) sGlobal68_hz2 (by norm_num) (by norm_num)

theorem sGlobal68_hz18 : B (59827153232297998295487 / 800000000000000) (23930861292919199366019 / 320000000000000) ((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack)) := bmul (bpoint (149450625 : ℝ)) sGlobal68_hz17 (by norm_num) (by norm_num)

theorem sGlobal68_hz19 : B (1729554180017180009583 / 200000000000000000) (8647770900085900056557 / 1000000000000000000) (√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) := bsqrt sGlobal68_hz18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal68_hz20 : B (4328681281566262743499 / 500000000000000000) (8657362563132525495641 / 1000000000000000000) ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))) := badd sGlobal68_hz19 sGlobal68_hz3 (by norm_num) (by norm_num)

theorem sGlobal68_hz21 : B (110732771457999278473 / 1000000000000000000) (55366385728999643621 / 500000000000000000) ((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ)))) := bmul sGlobal68_hz4 sGlobal68_hz20 (by norm_num) (by norm_num)

theorem sGlobal68_hz22 : B (209099159 / 15625000000000000) (13382346177 / 1000000000000000000) ((2 : ℝ) / (149450625 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (149450625 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal68_hz23 : B (2452349334953899930479 / 200000000000000000) (12261746674769501594427 / 1000000000000000000) (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2) := bsq sGlobal68_hz21 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal68_hz24 : B (82045469362091 / 500000000000000000) (32818187747289 / 200000000000000000) (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2)) := bmul sGlobal68_hz22 sGlobal68_hz23 (by norm_num) (by norm_num)

theorem sGlobal68_hz25 : B (82045469362091 / 250000000000000000) (32818187747289 / 100000000000000000) ((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) := bmul (bpoint (2 : ℝ)) sGlobal68_hz24 (by norm_num) (by norm_num)

theorem sGlobal68_hz26 : B (117258080744995992792057 / 1000000000000000000) (58629040372497996396029 / 500000000000000000) (√(13749457500 : ℝ)) := bsqrt (bpoint (13749457500 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal68_hz27 : B (117304080744995992792057 / 1000000000000000000) (58652040372497996396029 / 500000000000000000) ((√(13749457500 : ℝ)) + (46 : ℝ)) := badd sGlobal68_hz26 (bpoint (46 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal68_hz28 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal68_hz25 sGlobal68_hz27 (by norm_num) (by norm_num)

theorem sGlobal68_hz29 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (s3rs 12225 46 maskSlack) := by
    convert sGlobal68_hz28 using 1 <;>
      norm_num [s3rs, s3pp, s3K, mA, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal68_hz30 : B (490797546012267 / 1000000000000000000) (49079754601227 / 100000000000000000) ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (3 : ℝ)) sGlobal68_hz10 (by norm_num) (by norm_num)

theorem sGlobal68_hz31 : B (490797546012267 / 500000000000000000) (49079754601227 / 50000000000000000) ((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal68_hz30 (by norm_num) (by norm_num)

theorem sGlobal68_hz32 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal68_hz31 sGlobal68_hz27 (by norm_num) (by norm_num)

theorem sGlobal68_hz33 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (s3r1 12225 46) := by
    convert sGlobal68_hz32 using 1 <;>
      norm_num [s3r1, mA] <;> ring

theorem sGlobal68_hz34 : B (163599182004089 / 500000000000000000) (16359918200409 / 50000000000000000) ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (2 : ℝ)) sGlobal68_hz10 (by norm_num) (by norm_num)

theorem sGlobal68_hz35 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal68_hz34 (by norm_num) (by norm_num)

theorem sGlobal68_hz36 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal68_hz35 sGlobal68_hz27 (by norm_num) (by norm_num)

theorem sGlobal68_hz37 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (s3rpp 12225 46) := by
    convert sGlobal68_hz36 using 1 <;>
      norm_num [s3rpp, mA] <;> ring

theorem sGlobal68_hz38 {c : ℝ} (hc : B (137 / 200) (69 / 100) c) : B (137 / 200) (69 / 100) c := hc

theorem sGlobal68_hz39 : B (740197817494345467 / 1000000000000000000) (74019781749434547 / 100000000000000000) (kdot ((137 / 200))) := by
    constructor
    · apply bkdot_lower (q := (432369772507331441 / 1000000000000000000)) (a := (40809631397317949 / 100000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (5404622156341643 / 12500000000000000)) (a := (12753009811661859 / 31250000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal68_hz40 : B (18769 / 40000) (18769 / 40000) (((137 / 200) : ℝ)^2) := bsq (bpoint ((137 / 200) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal68_hz41 : B (21231 / 40000) (21231 / 40000) ((1 : ℝ) - (((137 / 200) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal68_hz40 (by norm_num) (by norm_num)

theorem sGlobal68_hz42 : B (728543066674853477 / 1000000000000000000) (364271533337426739 / 500000000000000000) (√((1 : ℝ) - (((137 / 200) : ℝ)^2))) := bsqrt sGlobal68_hz41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal68_hz43 : B (57975615158315607 / 250000000000000000) (23190246063326243 / 100000000000000000) ((√((1 : ℝ) - (((137 / 200) : ℝ)^2))) / Real.pi) := bdiv sGlobal68_hz42 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal68_hz44 : B (126758876245906661 / 250000000000000000) (507035504983626647 / 1000000000000000000) (((137 / 200) : ℝ) * (kdot ((137 / 200)))) := bmul (bpoint ((137 / 200) : ℝ)) sGlobal68_hz39 (by norm_num) (by norm_num)

theorem sGlobal68_hz45 : B (46183622851055567 / 62500000000000000) (738937965616889077 / 1000000000000000000) (((√((1 : ℝ) - (((137 / 200) : ℝ)^2))) / Real.pi) + (((137 / 200) : ℝ) * (kdot ((137 / 200))))) := badd sGlobal68_hz43 sGlobal68_hz44 (by norm_num) (by norm_num)

theorem sGlobal68_hz46 : B (46183622851055567 / 62500000000000000) (738937965616889077 / 1000000000000000000) (kappa ((137 / 200))) := by rw [kappa_eq]; exact sGlobal68_hz45

theorem sGlobal68_hz47 : B (742389493710301703 / 1000000000000000000) (148477898742060341 / 200000000000000000) (kdot ((69 / 100))) := by
    constructor
    · apply bkdot_lower (q := (107072391592885037 / 250000000000000000)) (a := (25290852313976981 / 62500000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (428289566371540147 / 1000000000000000000)) (a := (202326818511815847 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal68_hz48 : B (4761 / 10000) (4761 / 10000) (((69 / 100) : ℝ)^2) := bsq (bpoint ((69 / 100) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal68_hz49 : B (5239 / 10000) (5239 / 10000) ((1 : ℝ) - (((69 / 100) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal68_hz48 (by norm_num) (by norm_num)

theorem sGlobal68_hz50 : B (723809367167902849 / 1000000000000000000) (14476187343358057 / 20000000000000000) (√((1 : ℝ) - (((69 / 100) : ℝ)^2))) := bsqrt sGlobal68_hz49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal68_hz51 : B (57598919320494177 / 250000000000000000) (230395677281976709 / 1000000000000000000) ((√((1 : ℝ) - (((69 / 100) : ℝ)^2))) / Real.pi) := bdiv sGlobal68_hz50 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal68_hz52 : B (20489950026404327 / 40000000000000000) (512248750660108177 / 1000000000000000000) (((69 / 100) : ℝ) * (kdot ((69 / 100)))) := bmul (bpoint ((69 / 100) : ℝ)) sGlobal68_hz47 (by norm_num) (by norm_num)

theorem sGlobal68_hz53 : B (742644427942084883 / 1000000000000000000) (371322213971042443 / 500000000000000000) (((√((1 : ℝ) - (((69 / 100) : ℝ)^2))) / Real.pi) + (((69 / 100) : ℝ) * (kdot ((69 / 100))))) := badd sGlobal68_hz51 sGlobal68_hz52 (by norm_num) (by norm_num)

theorem sGlobal68_hz54 : B (742644427942084883 / 1000000000000000000) (371322213971042443 / 500000000000000000) (kappa ((69 / 100))) := by rw [kappa_eq]; exact sGlobal68_hz53

theorem sGlobal68_hz55 {c : ℝ} (hc : B (137 / 200) (69 / 100) c) : B (46183622851055567 / 62500000000000000) (371322213971042443 / 500000000000000000) (kappa c) := bkappa (sGlobal68_hz38 hc) (by norm_num) (by norm_num) sGlobal68_hz46.1 sGlobal68_hz54.2

theorem sGlobal68_hz56 : B 24450 24450 ((2 : ℝ) * (12225 : ℝ)) := bmul (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal68_hz57 {c : ℝ} (hc : B (137 / 200) (69 / 100) c) : B (128677786028957557 / 500000000000000000) (16316377148944433 / 62500000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (sGlobal68_hz55 hc) (by norm_num) (by norm_num)

theorem sGlobal68_hz58 {c : ℝ} (hc : B (137 / 200) (69 / 100) c) : B (62923437368160245373 / 10000000000000000) (7978708425833827737 / 1250000000000000) (((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) := bmul sGlobal68_hz56 (sGlobal68_hz57 hc) (by norm_num) (by norm_num)

theorem sGlobal68_hz59 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (4 : ℝ)) sGlobal68_hz10 (by norm_num) (by norm_num)

theorem sGlobal68_hz60 {c : ℝ} (hc : B (137 / 200) (69 / 100) c) : B (314617154120964826047 / 50000000000000000) (1595741521567583543311 / 250000000000000000) ((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bsub (sGlobal68_hz58 hc) sGlobal68_hz59 (by norm_num) (by norm_num)

theorem sGlobal68_hz61 {c : ℝ} (hc : B (137 / 200) (69 / 100) c) : B (1983107265508363853 / 25000000000000000) (39946733553165314387 / 500000000000000000) (√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) := bsqrt (sGlobal68_hz60 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal68_hz62 : B (30670756373515103 / 125000000000000000) (122683025494060423 / 500000000000000000) ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal68_hz7 (by norm_num) (by norm_num)

theorem sGlobal68_hz63 {c : ℝ} (hc : B (137 / 200) (69 / 100) c) : B (39539462284673216637 / 500000000000000000) (1592962021106850159 / 20000000000000000) ((√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) - ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))))) := bsub (sGlobal68_hz61 hc) sGlobal68_hz62 (by norm_num) (by norm_num)

theorem sGlobal68_hz64 {c : ℝ} (hc : B (137 / 200) (69 / 100) c) : B (39539462284673216637 / 500000000000000000) (1592962021106850159 / 20000000000000000) (s3dm 12225 46 c) := by
    convert (sGlobal68_hz63 hc) using 1 <;>
      norm_num [s3dm, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal68_hz65 : B (6126072185528622723889 / 500000000000000000) (2450428874211449090087 / 200000000000000000) ((s3ap 12225 46)^2) := bsq sGlobal68_hz9 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal68_hz66 : B (6126072185528622723889 / 250000000000000000) (2450428874211449090087 / 100000000000000000) ((2 : ℝ) * ((s3ap 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal68_hz65 (by norm_num) (by norm_num)

theorem sGlobal68_hz67 {c : ℝ} (hc : B (137 / 200) (69 / 100) c) : B (3126738155522191488623 / 500000000000000000) (6343820001722052328653 / 1000000000000000000) ((s3dm 12225 46 c)^2) := bsq (sGlobal68_hz64 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal68_hz68 {c : ℝ} (hc : B (137 / 200) (69 / 100) c) : B (18160468740392438566903 / 1000000000000000000) (2281351553883763490453 / 125000000000000000) (((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) := bsub sGlobal68_hz66 (sGlobal68_hz67 hc) (by norm_num) (by norm_num)

theorem sGlobal68_hz69 : B (1524735695971823534271 / 125000000000000000) (609894278388729413841 / 50000000000000000) ((s3am 12225 46)^2) := bsq sGlobal68_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal68_hz70 : B (1524735695971823534271 / 62500000000000000) (609894278388729413841 / 25000000000000000) ((2 : ℝ) * ((s3am 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal68_hz69 (by norm_num) (by norm_num)

theorem sGlobal68_hz71 {c : ℝ} (hc : B (137 / 200) (69 / 100) c) : B (744410522606078127 / 1000000000000000000) (748113774705620159 / 1000000000000000000) ((((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) / ((2 : ℝ) * ((s3am 12225 46)^2))) := bdiv (sGlobal68_hz68 hc) sGlobal68_hz70 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal68_hz72 {c : ℝ} (hc : B (137 / 200) (69 / 100) c) : B (744410522606078127 / 1000000000000000000) (748113774705620159 / 1000000000000000000) (s3c1 12225 46 c) := by
    convert (sGlobal68_hz71 hc) using 1 <;>
      norm_num [s3c1] <;> ring

theorem sGlobal68_hz73 {c : ℝ} (hc : B (137 / 200) (69 / 100) c) : B (740197817494345467 / 1000000000000000000) (148477898742060341 / 200000000000000000) (kdot c) := bkdot (sGlobal68_hz38 hc) sGlobal68_hz39.1 sGlobal68_hz47.2

theorem sGlobal68_hz74 : B (153453880271104043 / 200000000000000000) (767269401355520217 / 1000000000000000000) (kdot ((744410522606078127 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (191389073672123863 / 500000000000000000)) (a := (22848273092720387 / 62500000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (15311125893769909 / 40000000000000000)) (a := (36557236948352619 / 100000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal68_hz75 : B (153808055940516647 / 200000000000000000) (769040279702583237 / 1000000000000000000) (kdot ((748113774705620159 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (94898067880556419 / 250000000000000000)) (a := (181395340140379491 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (15183690860889027 / 40000000000000000)) (a := (18139534014037949 / 50000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal68_hz76 {c : ℝ} (hc : B (137 / 200) (69 / 100) c) : B (153453880271104043 / 200000000000000000) (769040279702583237 / 1000000000000000000) (kdot (s3c1 12225 46 c)) := bkdot (sGlobal68_hz72 hc) sGlobal68_hz74.1 sGlobal68_hz75.2

theorem sGlobal68_hz77 {c : ℝ} (hc : B (137 / 200) (69 / 100) c) : B (18769 / 40000) (4761 / 10000) (c^2) := bsq (sGlobal68_hz38 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal68_hz78 {c : ℝ} (hc : B (137 / 200) (69 / 100) c) : B (5239 / 10000) (21231 / 40000) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (sGlobal68_hz77 hc) (by norm_num) (by norm_num)

theorem sGlobal68_hz79 {c : ℝ} (hc : B (137 / 200) (69 / 100) c) : B (723809367167902849 / 1000000000000000000) (364271533337426739 / 500000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (sGlobal68_hz78 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal68_hz80 : B (39119999999999765769 / 1600000000000000) (3912000000000000489 / 160000000000000) ((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (149450625 : ℝ)) sGlobal68_hz10 (by norm_num) (by norm_num)

theorem sGlobal68_hz81 {c : ℝ} (hc : B (137 / 200) (69 / 100) c) : B (6697026423245563 / 12500000000000000) (135215679603723763 / 250000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (sGlobal68_hz79 hc) (sGlobal68_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal68_hz82 {c : ℝ} (hc : B (137 / 200) (69 / 100) c) : B (163742296048353034943 / 12500000000000000) (3306023366311046418603 / 250000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) := bmul sGlobal68_hz80 (sGlobal68_hz81 hc) (by norm_num) (by norm_num)

theorem sGlobal68_hz83 {c : ℝ} (hc : B (137 / 200) (69 / 100) c) : B (163742296048353034943 / 25000000000000000) (3306023366311046418603 / 500000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) / (2 : ℝ)) := bdiv (sGlobal68_hz82 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal68_hz84 {c : ℝ} (hc : B (137 / 200) (69 / 100) c) : B (163742296048353034943 / 25000000000000000) (3306023366311046418603 / 500000000000000000) (s3Cpa 12225 c) := by
    convert (sGlobal68_hz83 hc) using 1 <;>
      norm_num [s3Cpa, mA] <;> ring

theorem sGlobal68_hz85 {c : ℝ} (hc : B (137 / 200) (69 / 100) c) : B (57598919320494177 / 250000000000000000) (23190246063326243 / 100000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (sGlobal68_hz79 hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal68_hz86 {c : ℝ} (hc : B (137 / 200) (69 / 100) c) : B (126758876245906661 / 250000000000000000) (512248750660108177 / 1000000000000000000) (c * (kdot c)) := bmul (sGlobal68_hz38 hc) (sGlobal68_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal68_hz87 {c : ℝ} (hc : B (137 / 200) (69 / 100) c) : B (-281853073378131469 / 1000000000000000000) (-137566522175182107 / 500000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (sGlobal68_hz85 hc) (sGlobal68_hz86 hc) (by norm_num) (by norm_num)

theorem sGlobal68_hz88 {c : ℝ} (hc : B (137 / 200) (69 / 100) c) : B (-53838340969494650613 / 7812500000000000) (-6727002934366364754369 / 1000000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) := bmul sGlobal68_hz80 (sGlobal68_hz87 hc) (by norm_num) (by norm_num)

theorem sGlobal68_hz89 {c : ℝ} (hc : B (137 / 200) (69 / 100) c) : B (-53838340969494650613 / 15625000000000000) (-105109420849474449287 / 31250000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) / (2 : ℝ)) := bdiv (sGlobal68_hz88 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal68_hz90 {c : ℝ} (hc : B (137 / 200) (69 / 100) c) : B (-53838340969494650613 / 15625000000000000) (-105109420849474449287 / 31250000000000000) (s3Cpp 12225 c) := by
    convert (sGlobal68_hz89 hc) using 1 <;>
      norm_num [s3Cpp, mA] <;> ring

theorem sGlobal68_hz91 {c : ℝ} (hc : B (137 / 200) (69 / 100) c) : B (6664836951867859106121 / 1000000000000000000) (840898980319478906179 / 125000000000000000) ((s3Cpa 12225 c) + (s3r1 12225 46)) := badd (sGlobal68_hz84 hc) sGlobal68_hz33 (by norm_num) (by norm_num)

theorem sGlobal68_hz92 {c : ℝ} (hc : B (137 / 200) (69 / 100) c) : B (6034582818747023381 / 100000000000000000) (30455205884763124877 / 500000000000000000) (((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) := bdiv (sGlobal68_hz91 hc) sGlobal68_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal68_hz93 {c : ℝ} (hc : B (137 / 200) (69 / 100) c) : B (30234255606482147111 / 500000000000000000) (61033094795020310177 / 1000000000000000000) ((((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) + (s3e0 12225 46)) := badd (sGlobal68_hz92 hc) sGlobal68_hz16 (by norm_num) (by norm_num)

theorem sGlobal68_hz94 {c : ℝ} (hc : B (137 / 200) (69 / 100) c) : B (30234255606482147111 / 500000000000000000) (61033094795020310177 / 1000000000000000000) (s3Lam 12225 46 c) := by
    convert (sGlobal68_hz93 hc) using 1 <;>
      norm_num [s3Lam] <;> ring

theorem sGlobal68_hz95 {c : ℝ} (hc : B (137 / 200) (69 / 100) c) : B (-105277825482036432301 / 31250000000000000) (-1643369030280345051183 / 500000000000000000) ((s3Cpp 12225 c) + (s3rpp 12225 46)) := badd (sGlobal68_hz90 hc) sGlobal68_hz37 (by norm_num) (by norm_num)

theorem sGlobal68_hz96 {c : ℝ} (hc : B (137 / 200) (69 / 100) c) : B (-1295406213682960684743 / 500000000000000000) (-1643369030280345051183 / 1000000000000000000) (if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) := bweaken (bfirst (sGlobal68_hz95 hc) (sGlobal68_hz76 hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem sGlobal68_hz97 {c : ℝ} (hc : B (137 / 200) (69 / 100) c) : B (1828220424156194290447 / 500000000000000000) (1862519330128967638971 / 500000000000000000) ((s3Lam 12225 46 c)^2) := bsq (sGlobal68_hz94 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal68_hz98 {c : ℝ} (hc : B (137 / 200) (69 / 100) c) : B (277073513083327177 / 500000000000000000) (559674219904291397 / 1000000000000000000) ((s3c1 12225 46 c)^2) := bsq (sGlobal68_hz72 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal68_hz99 {c : ℝ} (hc : B (137 / 200) (69 / 100) c) : B (440325780095708603 / 1000000000000000000) (222926486916672823 / 500000000000000000) ((1 : ℝ) - ((s3c1 12225 46 c)^2)) := bsub (bpoint (1 : ℝ)) (sGlobal68_hz98 hc) (by norm_num) (by norm_num)

theorem sGlobal68_hz100 {c : ℝ} (hc : B (137 / 200) (69 / 100) c) : B (663570478619798609 / 1000000000000000000) (667722228050965551 / 1000000000000000000) (√((1 : ℝ) - ((s3c1 12225 46 c)^2))) := bsqrt (sGlobal68_hz99 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal68_hz101 {c : ℝ} (hc : B (137 / 200) (69 / 100) c) : B (2084668140771022271 / 1000000000000000000) (104885562314176097 / 50000000000000000) (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))) := bmul pi_mem (sGlobal68_hz100 hc) (by norm_num) (by norm_num)

theorem sGlobal68_hz102 {c : ℝ} (hc : B (137 / 200) (69 / 100) c) : B (217882755240410257663 / 125000000000000000) (55839802919426180599 / 31250000000000000) (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2))))) := bdiv (sGlobal68_hz97 hc) (sGlobal68_hz101 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal68_hz103 {c : ℝ} (hc : B (137 / 200) (69 / 100) c) : B (-423875192721319654091 / 500000000000000000) (28700932628258545597 / 200000000000000000) ((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) := badd (sGlobal68_hz96 hc) (sGlobal68_hz102 hc) (by norm_num) (by norm_num)

theorem sGlobal68_hz104 : B (3762781186094069 / 250000000000000000) (376278118609407 / 25000000000000000) ((s3e0 12225 46)^2) := bsq sGlobal68_hz16 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal68_hz105 {c : ℝ} (hc : B (137 / 200) (69 / 100) c) : B (-423867667158947465953 / 500000000000000000) (28703942853207420853 / 200000000000000000) (((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) := badd (sGlobal68_hz103 hc) sGlobal68_hz104 (by norm_num) (by norm_num)

theorem sGlobal68_hz106 {c : ℝ} (hc : B (137 / 200) (69 / 100) c) : B (-32369530434665906471 / 40000000000000000) (182016787720161374281 / 1000000000000000000) ((((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) + (s3rs 12225 46 maskSlack)) := badd (sGlobal68_hz105 hc) sGlobal68_hz29 (by norm_num) (by norm_num)

theorem sGlobal68_hz107 {c : ℝ} (hc : B (137 / 200) (69 / 100) c) : B (-32369530434665906471 / 40000000000000000) (182016787720161374281 / 1000000000000000000) (s3U 12225 46 maskSlack c) := by
    convert (sGlobal68_hz106 hc) using 1 <;>
      norm_num [s3U] <;> ring

theorem sGlobal68_hz108 {c : ℝ} (hc : B (137 / 200) (69 / 100) c) : B (-70448344573402998281 / 20000000000000000) (-26877069326606829553 / 7812500000000000) ((s3Cpp 12225 c) - (s3rpp 12225 46)) := bsub (sGlobal68_hz90 hc) sGlobal68_hz37 (by norm_num) (by norm_num)

theorem sGlobal68_hz109 {c : ℝ} (hc : B (137 / 200) (69 / 100) c) : B (-70448344573402998281 / 20000000000000000) (-26877069326606829553 / 7812500000000000) (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ)) := bweaken (bmin (sGlobal68_hz108 hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem sGlobal68_hz110 {c : ℝ} (hc : B (137 / 200) (69 / 100) c) : B (-2708880730765690187457 / 1000000000000000000) (-1319804985114651964109 / 500000000000000000) ((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) := bmul (sGlobal68_hz76 hc) (sGlobal68_hz109 hc) (by norm_num) (by norm_num)

theorem sGlobal68_hz111 {c : ℝ} (hc : B (137 / 200) (69 / 100) c) : B (-2708895781890434563737 / 1000000000000000000) (-1319812510677024152247 / 500000000000000000) (((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) := bsub (sGlobal68_hz110 hc) sGlobal68_hz104 (by norm_num) (by norm_num)

theorem sGlobal68_hz112 {c : ℝ} (hc : B (137 / 200) (69 / 100) c) : B (-2747392855344558833753 / 1000000000000000000) (-21424976758442364597 / 8000000000000000) ((((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) - (s3rs 12225 46 maskSlack)) := bsub (sGlobal68_hz111 hc) sGlobal68_hz29 (by norm_num) (by norm_num)

theorem sGlobal68_hz113 {c : ℝ} (hc : B (137 / 200) (69 / 100) c) : B (-2747392855344558833753 / 1000000000000000000) (-21424976758442364597 / 8000000000000000) (s3L 12225 46 maskSlack c) := by
    convert (sGlobal68_hz112 hc) using 1 <;>
      norm_num [s3L] <;> ring

theorem sGlobal68_hz114 {c : ℝ} (hc : B (137 / 200) (69 / 100) c) : B 0 (32369530434665906471 / 40000000000000000) |(s3U 12225 46 maskSlack c)| := bweaken (babs (sGlobal68_hz107 hc)) (by norm_num) (by norm_num)

theorem sGlobal68_hz115 {c : ℝ} (hc : B (137 / 200) (69 / 100) c) : B 0 (2747392855344558833753 / 1000000000000000000) |(s3L 12225 46 maskSlack c)| := bweaken (babs (sGlobal68_hz113 hc)) (by norm_num) (by norm_num)

theorem sGlobal68_hz116 {c : ℝ} (hc : B (137 / 200) (69 / 100) c) : B 0 (2747392855344558833753 / 1000000000000000000) (max |(s3U 12225 46 maskSlack c)| |(s3L 12225 46 maskSlack c)|) := bweaken (bmax (sGlobal68_hz114 hc) (sGlobal68_hz115 hc)) (by norm_num) (by norm_num)

theorem sGlobal68_hz117 {c : ℝ} (hc : B (137 / 200) (69 / 100) c) : B 0 (2747392855344558833753 / 1000000000000000000) (s3nks 12225 46 maskSlack c) := by
    convert (sGlobal68_hz116 hc) using 1 <;>
      norm_num [s3nks] <;> ring

theorem sGlobal68 {c : ℝ} (hc : B (137 / 200) (69 / 100) c) :
    0 < s3am 12225 46 ∧ 0 ≤ s3dm 12225 46 c ∧
    s3dm 12225 46 c ^ 2 ≤ 2 * s3ap 12225 46 ^ 2 ∧ s3c1 12225 46 c < 1 ∧
    0 ≤ s3Cpa 12225 c - s3r1 12225 46 ∧
    s3e0 12225 46 ≤ (s3Cpa 12225 c - s3r1 12225 46) / s3ap 12225 46 ∧
    s3nks 12225 46 maskSlack c ≤ 12225 * (7023 / 31250) := by

  refine ⟨lt_of_lt_of_le (by norm_num) sGlobal68_hz14.1,
    le_trans (by norm_num) (sGlobal68_hz64 hc).1, ?_,
    lt_of_le_of_lt (sGlobal68_hz72 hc).2 (by norm_num), ?_, ?_,
    le_trans (sGlobal68_hz117 hc).2 (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (sGlobal68_hz64 hc).1) (sGlobal68_hz64 hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) sGlobal68_hz9.1 2
    nlinarith only [h1, h2]
  · linarith only [(sGlobal68_hz84 hc).1, sGlobal68_hz33.2]
  · have hap : 0 < s3ap 12225 46 := lt_of_lt_of_le (by norm_num) sGlobal68_hz9.1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul sGlobal68_hz16.2 sGlobal68_hz9.2 (le_trans (by norm_num) sGlobal68_hz9.1) (by norm_num)
    linarith only [h, (sGlobal68_hz84 hc).1, sGlobal68_hz33.2]

end BstLean.Part255
