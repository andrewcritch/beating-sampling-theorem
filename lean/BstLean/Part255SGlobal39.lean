import BstLean.Part255SGlobal35
import BstLean.Part255Numeric10
namespace BstLean.Part255
open Real BstLean.Part130 BstLean.Part182 BstLean.Part197 BstLean.Part246
theorem sGlobal39_hz0 : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal39_hz1 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) ((√(23 : ℝ)) / (12225 : ℝ)) := bdiv sGlobal39_hz0 (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal39_hz2 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) maskSlack := by
    convert sGlobal39_hz1 using 1 <;>
      norm_num [maskSlack] <;> ring

theorem sGlobal39_hz3 : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal39_hz4 : B (6395294793910793 / 500000000000000000) (12790589587821587 / 1000000000000000000) (√((2 / 12225) : ℝ)) := bsqrt (bpoint ((2 / 12225) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal39_hz5 : B (7230130686979 / 62500000000000000) (23136418198333 / 200000000000000000) (√((2 / 149450625) : ℝ)) := bsqrt (bpoint ((2 / 149450625) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal39_hz6 : B (2211334438749598093 / 20000000000000000) (110566721937479904651 / 1000000000000000000) (√(12225 : ℝ)) := bsqrt (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal39_hz7 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))) := bmul sGlobal39_hz3 sGlobal39_hz4 (by norm_num) (by norm_num)

theorem sGlobal39_hz8 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) ((√(12225 : ℝ)) + ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := badd sGlobal39_hz6 sGlobal39_hz7 (by norm_num) (by norm_num)

theorem sGlobal39_hz9 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) (s3ap 12225 46) := by
    convert sGlobal39_hz8 using 1 <;>
      norm_num [s3ap, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal39_hz10 : B (163599182004089 / 1000000000000000000) (16359918200409 / 100000000000000000) ((2 : ℝ) / (12225 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal39_hz11 : B (1222499983640081799591 / 100000000000000000) (12224999836400817995911 / 1000000000000000000) ((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ))) := bsub (bpoint (12225 : ℝ)) sGlobal39_hz10 (by norm_num) (by norm_num)

theorem sGlobal39_hz12 : B (110566721197658827907 / 1000000000000000000) (27641680299414706977 / 250000000000000000) (√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) := bsqrt sGlobal39_hz11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal39_hz13 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) ((√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) - ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bsub sGlobal39_hz12 sGlobal39_hz7 (by norm_num) (by norm_num)

theorem sGlobal39_hz14 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) (s3am 12225 46) := by
    convert sGlobal39_hz13 using 1 <;>
      norm_num [s3am, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal39_hz15 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√((2 / 12225) : ℝ)) * (√(92 : ℝ))) := bmul sGlobal39_hz4 sGlobal39_hz3 (by norm_num) (by norm_num)

theorem sGlobal39_hz16 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) (s3e0 12225 46) := by
    convert sGlobal39_hz15 using 1 <;>
      norm_num [s3e0, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal39_hz17 : B (250196148528560847 / 500000000000000000) (100078459411424339 / 200000000000000000) (((1 / 2) : ℝ) + maskSlack) := badd (bpoint ((1 / 2) : ℝ)) sGlobal39_hz2 (by norm_num) (by norm_num)

theorem sGlobal39_hz18 : B (59827153232297998295487 / 800000000000000) (23930861292919199366019 / 320000000000000) ((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack)) := bmul (bpoint (149450625 : ℝ)) sGlobal39_hz17 (by norm_num) (by norm_num)

theorem sGlobal39_hz19 : B (1729554180017180009583 / 200000000000000000) (8647770900085900056557 / 1000000000000000000) (√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) := bsqrt sGlobal39_hz18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal39_hz20 : B (4328681281566262743499 / 500000000000000000) (8657362563132525495641 / 1000000000000000000) ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))) := badd sGlobal39_hz19 sGlobal39_hz3 (by norm_num) (by norm_num)

theorem sGlobal39_hz21 : B (110732771457999278473 / 1000000000000000000) (55366385728999643621 / 500000000000000000) ((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ)))) := bmul sGlobal39_hz4 sGlobal39_hz20 (by norm_num) (by norm_num)

theorem sGlobal39_hz22 : B (209099159 / 15625000000000000) (13382346177 / 1000000000000000000) ((2 : ℝ) / (149450625 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (149450625 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal39_hz23 : B (2452349334953899930479 / 200000000000000000) (12261746674769501594427 / 1000000000000000000) (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2) := bsq sGlobal39_hz21 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal39_hz24 : B (82045469362091 / 500000000000000000) (32818187747289 / 200000000000000000) (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2)) := bmul sGlobal39_hz22 sGlobal39_hz23 (by norm_num) (by norm_num)

theorem sGlobal39_hz25 : B (82045469362091 / 250000000000000000) (32818187747289 / 100000000000000000) ((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) := bmul (bpoint (2 : ℝ)) sGlobal39_hz24 (by norm_num) (by norm_num)

theorem sGlobal39_hz26 : B (117258080744995992792057 / 1000000000000000000) (58629040372497996396029 / 500000000000000000) (√(13749457500 : ℝ)) := bsqrt (bpoint (13749457500 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal39_hz27 : B (117304080744995992792057 / 1000000000000000000) (58652040372497996396029 / 500000000000000000) ((√(13749457500 : ℝ)) + (46 : ℝ)) := badd sGlobal39_hz26 (bpoint (46 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal39_hz28 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal39_hz25 sGlobal39_hz27 (by norm_num) (by norm_num)

theorem sGlobal39_hz29 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (s3rs 12225 46 maskSlack) := by
    convert sGlobal39_hz28 using 1 <;>
      norm_num [s3rs, s3pp, s3K, mA, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal39_hz30 : B (490797546012267 / 1000000000000000000) (49079754601227 / 100000000000000000) ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (3 : ℝ)) sGlobal39_hz10 (by norm_num) (by norm_num)

theorem sGlobal39_hz31 : B (490797546012267 / 500000000000000000) (49079754601227 / 50000000000000000) ((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal39_hz30 (by norm_num) (by norm_num)

theorem sGlobal39_hz32 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal39_hz31 sGlobal39_hz27 (by norm_num) (by norm_num)

theorem sGlobal39_hz33 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (s3r1 12225 46) := by
    convert sGlobal39_hz32 using 1 <;>
      norm_num [s3r1, mA] <;> ring

theorem sGlobal39_hz34 : B (163599182004089 / 500000000000000000) (16359918200409 / 50000000000000000) ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (2 : ℝ)) sGlobal39_hz10 (by norm_num) (by norm_num)

theorem sGlobal39_hz35 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal39_hz34 (by norm_num) (by norm_num)

theorem sGlobal39_hz36 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal39_hz35 sGlobal39_hz27 (by norm_num) (by norm_num)

theorem sGlobal39_hz37 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (s3rpp 12225 46) := by
    convert sGlobal39_hz36 using 1 <;>
      norm_num [s3rpp, mA] <;> ring

theorem sGlobal39_hz38 {c : ℝ} (hc : B (27 / 50) (109 / 200) c) : B (27 / 50) (109 / 200) c := hc

theorem sGlobal39_hz39 : B (340787885684049643 / 500000000000000000) (340787885684051451 / 500000000000000000) (kdot ((27 / 50))) := by
    constructor
    · apply bkdot_lower (q := (68316965625002639 / 125000000000000000)) (a := (50017960869748799 / 100000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (546535725000021111 / 1000000000000000000)) (a := (500179608697482311 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal39_hz40 : B (729 / 2500) (729 / 2500) (((27 / 50) : ℝ)^2) := bsq (bpoint ((27 / 50) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal39_hz41 : B (1771 / 2500) (1771 / 2500) ((1 : ℝ) - (((27 / 50) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal39_hz40 (by norm_num) (by norm_num)

theorem sGlobal39_hz42 : B (841665016500032511 / 1000000000000000000) (821938492675813 / 976562500000000) (√((1 : ℝ) - (((27 / 50) : ℝ)^2))) := bsqrt sGlobal39_hz41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal39_hz43 : B (133955147803501823 / 500000000000000000) (267910295607003647 / 1000000000000000000) ((√((1 : ℝ) - (((27 / 50) : ℝ)^2))) / Real.pi) := bdiv sGlobal39_hz42 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal39_hz44 : B (184025458269386807 / 500000000000000000) (23003182283673473 / 62500000000000000) (((27 / 50) : ℝ) * (kdot ((27 / 50)))) := bmul (bpoint ((27 / 50) : ℝ)) sGlobal39_hz39 (by norm_num) (by norm_num)

theorem sGlobal39_hz45 : B (31798060607288863 / 50000000000000000) (127192242429155843 / 200000000000000000) (((√((1 : ℝ) - (((27 / 50) : ℝ)^2))) / Real.pi) + (((27 / 50) : ℝ) * (kdot ((27 / 50))))) := badd sGlobal39_hz43 sGlobal39_hz44 (by norm_num) (by norm_num)

theorem sGlobal39_hz46 : B (31798060607288863 / 50000000000000000) (127192242429155843 / 200000000000000000) (kappa ((27 / 50))) := by rw [kappa_eq]; exact sGlobal39_hz45

theorem sGlobal39_hz47 : B (683470353509254499 / 1000000000000000000) (136694070701851411 / 200000000000000000) (kdot ((109 / 200))) := by
    constructor
    · apply bkdot_lower (q := (54267705117963359 / 100000000000000000)) (a := (497203606029350171 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (542677051179633589 / 1000000000000000000)) (a := (497203606029346157 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal39_hz48 : B (11881 / 40000) (11881 / 40000) (((109 / 200) : ℝ)^2) := bsq (bpoint ((109 / 200) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal39_hz49 : B (28119 / 40000) (28119 / 40000) ((1 : ℝ) - (((109 / 200) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal39_hz48 (by norm_num) (by norm_num)

theorem sGlobal39_hz50 : B (167687208814506779 / 200000000000000000) (104804505509066737 / 125000000000000000) (√((1 : ℝ) - (((109 / 200) : ℝ)^2))) := bsqrt sGlobal39_hz49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal39_hz51 : B (266882481761115963 / 1000000000000000000) (66720620440278991 / 250000000000000000) ((√((1 : ℝ) - (((109 / 200) : ℝ)^2))) / Real.pi) := bdiv sGlobal39_hz50 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal39_hz52 : B (372491342662543701 / 1000000000000000000) (74498268532509019 / 200000000000000000) (((109 / 200) : ℝ) * (kdot ((109 / 200)))) := bmul (bpoint ((109 / 200) : ℝ)) sGlobal39_hz47 (by norm_num) (by norm_num)

theorem sGlobal39_hz53 : B (39960864026478729 / 62500000000000000) (639373824423661059 / 1000000000000000000) (((√((1 : ℝ) - (((109 / 200) : ℝ)^2))) / Real.pi) + (((109 / 200) : ℝ) * (kdot ((109 / 200))))) := badd sGlobal39_hz51 sGlobal39_hz52 (by norm_num) (by norm_num)

theorem sGlobal39_hz54 : B (39960864026478729 / 62500000000000000) (639373824423661059 / 1000000000000000000) (kappa ((109 / 200))) := by rw [kappa_eq]; exact sGlobal39_hz53

theorem sGlobal39_hz55 {c : ℝ} (hc : B (27 / 50) (109 / 200) c) : B (31798060607288863 / 50000000000000000) (639373824423661059 / 1000000000000000000) (kappa c) := bkappa (sGlobal39_hz38 hc) (by norm_num) (by norm_num) sGlobal39_hz46.1 sGlobal39_hz54.2

theorem sGlobal39_hz56 : B 24450 24450 ((2 : ℝ) * (12225 : ℝ)) := bmul (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal39_hz57 {c : ℝ} (hc : B (27 / 50) (109 / 200) c) : B (360626175576338941 / 1000000000000000000) (18201939392711137 / 50000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (sGlobal39_hz55 hc) (by norm_num) (by norm_num)

theorem sGlobal39_hz58 {c : ℝ} (hc : B (27 / 50) (109 / 200) c) : B (176346199856829742149 / 20000000000000000) (8900748363035745993 / 1000000000000000) (((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) := bmul sGlobal39_hz56 (sGlobal39_hz57 hc) (by norm_num) (by norm_num)

theorem sGlobal39_hz59 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (4 : ℝ)) sGlobal39_hz10 (by norm_num) (by norm_num)

theorem sGlobal39_hz60 {c : ℝ} (hc : B (27 / 50) (109 / 200) c) : B (881730933844475909109 / 100000000000000000) (2225186927159754494161 / 250000000000000000) ((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bsub (sGlobal39_hz58 hc) sGlobal39_hz59 (by norm_num) (by norm_num)

theorem sGlobal39_hz61 {c : ℝ} (hc : B (27 / 50) (109 / 200) c) : B (93900528957214927347 / 1000000000000000000) (94343774085198743319 / 1000000000000000000) (√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) := bsqrt (sGlobal39_hz60 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal39_hz62 : B (30670756373515103 / 125000000000000000) (122683025494060423 / 500000000000000000) ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal39_hz7 (by norm_num) (by norm_num)

theorem sGlobal39_hz63 {c : ℝ} (hc : B (27 / 50) (109 / 200) c) : B (93655162906226806501 / 1000000000000000000) (18819681606842124499 / 200000000000000000) ((√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) - ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))))) := bsub (sGlobal39_hz61 hc) sGlobal39_hz62 (by norm_num) (by norm_num)

theorem sGlobal39_hz64 {c : ℝ} (hc : B (27 / 50) (109 / 200) c) : B (93655162906226806501 / 1000000000000000000) (18819681606842124499 / 200000000000000000) (s3dm 12225 46 c) := by
    convert (sGlobal39_hz63 hc) using 1 <;>
      norm_num [s3dm, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal39_hz65 : B (6126072185528622723889 / 500000000000000000) (2450428874211449090087 / 200000000000000000) ((s3ap 12225 46)^2) := bsq sGlobal39_hz9 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal39_hz66 : B (6126072185528622723889 / 250000000000000000) (2450428874211449090087 / 100000000000000000) ((2 : ℝ) * ((s3ap 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal39_hz65 (by norm_num) (by norm_num)

theorem sGlobal39_hz67 {c : ℝ} (hc : B (27 / 50) (109 / 200) c) : B (4385644769495940782217 / 500000000000000000) (2213627598643198557027 / 250000000000000000) ((s3dm 12225 46 c)^2) := bsq (sGlobal39_hz64 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal39_hz68 {c : ℝ} (hc : B (27 / 50) (109 / 200) c) : B (1956222293442712083431 / 125000000000000000) (3933249800780652334109 / 250000000000000000) (((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) := bsub sGlobal39_hz66 (sGlobal39_hz67 hc) (by norm_num) (by norm_num)

theorem sGlobal39_hz69 : B (1524735695971823534271 / 125000000000000000) (609894278388729413841 / 50000000000000000) ((s3am 12225 46)^2) := bsq sGlobal39_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal39_hz70 : B (1524735695971823534271 / 62500000000000000) (609894278388729413841 / 25000000000000000) ((2 : ℝ) * ((s3am 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal39_hz69 (by norm_num) (by norm_num)

theorem sGlobal39_hz71 {c : ℝ} (hc : B (27 / 50) (109 / 200) c) : B (320747769369279303 / 500000000000000000) (80613352595548327 / 125000000000000000) ((((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) / ((2 : ℝ) * ((s3am 12225 46)^2))) := bdiv (sGlobal39_hz68 hc) sGlobal39_hz70 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal39_hz72 {c : ℝ} (hc : B (27 / 50) (109 / 200) c) : B (320747769369279303 / 500000000000000000) (80613352595548327 / 125000000000000000) (s3c1 12225 46 c) := by
    convert (sGlobal39_hz71 hc) using 1 <;>
      norm_num [s3c1] <;> ring

theorem sGlobal39_hz73 {c : ℝ} (hc : B (27 / 50) (109 / 200) c) : B (340787885684049643 / 500000000000000000) (136694070701851411 / 200000000000000000) (kdot c) := bkdot (sGlobal39_hz38 hc) sGlobal39_hz39.1 sGlobal39_hz47.2

theorem sGlobal39_hz74 : B (721685714809593349 / 1000000000000000000) (90210714351199169 / 125000000000000000) (kdot ((320747769369279303 / 500000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (93466810847298967 / 200000000000000000)) (a := (218587528435819031 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (233667027118247417 / 500000000000000000)) (a := (218587528435819029 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal39_hz75 : B (144620766189245921 / 200000000000000000) (90387978868278701 / 125000000000000000) (kdot ((80613352595548327 / 125000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (116155699118732501 / 250000000000000000)) (a := (434947485253241261 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (464622796474930003 / 1000000000000000000)) (a := (434947485253241257 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal39_hz76 {c : ℝ} (hc : B (27 / 50) (109 / 200) c) : B (721685714809593349 / 1000000000000000000) (90387978868278701 / 125000000000000000) (kdot (s3c1 12225 46 c)) := bkdot (sGlobal39_hz72 hc) sGlobal39_hz74.1 sGlobal39_hz75.2

theorem sGlobal39_hz77 {c : ℝ} (hc : B (27 / 50) (109 / 200) c) : B (729 / 2500) (11881 / 40000) (c^2) := bsq (sGlobal39_hz38 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal39_hz78 {c : ℝ} (hc : B (27 / 50) (109 / 200) c) : B (28119 / 40000) (1771 / 2500) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (sGlobal39_hz77 hc) (by norm_num) (by norm_num)

theorem sGlobal39_hz79 {c : ℝ} (hc : B (27 / 50) (109 / 200) c) : B (167687208814506779 / 200000000000000000) (821938492675813 / 976562500000000) (√((1 : ℝ) - (c^2))) := bsqrt (sGlobal39_hz78 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal39_hz80 : B (39119999999999765769 / 1600000000000000) (3912000000000000489 / 160000000000000) ((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (149450625 : ℝ)) sGlobal39_hz10 (by norm_num) (by norm_num)

theorem sGlobal39_hz81 {c : ℝ} (hc : B (27 / 50) (109 / 200) c) : B (285728846740777489 / 500000000000000000) (287626543181825947 / 500000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (sGlobal39_hz79 hc) (sGlobal39_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal39_hz82 {c : ℝ} (hc : B (27 / 50) (109 / 200) c) : B (3493035151405983888477 / 250000000000000000) (7032468980795645283209 / 500000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) := bmul sGlobal39_hz80 (sGlobal39_hz81 hc) (by norm_num) (by norm_num)

theorem sGlobal39_hz83 {c : ℝ} (hc : B (27 / 50) (109 / 200) c) : B (3493035151405983888477 / 500000000000000000) (7032468980795645283209 / 1000000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) / (2 : ℝ)) := bdiv (sGlobal39_hz82 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal39_hz84 {c : ℝ} (hc : B (27 / 50) (109 / 200) c) : B (3493035151405983888477 / 500000000000000000) (7032468980795645283209 / 1000000000000000000) (s3Cpa 12225 c) := by
    convert (sGlobal39_hz83 hc) using 1 <;>
      norm_num [s3Cpa, mA] <;> ring

theorem sGlobal39_hz85 {c : ℝ} (hc : B (27 / 50) (109 / 200) c) : B (266882481761115963 / 1000000000000000000) (267910295607003647 / 1000000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (sGlobal39_hz79 hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal39_hz86 {c : ℝ} (hc : B (27 / 50) (109 / 200) c) : B (184025458269386807 / 500000000000000000) (74498268532509019 / 200000000000000000) (c * (kdot c)) := bmul (sGlobal39_hz38 hc) (sGlobal39_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal39_hz87 {c : ℝ} (hc : B (27 / 50) (109 / 200) c) : B (-26402215225357283 / 250000000000000000) (-100140620931769967 / 1000000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (sGlobal39_hz85 hc) (sGlobal39_hz86 hc) (by norm_num) (by norm_num)

theorem sGlobal39_hz88 {c : ℝ} (hc : B (27 / 50) (109 / 200) c) : B (-322767081129992825021 / 125000000000000000) (-1224219090890880516563 / 500000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) := bmul sGlobal39_hz80 (sGlobal39_hz87 hc) (by norm_num) (by norm_num)

theorem sGlobal39_hz89 {c : ℝ} (hc : B (27 / 50) (109 / 200) c) : B (-322767081129992825021 / 250000000000000000) (-1224219090890880516563 / 1000000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) / (2 : ℝ)) := bdiv (sGlobal39_hz88 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal39_hz90 {c : ℝ} (hc : B (27 / 50) (109 / 200) c) : B (-322767081129992825021 / 250000000000000000) (-1224219090890880516563 / 1000000000000000000) (s3Cpp 12225 c) := by
    convert (sGlobal39_hz89 hc) using 1 <;>
      norm_num [s3Cpp, mA] <;> ring

theorem sGlobal39_hz91 {c : ℝ} (hc : B (27 / 50) (109 / 200) c) : B (1420243082549141097071 / 200000000000000000) (1429522818145876739087 / 200000000000000000) ((s3Cpa 12225 c) + (s3r1 12225 46)) := badd (sGlobal39_hz84 hc) sGlobal39_hz33 (by norm_num) (by norm_num)

theorem sGlobal39_hz92 {c : ℝ} (hc : B (27 / 50) (109 / 200) c) : B (6429695554662747013 / 100000000000000000) (6471706584639168211 / 100000000000000000) (((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) := bdiv (sGlobal39_hz91 hc) sGlobal39_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal39_hz93 {c : ℝ} (hc : B (27 / 50) (109 / 200) c) : B (32209819286060765271 / 500000000000000000) (64839748871885742533 / 1000000000000000000) ((((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) + (s3e0 12225 46)) := badd (sGlobal39_hz92 hc) sGlobal39_hz16 (by norm_num) (by norm_num)

theorem sGlobal39_hz94 {c : ℝ} (hc : B (27 / 50) (109 / 200) c) : B (32209819286060765271 / 500000000000000000) (64839748871885742533 / 1000000000000000000) (s3Lam 12225 46 c) := by
    convert (sGlobal39_hz93 hc) using 1 <;>
      norm_num [s3Lam] <;> ring

theorem sGlobal39_hz95 {c : ℝ} (hc : B (27 / 50) (109 / 200) c) : B (-303576229474369873621 / 250000000000000000) (-229491136853677648349 / 200000000000000000) ((s3Cpp 12225 c) + (s3rpp 12225 46)) := badd (sGlobal39_hz90 hc) sGlobal39_hz37 (by norm_num) (by norm_num)

theorem sGlobal39_hz96 {c : ℝ} (hc : B (27 / 50) (109 / 200) c) : B (-878068538068514236263 / 1000000000000000000) (-71715980266774265109 / 125000000000000000) (if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) := bweaken (bfirst (sGlobal39_hz95 hc) (sGlobal39_hz76 hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem sGlobal39_hz97 {c : ℝ} (hc : B (27 / 50) (109 / 200) c) : B (2074944916881384053183 / 500000000000000000) (84083860675384168429 / 20000000000000000) ((s3Lam 12225 46 c)^2) := bsq (sGlobal39_hz94 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal39_hz98 {c : ℝ} (hc : B (27 / 50) (109 / 200) c) : B (82303305244294709 / 200000000000000000) (83180961493685737 / 200000000000000000) ((s3c1 12225 46 c)^2) := bsq (sGlobal39_hz72 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal39_hz99 {c : ℝ} (hc : B (27 / 50) (109 / 200) c) : B (116819038506314263 / 200000000000000000) (117696694755705291 / 200000000000000000) ((1 : ℝ) - ((s3c1 12225 46 c)^2)) := bsub (bpoint (1 : ℝ)) (sGlobal39_hz98 hc) (by norm_num) (by norm_num)

theorem sGlobal39_hz100 {c : ℝ} (hc : B (27 / 50) (109 / 200) c) : B (764261207004235767 / 1000000000000000000) (767126765129809857 / 1000000000000000000) (√((1 : ℝ) - ((s3c1 12225 46 c)^2))) := bsqrt (sGlobal39_hz99 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal39_hz101 {c : ℝ} (hc : B (27 / 50) (109 / 200) c) : B (2400997393348175317 / 1000000000000000000) (1204999904851956709 / 500000000000000000) (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))) := bmul pi_mem (sGlobal39_hz100 hc) (by norm_num) (by norm_num)

theorem sGlobal39_hz102 {c : ℝ} (hc : B (27 / 50) (109 / 200) c) : B (215243265634978060897 / 125000000000000000) (109438712985921042087 / 62500000000000000) (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2))))) := bdiv (sGlobal39_hz97 hc) (sGlobal39_hz101 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal39_hz103 {c : ℝ} (hc : B (27 / 50) (109 / 200) c) : B (843877587011310250913 / 1000000000000000000) (29432289141013563813 / 25000000000000000) ((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) := badd (sGlobal39_hz96 hc) (sGlobal39_hz102 hc) (by norm_num) (by norm_num)

theorem sGlobal39_hz104 : B (3762781186094069 / 250000000000000000) (376278118609407 / 25000000000000000) ((s3e0 12225 46)^2) := bsq sGlobal39_hz16 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal39_hz105 {c : ℝ} (hc : B (27 / 50) (109 / 200) c) : B (843892638136054627189 / 1000000000000000000) (1471633270956608661 / 1250000000000000) (((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) := badd (sGlobal39_hz103 hc) sGlobal39_hz104 (by norm_num) (by norm_num)

theorem sGlobal39_hz106 {c : ℝ} (hc : B (27 / 50) (109 / 200) c) : B (22059742789682547433 / 25000000000000000) (37993865319356599963 / 31250000000000000) ((((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) + (s3rs 12225 46 maskSlack)) := badd (sGlobal39_hz105 hc) sGlobal39_hz29 (by norm_num) (by norm_num)

theorem sGlobal39_hz107 {c : ℝ} (hc : B (27 / 50) (109 / 200) c) : B (22059742789682547433 / 25000000000000000) (37993865319356599963 / 31250000000000000) (s3U 12225 46 maskSlack c) := by
    convert (sGlobal39_hz106 hc) using 1 <;>
      norm_num [s3U] <;> ring

theorem sGlobal39_hz108 {c : ℝ} (hc : B (27 / 50) (109 / 200) c) : B (-683915865571231787451 / 500000000000000000) (-1300982497513372322163 / 1000000000000000000) ((s3Cpp 12225 c) - (s3rpp 12225 46)) := bsub (sGlobal39_hz90 hc) sGlobal39_hz37 (by norm_num) (by norm_num)

theorem sGlobal39_hz109 {c : ℝ} (hc : B (27 / 50) (109 / 200) c) : B (-683915865571231787451 / 500000000000000000) (-1300982497513372322163 / 1000000000000000000) (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ)) := bweaken (bmin (sGlobal39_hz108 hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem sGlobal39_hz110 {c : ℝ} (hc : B (27 / 50) (109 / 200) c) : B (-989084364878928569417 / 1000000000000000000) (-46945024183635405301 / 50000000000000000) ((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) := bmul (sGlobal39_hz76 hc) (sGlobal39_hz109 hc) (by norm_num) (by norm_num)

theorem sGlobal39_hz111 {c : ℝ} (hc : B (27 / 50) (109 / 200) c) : B (-989099416003672945697 / 1000000000000000000) (-117364441849681560287 / 125000000000000000) (((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) := bsub (sGlobal39_hz110 hc) sGlobal39_hz104 (by norm_num) (by norm_num)

theorem sGlobal39_hz112 {c : ℝ} (hc : B (27 / 50) (109 / 200) c) : B (-1027596489457797215713 / 1000000000000000000) (-977412608248699752427 / 1000000000000000000) ((((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) - (s3rs 12225 46 maskSlack)) := bsub (sGlobal39_hz111 hc) sGlobal39_hz29 (by norm_num) (by norm_num)

theorem sGlobal39_hz113 {c : ℝ} (hc : B (27 / 50) (109 / 200) c) : B (-1027596489457797215713 / 1000000000000000000) (-977412608248699752427 / 1000000000000000000) (s3L 12225 46 maskSlack c) := by
    convert (sGlobal39_hz112 hc) using 1 <;>
      norm_num [s3L] <;> ring

theorem sGlobal39_hz114 {c : ℝ} (hc : B (27 / 50) (109 / 200) c) : B 0 (37993865319356599963 / 31250000000000000) |(s3U 12225 46 maskSlack c)| := bweaken (babs (sGlobal39_hz107 hc)) (by norm_num) (by norm_num)

theorem sGlobal39_hz115 {c : ℝ} (hc : B (27 / 50) (109 / 200) c) : B 0 (1027596489457797215713 / 1000000000000000000) |(s3L 12225 46 maskSlack c)| := bweaken (babs (sGlobal39_hz113 hc)) (by norm_num) (by norm_num)

theorem sGlobal39_hz116 {c : ℝ} (hc : B (27 / 50) (109 / 200) c) : B 0 (37993865319356599963 / 31250000000000000) (max |(s3U 12225 46 maskSlack c)| |(s3L 12225 46 maskSlack c)|) := bweaken (bmax (sGlobal39_hz114 hc) (sGlobal39_hz115 hc)) (by norm_num) (by norm_num)

theorem sGlobal39_hz117 {c : ℝ} (hc : B (27 / 50) (109 / 200) c) : B 0 (37993865319356599963 / 31250000000000000) (s3nks 12225 46 maskSlack c) := by
    convert (sGlobal39_hz116 hc) using 1 <;>
      norm_num [s3nks] <;> ring

theorem sGlobal39 {c : ℝ} (hc : B (27 / 50) (109 / 200) c) :
    0 < s3am 12225 46 ∧ 0 ≤ s3dm 12225 46 c ∧
    s3dm 12225 46 c ^ 2 ≤ 2 * s3ap 12225 46 ^ 2 ∧ s3c1 12225 46 c < 1 ∧
    0 ≤ s3Cpa 12225 c - s3r1 12225 46 ∧
    s3e0 12225 46 ≤ (s3Cpa 12225 c - s3r1 12225 46) / s3ap 12225 46 ∧
    s3nks 12225 46 maskSlack c ≤ 12225 * (99453 / 1000000) := by

  refine ⟨lt_of_lt_of_le (by norm_num) sGlobal39_hz14.1,
    le_trans (by norm_num) (sGlobal39_hz64 hc).1, ?_,
    lt_of_le_of_lt (sGlobal39_hz72 hc).2 (by norm_num), ?_, ?_,
    le_trans (sGlobal39_hz117 hc).2 (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (sGlobal39_hz64 hc).1) (sGlobal39_hz64 hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) sGlobal39_hz9.1 2
    nlinarith only [h1, h2]
  · linarith only [(sGlobal39_hz84 hc).1, sGlobal39_hz33.2]
  · have hap : 0 < s3ap 12225 46 := lt_of_lt_of_le (by norm_num) sGlobal39_hz9.1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul sGlobal39_hz16.2 sGlobal39_hz9.2 (le_trans (by norm_num) sGlobal39_hz9.1) (by norm_num)
    linarith only [h, (sGlobal39_hz84 hc).1, sGlobal39_hz33.2]

end BstLean.Part255
