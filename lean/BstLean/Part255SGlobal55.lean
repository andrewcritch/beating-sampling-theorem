import BstLean.Part255SGlobal51
import BstLean.Part255Numeric10
namespace BstLean.Part255
open Real BstLean.Part130 BstLean.Part182 BstLean.Part197 BstLean.Part246
theorem sGlobal55_hz0 : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal55_hz1 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) ((√(23 : ℝ)) / (12225 : ℝ)) := bdiv sGlobal55_hz0 (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal55_hz2 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) maskSlack := by
    convert sGlobal55_hz1 using 1 <;>
      norm_num [maskSlack] <;> ring

theorem sGlobal55_hz3 : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal55_hz4 : B (6395294793910793 / 500000000000000000) (12790589587821587 / 1000000000000000000) (√((2 / 12225) : ℝ)) := bsqrt (bpoint ((2 / 12225) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal55_hz5 : B (7230130686979 / 62500000000000000) (23136418198333 / 200000000000000000) (√((2 / 149450625) : ℝ)) := bsqrt (bpoint ((2 / 149450625) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal55_hz6 : B (2211334438749598093 / 20000000000000000) (110566721937479904651 / 1000000000000000000) (√(12225 : ℝ)) := bsqrt (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal55_hz7 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))) := bmul sGlobal55_hz3 sGlobal55_hz4 (by norm_num) (by norm_num)

theorem sGlobal55_hz8 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) ((√(12225 : ℝ)) + ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := badd sGlobal55_hz6 sGlobal55_hz7 (by norm_num) (by norm_num)

theorem sGlobal55_hz9 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) (s3ap 12225 46) := by
    convert sGlobal55_hz8 using 1 <;>
      norm_num [s3ap, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal55_hz10 : B (163599182004089 / 1000000000000000000) (16359918200409 / 100000000000000000) ((2 : ℝ) / (12225 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal55_hz11 : B (1222499983640081799591 / 100000000000000000) (12224999836400817995911 / 1000000000000000000) ((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ))) := bsub (bpoint (12225 : ℝ)) sGlobal55_hz10 (by norm_num) (by norm_num)

theorem sGlobal55_hz12 : B (110566721197658827907 / 1000000000000000000) (27641680299414706977 / 250000000000000000) (√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) := bsqrt sGlobal55_hz11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal55_hz13 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) ((√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) - ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bsub sGlobal55_hz12 sGlobal55_hz7 (by norm_num) (by norm_num)

theorem sGlobal55_hz14 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) (s3am 12225 46) := by
    convert sGlobal55_hz13 using 1 <;>
      norm_num [s3am, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal55_hz15 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√((2 / 12225) : ℝ)) * (√(92 : ℝ))) := bmul sGlobal55_hz4 sGlobal55_hz3 (by norm_num) (by norm_num)

theorem sGlobal55_hz16 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) (s3e0 12225 46) := by
    convert sGlobal55_hz15 using 1 <;>
      norm_num [s3e0, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal55_hz17 : B (250196148528560847 / 500000000000000000) (100078459411424339 / 200000000000000000) (((1 / 2) : ℝ) + maskSlack) := badd (bpoint ((1 / 2) : ℝ)) sGlobal55_hz2 (by norm_num) (by norm_num)

theorem sGlobal55_hz18 : B (59827153232297998295487 / 800000000000000) (23930861292919199366019 / 320000000000000) ((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack)) := bmul (bpoint (149450625 : ℝ)) sGlobal55_hz17 (by norm_num) (by norm_num)

theorem sGlobal55_hz19 : B (1729554180017180009583 / 200000000000000000) (8647770900085900056557 / 1000000000000000000) (√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) := bsqrt sGlobal55_hz18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal55_hz20 : B (4328681281566262743499 / 500000000000000000) (8657362563132525495641 / 1000000000000000000) ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))) := badd sGlobal55_hz19 sGlobal55_hz3 (by norm_num) (by norm_num)

theorem sGlobal55_hz21 : B (110732771457999278473 / 1000000000000000000) (55366385728999643621 / 500000000000000000) ((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ)))) := bmul sGlobal55_hz4 sGlobal55_hz20 (by norm_num) (by norm_num)

theorem sGlobal55_hz22 : B (209099159 / 15625000000000000) (13382346177 / 1000000000000000000) ((2 : ℝ) / (149450625 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (149450625 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal55_hz23 : B (2452349334953899930479 / 200000000000000000) (12261746674769501594427 / 1000000000000000000) (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2) := bsq sGlobal55_hz21 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal55_hz24 : B (82045469362091 / 500000000000000000) (32818187747289 / 200000000000000000) (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2)) := bmul sGlobal55_hz22 sGlobal55_hz23 (by norm_num) (by norm_num)

theorem sGlobal55_hz25 : B (82045469362091 / 250000000000000000) (32818187747289 / 100000000000000000) ((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) := bmul (bpoint (2 : ℝ)) sGlobal55_hz24 (by norm_num) (by norm_num)

theorem sGlobal55_hz26 : B (117258080744995992792057 / 1000000000000000000) (58629040372497996396029 / 500000000000000000) (√(13749457500 : ℝ)) := bsqrt (bpoint (13749457500 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal55_hz27 : B (117304080744995992792057 / 1000000000000000000) (58652040372497996396029 / 500000000000000000) ((√(13749457500 : ℝ)) + (46 : ℝ)) := badd sGlobal55_hz26 (bpoint (46 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal55_hz28 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal55_hz25 sGlobal55_hz27 (by norm_num) (by norm_num)

theorem sGlobal55_hz29 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (s3rs 12225 46 maskSlack) := by
    convert sGlobal55_hz28 using 1 <;>
      norm_num [s3rs, s3pp, s3K, mA, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal55_hz30 : B (490797546012267 / 1000000000000000000) (49079754601227 / 100000000000000000) ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (3 : ℝ)) sGlobal55_hz10 (by norm_num) (by norm_num)

theorem sGlobal55_hz31 : B (490797546012267 / 500000000000000000) (49079754601227 / 50000000000000000) ((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal55_hz30 (by norm_num) (by norm_num)

theorem sGlobal55_hz32 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal55_hz31 sGlobal55_hz27 (by norm_num) (by norm_num)

theorem sGlobal55_hz33 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (s3r1 12225 46) := by
    convert sGlobal55_hz32 using 1 <;>
      norm_num [s3r1, mA] <;> ring

theorem sGlobal55_hz34 : B (163599182004089 / 500000000000000000) (16359918200409 / 50000000000000000) ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (2 : ℝ)) sGlobal55_hz10 (by norm_num) (by norm_num)

theorem sGlobal55_hz35 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal55_hz34 (by norm_num) (by norm_num)

theorem sGlobal55_hz36 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal55_hz35 sGlobal55_hz27 (by norm_num) (by norm_num)

theorem sGlobal55_hz37 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (s3rpp 12225 46) := by
    convert sGlobal55_hz36 using 1 <;>
      norm_num [s3rpp, mA] <;> ring

theorem sGlobal55_hz38 {c : ℝ} (hc : B (31 / 50) (5 / 8) c) : B (31 / 50) (5 / 8) c := hc

theorem sGlobal55_hz39 : B (11138553339727929 / 15625000000000000) (712867413742587469 / 1000000000000000000) (kdot ((31 / 50))) := by
    constructor
    · apply bkdot_lower (q := (484322104837852617 / 1000000000000000000)) (a := (90205362359252487 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (60540263104731577 / 125000000000000000)) (a := (451026811796262417 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal55_hz40 : B (961 / 2500) (961 / 2500) (((31 / 50) : ℝ)^2) := bsq (bpoint ((31 / 50) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal55_hz41 : B (1539 / 2500) (1539 / 2500) ((1 : ℝ) - (((31 / 50) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal55_hz40 (by norm_num) (by norm_num)

theorem sGlobal55_hz42 : B (784601809837321239 / 1000000000000000000) (19615045245933031 / 25000000000000000) (√((1 : ℝ) - (((31 / 50) : ℝ)^2))) := bsqrt sGlobal55_hz41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal55_hz43 : B (49949302557782779 / 200000000000000000) (31218314098614237 / 125000000000000000) ((√((1 : ℝ) - (((31 / 50) : ℝ)^2))) / Real.pi) := bdiv sGlobal55_hz42 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal55_hz44 : B (220988898260202111 / 500000000000000000) (441977796520404231 / 1000000000000000000) (((31 / 50) : ℝ) * (kdot ((31 / 50)))) := bmul (bpoint ((31 / 50) : ℝ)) sGlobal55_hz39 (by norm_num) (by norm_num)

theorem sGlobal55_hz45 : B (691724309309318117 / 1000000000000000000) (691724309309318127 / 1000000000000000000) (((√((1 : ℝ) - (((31 / 50) : ℝ)^2))) / Real.pi) + (((31 / 50) : ℝ) * (kdot ((31 / 50))))) := badd sGlobal55_hz43 sGlobal55_hz44 (by norm_num) (by norm_num)

theorem sGlobal55_hz46 : B (691724309309318117 / 1000000000000000000) (691724309309318127 / 1000000000000000000) (kappa ((31 / 50))) := by rw [kappa_eq]; exact sGlobal55_hz45

theorem sGlobal55_hz47 : B (142980208281654933 / 200000000000000000) (714901041408274673 / 1000000000000000000) (kdot ((5 / 8))) := by
    constructor
    · apply bkdot_lower (q := (480384461415261401 / 1000000000000000000)) (a := (55979049616116561 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (2401922307076307 / 5000000000000000)) (a := (111958099232233119 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal55_hz48 : B (25 / 64) (25 / 64) (((5 / 8) : ℝ)^2) := bsq (bpoint ((5 / 8) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal55_hz49 : B (39 / 64) (39 / 64) ((1 : ℝ) - (((5 / 8) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal55_hz48 (by norm_num) (by norm_num)

theorem sGlobal55_hz50 : B (31224989991991991 / 40000000000000000) (24394523431243743 / 31250000000000000) (√((1 : ℝ) - (((5 / 8) : ℝ)^2))) := bsqrt sGlobal55_hz49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal55_hz51 : B (15530035953814021 / 62500000000000000) (248480575261024337 / 1000000000000000000) ((√((1 : ℝ) - (((5 / 8) : ℝ)^2))) / Real.pi) := bdiv sGlobal55_hz50 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal55_hz52 : B (89362630176034333 / 200000000000000000) (446813150880171671 / 1000000000000000000) (((5 / 8) : ℝ) * (kdot ((5 / 8)))) := bmul (bpoint ((5 / 8) : ℝ)) sGlobal55_hz47 (by norm_num) (by norm_num)

theorem sGlobal55_hz53 : B (695293726141196001 / 1000000000000000000) (86911715767649501 / 125000000000000000) (((√((1 : ℝ) - (((5 / 8) : ℝ)^2))) / Real.pi) + (((5 / 8) : ℝ) * (kdot ((5 / 8))))) := badd sGlobal55_hz51 sGlobal55_hz52 (by norm_num) (by norm_num)

theorem sGlobal55_hz54 : B (695293726141196001 / 1000000000000000000) (86911715767649501 / 125000000000000000) (kappa ((5 / 8))) := by rw [kappa_eq]; exact sGlobal55_hz53

theorem sGlobal55_hz55 {c : ℝ} (hc : B (31 / 50) (5 / 8) c) : B (691724309309318117 / 1000000000000000000) (86911715767649501 / 125000000000000000) (kappa c) := bkappa (sGlobal55_hz38 hc) (by norm_num) (by norm_num) sGlobal55_hz46.1 sGlobal55_hz54.2

theorem sGlobal55_hz56 : B 24450 24450 ((2 : ℝ) * (12225 : ℝ)) := bmul (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal55_hz57 {c : ℝ} (hc : B (31 / 50) (5 / 8) c) : B (38088284232350499 / 125000000000000000) (308275690690681883 / 1000000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (sGlobal55_hz55 hc) (by norm_num) (by norm_num)

theorem sGlobal55_hz58 {c : ℝ} (hc : B (31 / 50) (5 / 8) c) : B (18625170989619394011 / 2500000000000000) (150746812747743440787 / 20000000000000000) (((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) := bmul sGlobal55_hz56 (sGlobal55_hz57 hc) (by norm_num) (by norm_num)

theorem sGlobal55_hz59 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (4 : ℝ)) sGlobal55_hz10 (by norm_num) (by norm_num)

theorem sGlobal55_hz60 {c : ℝ} (hc : B (31 / 50) (5 / 8) c) : B (186251693536275739701 / 25000000000000000) (3768669991495222011497 / 500000000000000000) ((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bsub (sGlobal55_hz58 hc) sGlobal55_hz59 (by norm_num) (by norm_num)

theorem sGlobal55_hz61 {c : ℝ} (hc : B (31 / 50) (5 / 8) c) : B (86313774922957862647 / 1000000000000000000) (86817855208421522161 / 1000000000000000000) (√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) := bsqrt (sGlobal55_hz60 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal55_hz62 : B (30670756373515103 / 125000000000000000) (122683025494060423 / 500000000000000000) ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal55_hz7 (by norm_num) (by norm_num)

theorem sGlobal55_hz63 {c : ℝ} (hc : B (31 / 50) (5 / 8) c) : B (86068408871969741801 / 1000000000000000000) (86572489157433401337 / 1000000000000000000) ((√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) - ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))))) := bsub (sGlobal55_hz61 hc) sGlobal55_hz62 (by norm_num) (by norm_num)

theorem sGlobal55_hz64 {c : ℝ} (hc : B (31 / 50) (5 / 8) c) : B (86068408871969741801 / 1000000000000000000) (86572489157433401337 / 1000000000000000000) (s3dm 12225 46 c) := by
    convert (sGlobal55_hz63 hc) using 1 <;>
      norm_num [s3dm, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal55_hz65 : B (6126072185528622723889 / 500000000000000000) (2450428874211449090087 / 200000000000000000) ((s3ap 12225 46)^2) := bsq sGlobal55_hz9 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal55_hz66 : B (6126072185528622723889 / 250000000000000000) (2450428874211449090087 / 100000000000000000) ((2 : ℝ) * ((s3ap 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal55_hz65 (by norm_num) (by norm_num)

theorem sGlobal55_hz67 {c : ℝ} (hc : B (31 / 50) (5 / 8) c) : B (7407771005752559762297 / 1000000000000000000) (3747397939456961917873 / 500000000000000000) ((s3dm 12225 46 c)^2) := bsq (sGlobal55_hz64 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal55_hz68 {c : ℝ} (hc : B (31 / 50) (5 / 8) c) : B (1700949286320056705981 / 100000000000000000) (17096517736361931138573 / 1000000000000000000) (((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) := bsub sGlobal55_hz66 (sGlobal55_hz67 hc) (by norm_num) (by norm_num)

theorem sGlobal55_hz69 : B (1524735695971823534271 / 125000000000000000) (609894278388729413841 / 50000000000000000) ((s3am 12225 46)^2) := bsq sGlobal55_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal55_hz70 : B (1524735695971823534271 / 62500000000000000) (609894278388729413841 / 25000000000000000) ((2 : ℝ) * ((s3am 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal55_hz69 (by norm_num) (by norm_num)

theorem sGlobal55_hz71 {c : ℝ} (hc : B (31 / 50) (5 / 8) c) : B (174307800814037109 / 250000000000000000) (175199603666648649 / 250000000000000000) ((((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) / ((2 : ℝ) * ((s3am 12225 46)^2))) := bdiv (sGlobal55_hz68 hc) sGlobal55_hz70 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal55_hz72 {c : ℝ} (hc : B (31 / 50) (5 / 8) c) : B (174307800814037109 / 250000000000000000) (175199603666648649 / 250000000000000000) (s3c1 12225 46 c) := by
    convert (sGlobal55_hz71 hc) using 1 <;>
      norm_num [s3c1] <;> ring

theorem sGlobal55_hz73 {c : ℝ} (hc : B (31 / 50) (5 / 8) c) : B (11138553339727929 / 15625000000000000) (714901041408274673 / 1000000000000000000) (kdot c) := bkdot (sGlobal55_hz38 hc) sGlobal55_hz39.1 sGlobal55_hz47.2

theorem sGlobal55_hz74 : B (745584905595100571 / 1000000000000000000) (745584905595100573 / 1000000000000000000) (kdot ((174307800814037109 / 250000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (422362210000536403 / 1000000000000000000)) (a := (399634295772392877 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (211181105000268201 / 500000000000000000)) (a := (3197074366179143 / 8000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal55_hz75 : B (186793188987713199 / 250000000000000000) (373586377975426399 / 500000000000000000) (kdot ((175199603666648649 / 250000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (209713084661965727 / 500000000000000000)) (a := (3102657080203729 / 7812500000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (419426169323931453 / 1000000000000000000)) (a := (39714010626607731 / 100000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal55_hz76 {c : ℝ} (hc : B (31 / 50) (5 / 8) c) : B (745584905595100571 / 1000000000000000000) (373586377975426399 / 500000000000000000) (kdot (s3c1 12225 46 c)) := bkdot (sGlobal55_hz72 hc) sGlobal55_hz74.1 sGlobal55_hz75.2

theorem sGlobal55_hz77 {c : ℝ} (hc : B (31 / 50) (5 / 8) c) : B (961 / 2500) (25 / 64) (c^2) := bsq (sGlobal55_hz38 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal55_hz78 {c : ℝ} (hc : B (31 / 50) (5 / 8) c) : B (39 / 64) (1539 / 2500) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (sGlobal55_hz77 hc) (by norm_num) (by norm_num)

theorem sGlobal55_hz79 {c : ℝ} (hc : B (31 / 50) (5 / 8) c) : B (31224989991991991 / 40000000000000000) (19615045245933031 / 25000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (sGlobal55_hz78 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal55_hz80 : B (39119999999999765769 / 1600000000000000) (3912000000000000489 / 160000000000000) ((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (149450625 : ℝ)) sGlobal55_hz10 (by norm_num) (by norm_num)

theorem sGlobal55_hz81 {c : ℝ} (hc : B (31 / 50) (5 / 8) c) : B (6956024331165471 / 12500000000000000) (560912650943518043 / 1000000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (sGlobal55_hz79 hc) (sGlobal55_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal55_hz82 {c : ℝ} (hc : B (31 / 50) (5 / 8) c) : B (13605983591759579810173 / 1000000000000000000) (342857857889225446641 / 25000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) := bmul sGlobal55_hz80 (sGlobal55_hz81 hc) (by norm_num) (by norm_num)

theorem sGlobal55_hz83 {c : ℝ} (hc : B (31 / 50) (5 / 8) c) : B (3401495897939894952543 / 500000000000000000) (342857857889225446641 / 50000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) / (2 : ℝ)) := bdiv (sGlobal55_hz82 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal55_hz84 {c : ℝ} (hc : B (31 / 50) (5 / 8) c) : B (3401495897939894952543 / 500000000000000000) (342857857889225446641 / 50000000000000000) (s3Cpa 12225 c) := by
    convert (sGlobal55_hz83 hc) using 1 <;>
      norm_num [s3Cpa, mA] <;> ring

theorem sGlobal55_hz85 {c : ℝ} (hc : B (31 / 50) (5 / 8) c) : B (15530035953814021 / 62500000000000000) (31218314098614237 / 125000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (sGlobal55_hz79 hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal55_hz86 {c : ℝ} (hc : B (31 / 50) (5 / 8) c) : B (220988898260202111 / 500000000000000000) (446813150880171671 / 1000000000000000000) (c * (kdot c)) := bmul (sGlobal55_hz38 hc) (sGlobal55_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal55_hz87 {c : ℝ} (hc : B (31 / 50) (5 / 8) c) : B (-39666515123829467 / 200000000000000000) (-96115641865745163 / 500000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (sGlobal55_hz85 hc) (sGlobal55_hz86 hc) (by norm_num) (by norm_num)

theorem sGlobal55_hz88 {c : ℝ} (hc : B (31 / 50) (5 / 8) c) : B (-606153934236019118363 / 125000000000000000) (-4700054887234910329121 / 1000000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) := bmul sGlobal55_hz80 (sGlobal55_hz87 hc) (by norm_num) (by norm_num)

theorem sGlobal55_hz89 {c : ℝ} (hc : B (31 / 50) (5 / 8) c) : B (-606153934236019118363 / 250000000000000000) (-29375343045218189557 / 12500000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) / (2 : ℝ)) := bdiv (sGlobal55_hz88 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal55_hz90 {c : ℝ} (hc : B (31 / 50) (5 / 8) c) : B (-606153934236019118363 / 250000000000000000) (-29375343045218189557 / 12500000000000000) (s3Cpp 12225 c) := by
    convert (sGlobal55_hz89 hc) using 1 <;>
      norm_num [s3Cpp, mA] <;> ring

theorem sGlobal55_hz91 {c : ℝ} (hc : B (31 / 50) (5 / 8) c) : B (6918136905813527613487 / 1000000000000000000) (3486151133859123672523 / 500000000000000000) ((s3Cpa 12225 c) + (s3r1 12225 46)) := badd (sGlobal55_hz84 hc) sGlobal55_hz33 (by norm_num) (by norm_num)

theorem sGlobal55_hz92 {c : ℝ} (hc : B (31 / 50) (5 / 8) c) : B (62639296971641399187 / 1000000000000000000) (15782432404476039087 / 250000000000000000) (((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) := bdiv (sGlobal55_hz91 hc) sGlobal55_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal55_hz93 {c : ℝ} (hc : B (31 / 50) (5 / 8) c) : B (62761979997135459599 / 1000000000000000000) (63252412643398216771 / 1000000000000000000) ((((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) + (s3e0 12225 46)) := badd (sGlobal55_hz92 hc) sGlobal55_hz16 (by norm_num) (by norm_num)

theorem sGlobal55_hz94 {c : ℝ} (hc : B (31 / 50) (5 / 8) c) : B (62761979997135459599 / 1000000000000000000) (63252412643398216771 / 1000000000000000000) (s3Lam 12225 46 c) := by
    convert (sGlobal55_hz93 hc) using 1 <;>
      norm_num [s3Lam] <;> ring

theorem sGlobal55_hz95 {c : ℝ} (hc : B (31 / 50) (5 / 8) c) : B (-586963082580396166963 / 250000000000000000) (-1136632018497481444871 / 500000000000000000) ((s3Cpp 12225 c) + (s3rpp 12225 46)) := badd (sGlobal55_hz90 hc) sGlobal55_hz37 (by norm_num) (by norm_num)

theorem sGlobal55_hz96 {c : ℝ} (hc : B (31 / 50) (5 / 8) c) : B (-877125648106005204911 / 500000000000000000) (-1136632018497481444871 / 1000000000000000000) (if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) := bweaken (bfirst (sGlobal55_hz95 hc) (sGlobal55_hz76 hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem sGlobal55_hz97 {c : ℝ} (hc : B (31 / 50) (5 / 8) c) : B (1969533066580415772647 / 500000000000000000) (4000867705210722588491 / 1000000000000000000) ((s3Lam 12225 46 c)^2) := bsq (sGlobal55_hz94 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal55_hz98 {c : ℝ} (hc : B (31 / 50) (5 / 8) c) : B (486131350794016573 / 1000000000000000000) (122779604499803067 / 250000000000000000) ((s3c1 12225 46 c)^2) := bsq (sGlobal55_hz72 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal55_hz99 {c : ℝ} (hc : B (31 / 50) (5 / 8) c) : B (127220395500196933 / 250000000000000000) (513868649205983427 / 1000000000000000000) ((1 : ℝ) - ((s3c1 12225 46 c)^2)) := bsub (bpoint (1 : ℝ)) (sGlobal55_hz98 hc) (by norm_num) (by norm_num)

theorem sGlobal55_hz100 {c : ℝ} (hc : B (31 / 50) (5 / 8) c) : B (356679681927912643 / 500000000000000000) (14336926437782729 / 20000000000000000) (√((1 : ℝ) - ((s3c1 12225 46 c)^2))) := bsqrt (sGlobal55_hz99 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal55_hz101 {c : ℝ} (hc : B (31 / 50) (5 / 8) c) : B (2241084536858948999 / 1000000000000000000) (1126019569299887633 / 500000000000000000) (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))) := bmul pi_mem (sGlobal55_hz100 hc) (by norm_num) (by norm_num)

theorem sGlobal55_hz102 {c : ℝ} (hc : B (31 / 50) (5 / 8) c) : B (218638858537444194109 / 125000000000000000) (1785237298909859060139 / 1000000000000000000) (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2))))) := bdiv (sGlobal55_hz97 hc) (sGlobal55_hz101 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal55_hz103 {c : ℝ} (hc : B (31 / 50) (5 / 8) c) : B (-102808558249137139 / 20000000000000000) (162151320103094403817 / 250000000000000000) ((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) := badd (sGlobal55_hz96 hc) (sGlobal55_hz102 hc) (by norm_num) (by norm_num)

theorem sGlobal55_hz104 : B (3762781186094069 / 250000000000000000) (376278118609407 / 25000000000000000) ((s3e0 12225 46)^2) := bsq sGlobal55_hz16 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal55_hz105 {c : ℝ} (hc : B (31 / 50) (5 / 8) c) : B (-2562688393856240337 / 500000000000000000) (162155082884280497887 / 250000000000000000) (((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) := badd (sGlobal55_hz103 hc) sGlobal55_hz104 (by norm_num) (by norm_num)

theorem sGlobal55_hz106 {c : ℝ} (hc : B (31 / 50) (5 / 8) c) : B (33371696663534789457 / 1000000000000000000) (171779351247811565391 / 250000000000000000) ((((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) + (s3rs 12225 46 maskSlack)) := badd (sGlobal55_hz105 hc) sGlobal55_hz29 (by norm_num) (by norm_num)

theorem sGlobal55_hz107 {c : ℝ} (hc : B (31 / 50) (5 / 8) c) : B (33371696663534789457 / 1000000000000000000) (171779351247811565391 / 250000000000000000) (s3U 12225 46 maskSlack c) := by
    convert (sGlobal55_hz106 hc) using 1 <;>
      norm_num [s3U] <;> ring

theorem sGlobal55_hz108 {c : ℝ} (hc : B (31 / 50) (5 / 8) c) : B (-250137914356656874827 / 100000000000000000) (-30334885627999337127 / 12500000000000000) ((s3Cpp 12225 c) - (s3rpp 12225 46)) := bsub (sGlobal55_hz90 hc) sGlobal55_hz37 (by norm_num) (by norm_num)

theorem sGlobal55_hz109 {c : ℝ} (hc : B (31 / 50) (5 / 8) c) : B (-250137914356656874827 / 100000000000000000) (-30334885627999337127 / 12500000000000000) (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ)) := bweaken (bmin (sGlobal55_hz108 hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem sGlobal55_hz110 {c : ℝ} (hc : B (31 / 50) (5 / 8) c) : B (-1868962348376617055061 / 1000000000000000000) (-1809378626975204709627 / 1000000000000000000) ((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) := bmul (sGlobal55_hz76 hc) (sGlobal55_hz109 hc) (by norm_num) (by norm_num)

theorem sGlobal55_hz111 {c : ℝ} (hc : B (31 / 50) (5 / 8) c) : B (-1868977399501361431341 / 1000000000000000000) (-1809393678099949085903 / 1000000000000000000) (((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) := bsub (sGlobal55_hz110 hc) sGlobal55_hz104 (by norm_num) (by norm_num)

theorem sGlobal55_hz112 {c : ℝ} (hc : B (31 / 50) (5 / 8) c) : B (-1907474472955485701357 / 1000000000000000000) (-923945375775598178017 / 500000000000000000) ((((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) - (s3rs 12225 46 maskSlack)) := bsub (sGlobal55_hz111 hc) sGlobal55_hz29 (by norm_num) (by norm_num)

theorem sGlobal55_hz113 {c : ℝ} (hc : B (31 / 50) (5 / 8) c) : B (-1907474472955485701357 / 1000000000000000000) (-923945375775598178017 / 500000000000000000) (s3L 12225 46 maskSlack c) := by
    convert (sGlobal55_hz112 hc) using 1 <;>
      norm_num [s3L] <;> ring

theorem sGlobal55_hz114 {c : ℝ} (hc : B (31 / 50) (5 / 8) c) : B 0 (171779351247811565391 / 250000000000000000) |(s3U 12225 46 maskSlack c)| := bweaken (babs (sGlobal55_hz107 hc)) (by norm_num) (by norm_num)

theorem sGlobal55_hz115 {c : ℝ} (hc : B (31 / 50) (5 / 8) c) : B 0 (1907474472955485701357 / 1000000000000000000) |(s3L 12225 46 maskSlack c)| := bweaken (babs (sGlobal55_hz113 hc)) (by norm_num) (by norm_num)

theorem sGlobal55_hz116 {c : ℝ} (hc : B (31 / 50) (5 / 8) c) : B 0 (1907474472955485701357 / 1000000000000000000) (max |(s3U 12225 46 maskSlack c)| |(s3L 12225 46 maskSlack c)|) := bweaken (bmax (sGlobal55_hz114 hc) (sGlobal55_hz115 hc)) (by norm_num) (by norm_num)

theorem sGlobal55_hz117 {c : ℝ} (hc : B (31 / 50) (5 / 8) c) : B 0 (1907474472955485701357 / 1000000000000000000) (s3nks 12225 46 maskSlack c) := by
    convert (sGlobal55_hz116 hc) using 1 <;>
      norm_num [s3nks] <;> ring

theorem sGlobal55 {c : ℝ} (hc : B (31 / 50) (5 / 8) c) :
    0 < s3am 12225 46 ∧ 0 ≤ s3dm 12225 46 c ∧
    s3dm 12225 46 c ^ 2 ≤ 2 * s3ap 12225 46 ^ 2 ∧ s3c1 12225 46 c < 1 ∧
    0 ≤ s3Cpa 12225 c - s3r1 12225 46 ∧
    s3e0 12225 46 ≤ (s3Cpa 12225 c - s3r1 12225 46) / s3ap 12225 46 ∧
    s3nks 12225 46 maskSlack c ≤ 12225 * (156031 / 1000000) := by

  refine ⟨lt_of_lt_of_le (by norm_num) sGlobal55_hz14.1,
    le_trans (by norm_num) (sGlobal55_hz64 hc).1, ?_,
    lt_of_le_of_lt (sGlobal55_hz72 hc).2 (by norm_num), ?_, ?_,
    le_trans (sGlobal55_hz117 hc).2 (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (sGlobal55_hz64 hc).1) (sGlobal55_hz64 hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) sGlobal55_hz9.1 2
    nlinarith only [h1, h2]
  · linarith only [(sGlobal55_hz84 hc).1, sGlobal55_hz33.2]
  · have hap : 0 < s3ap 12225 46 := lt_of_lt_of_le (by norm_num) sGlobal55_hz9.1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul sGlobal55_hz16.2 sGlobal55_hz9.2 (le_trans (by norm_num) sGlobal55_hz9.1) (by norm_num)
    linarith only [h, (sGlobal55_hz84 hc).1, sGlobal55_hz33.2]

end BstLean.Part255
