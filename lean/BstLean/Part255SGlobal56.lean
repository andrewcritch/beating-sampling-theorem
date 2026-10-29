import BstLean.Part255SGlobal52
import BstLean.Part255Numeric10
namespace BstLean.Part255
open Real BstLean.Part130 BstLean.Part182 BstLean.Part197 BstLean.Part246
theorem sGlobal56_hz0 : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal56_hz1 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) ((√(23 : ℝ)) / (12225 : ℝ)) := bdiv sGlobal56_hz0 (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal56_hz2 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) maskSlack := by
    convert sGlobal56_hz1 using 1 <;>
      norm_num [maskSlack] <;> ring

theorem sGlobal56_hz3 : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal56_hz4 : B (6395294793910793 / 500000000000000000) (12790589587821587 / 1000000000000000000) (√((2 / 12225) : ℝ)) := bsqrt (bpoint ((2 / 12225) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal56_hz5 : B (7230130686979 / 62500000000000000) (23136418198333 / 200000000000000000) (√((2 / 149450625) : ℝ)) := bsqrt (bpoint ((2 / 149450625) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal56_hz6 : B (2211334438749598093 / 20000000000000000) (110566721937479904651 / 1000000000000000000) (√(12225 : ℝ)) := bsqrt (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal56_hz7 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))) := bmul sGlobal56_hz3 sGlobal56_hz4 (by norm_num) (by norm_num)

theorem sGlobal56_hz8 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) ((√(12225 : ℝ)) + ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := badd sGlobal56_hz6 sGlobal56_hz7 (by norm_num) (by norm_num)

theorem sGlobal56_hz9 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) (s3ap 12225 46) := by
    convert sGlobal56_hz8 using 1 <;>
      norm_num [s3ap, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal56_hz10 : B (163599182004089 / 1000000000000000000) (16359918200409 / 100000000000000000) ((2 : ℝ) / (12225 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal56_hz11 : B (1222499983640081799591 / 100000000000000000) (12224999836400817995911 / 1000000000000000000) ((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ))) := bsub (bpoint (12225 : ℝ)) sGlobal56_hz10 (by norm_num) (by norm_num)

theorem sGlobal56_hz12 : B (110566721197658827907 / 1000000000000000000) (27641680299414706977 / 250000000000000000) (√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) := bsqrt sGlobal56_hz11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal56_hz13 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) ((√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) - ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bsub sGlobal56_hz12 sGlobal56_hz7 (by norm_num) (by norm_num)

theorem sGlobal56_hz14 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) (s3am 12225 46) := by
    convert sGlobal56_hz13 using 1 <;>
      norm_num [s3am, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal56_hz15 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√((2 / 12225) : ℝ)) * (√(92 : ℝ))) := bmul sGlobal56_hz4 sGlobal56_hz3 (by norm_num) (by norm_num)

theorem sGlobal56_hz16 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) (s3e0 12225 46) := by
    convert sGlobal56_hz15 using 1 <;>
      norm_num [s3e0, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal56_hz17 : B (250196148528560847 / 500000000000000000) (100078459411424339 / 200000000000000000) (((1 / 2) : ℝ) + maskSlack) := badd (bpoint ((1 / 2) : ℝ)) sGlobal56_hz2 (by norm_num) (by norm_num)

theorem sGlobal56_hz18 : B (59827153232297998295487 / 800000000000000) (23930861292919199366019 / 320000000000000) ((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack)) := bmul (bpoint (149450625 : ℝ)) sGlobal56_hz17 (by norm_num) (by norm_num)

theorem sGlobal56_hz19 : B (1729554180017180009583 / 200000000000000000) (8647770900085900056557 / 1000000000000000000) (√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) := bsqrt sGlobal56_hz18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal56_hz20 : B (4328681281566262743499 / 500000000000000000) (8657362563132525495641 / 1000000000000000000) ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))) := badd sGlobal56_hz19 sGlobal56_hz3 (by norm_num) (by norm_num)

theorem sGlobal56_hz21 : B (110732771457999278473 / 1000000000000000000) (55366385728999643621 / 500000000000000000) ((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ)))) := bmul sGlobal56_hz4 sGlobal56_hz20 (by norm_num) (by norm_num)

theorem sGlobal56_hz22 : B (209099159 / 15625000000000000) (13382346177 / 1000000000000000000) ((2 : ℝ) / (149450625 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (149450625 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal56_hz23 : B (2452349334953899930479 / 200000000000000000) (12261746674769501594427 / 1000000000000000000) (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2) := bsq sGlobal56_hz21 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal56_hz24 : B (82045469362091 / 500000000000000000) (32818187747289 / 200000000000000000) (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2)) := bmul sGlobal56_hz22 sGlobal56_hz23 (by norm_num) (by norm_num)

theorem sGlobal56_hz25 : B (82045469362091 / 250000000000000000) (32818187747289 / 100000000000000000) ((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) := bmul (bpoint (2 : ℝ)) sGlobal56_hz24 (by norm_num) (by norm_num)

theorem sGlobal56_hz26 : B (117258080744995992792057 / 1000000000000000000) (58629040372497996396029 / 500000000000000000) (√(13749457500 : ℝ)) := bsqrt (bpoint (13749457500 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal56_hz27 : B (117304080744995992792057 / 1000000000000000000) (58652040372497996396029 / 500000000000000000) ((√(13749457500 : ℝ)) + (46 : ℝ)) := badd sGlobal56_hz26 (bpoint (46 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal56_hz28 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal56_hz25 sGlobal56_hz27 (by norm_num) (by norm_num)

theorem sGlobal56_hz29 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (s3rs 12225 46 maskSlack) := by
    convert sGlobal56_hz28 using 1 <;>
      norm_num [s3rs, s3pp, s3K, mA, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal56_hz30 : B (490797546012267 / 1000000000000000000) (49079754601227 / 100000000000000000) ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (3 : ℝ)) sGlobal56_hz10 (by norm_num) (by norm_num)

theorem sGlobal56_hz31 : B (490797546012267 / 500000000000000000) (49079754601227 / 50000000000000000) ((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal56_hz30 (by norm_num) (by norm_num)

theorem sGlobal56_hz32 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal56_hz31 sGlobal56_hz27 (by norm_num) (by norm_num)

theorem sGlobal56_hz33 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (s3r1 12225 46) := by
    convert sGlobal56_hz32 using 1 <;>
      norm_num [s3r1, mA] <;> ring

theorem sGlobal56_hz34 : B (163599182004089 / 500000000000000000) (16359918200409 / 50000000000000000) ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (2 : ℝ)) sGlobal56_hz10 (by norm_num) (by norm_num)

theorem sGlobal56_hz35 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal56_hz34 (by norm_num) (by norm_num)

theorem sGlobal56_hz36 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal56_hz35 sGlobal56_hz27 (by norm_num) (by norm_num)

theorem sGlobal56_hz37 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (s3rpp 12225 46) := by
    convert sGlobal56_hz36 using 1 <;>
      norm_num [s3rpp, mA] <;> ring

theorem sGlobal56_hz38 {c : ℝ} (hc : B (5 / 8) (63 / 100) c) : B (5 / 8) (63 / 100) c := hc

theorem sGlobal56_hz39 : B (142980208281654933 / 200000000000000000) (714901041408274673 / 1000000000000000000) (kdot ((5 / 8))) := by
    constructor
    · apply bkdot_lower (q := (480384461415261401 / 1000000000000000000)) (a := (55979049616116561 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (2401922307076307 / 5000000000000000)) (a := (111958099232233119 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal56_hz40 : B (25 / 64) (25 / 64) (((5 / 8) : ℝ)^2) := bsq (bpoint ((5 / 8) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal56_hz41 : B (39 / 64) (39 / 64) ((1 : ℝ) - (((5 / 8) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal56_hz40 (by norm_num) (by norm_num)

theorem sGlobal56_hz42 : B (31224989991991991 / 40000000000000000) (24394523431243743 / 31250000000000000) (√((1 : ℝ) - (((5 / 8) : ℝ)^2))) := bsqrt sGlobal56_hz41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal56_hz43 : B (15530035953814021 / 62500000000000000) (248480575261024337 / 1000000000000000000) ((√((1 : ℝ) - (((5 / 8) : ℝ)^2))) / Real.pi) := bdiv sGlobal56_hz42 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal56_hz44 : B (89362630176034333 / 200000000000000000) (446813150880171671 / 1000000000000000000) (((5 / 8) : ℝ) * (kdot ((5 / 8)))) := bmul (bpoint ((5 / 8) : ℝ)) sGlobal56_hz39 (by norm_num) (by norm_num)

theorem sGlobal56_hz45 : B (695293726141196001 / 1000000000000000000) (86911715767649501 / 125000000000000000) (((√((1 : ℝ) - (((5 / 8) : ℝ)^2))) / Real.pi) + (((5 / 8) : ℝ) * (kdot ((5 / 8))))) := badd sGlobal56_hz43 sGlobal56_hz44 (by norm_num) (by norm_num)

theorem sGlobal56_hz46 : B (695293726141196001 / 1000000000000000000) (86911715767649501 / 125000000000000000) (kappa ((5 / 8))) := by rw [kappa_eq]; exact sGlobal56_hz45

theorem sGlobal56_hz47 : B (716945125200852751 / 1000000000000000000) (716945125200852757 / 1000000000000000000) (kdot ((63 / 100))) := by
    constructor
    · apply bkdot_lower (q := (119109682916281739 / 250000000000000000)) (a := (444621557615889849 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (95287746333025391 / 200000000000000000)) (a := (444621557615889841 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal56_hz48 : B (3969 / 10000) (3969 / 10000) (((63 / 100) : ℝ)^2) := bsq (bpoint ((63 / 100) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal56_hz49 : B (6031 / 10000) (6031 / 10000) ((1 : ℝ) - (((63 / 100) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal56_hz48 (by norm_num) (by norm_num)

theorem sGlobal56_hz50 : B (776595132614156937 / 1000000000000000000) (388297566307078469 / 500000000000000000) (√((1 : ℝ) - (((63 / 100) : ℝ)^2))) := bsqrt sGlobal56_hz49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal56_hz51 : B (247197908273298117 / 1000000000000000000) (123598954136649059 / 500000000000000000) ((√((1 : ℝ) - (((63 / 100) : ℝ)^2))) / Real.pi) := bdiv sGlobal56_hz50 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal56_hz52 : B (451675428876537233 / 1000000000000000000) (451675428876537237 / 1000000000000000000) (((63 / 100) : ℝ) * (kdot ((63 / 100)))) := bmul (bpoint ((63 / 100) : ℝ)) sGlobal56_hz47 (by norm_num) (by norm_num)

theorem sGlobal56_hz53 : B (13977466742996707 / 20000000000000000) (139774667429967071 / 200000000000000000) (((√((1 : ℝ) - (((63 / 100) : ℝ)^2))) / Real.pi) + (((63 / 100) : ℝ) * (kdot ((63 / 100))))) := badd sGlobal56_hz51 sGlobal56_hz52 (by norm_num) (by norm_num)

theorem sGlobal56_hz54 : B (13977466742996707 / 20000000000000000) (139774667429967071 / 200000000000000000) (kappa ((63 / 100))) := by rw [kappa_eq]; exact sGlobal56_hz53

theorem sGlobal56_hz55 {c : ℝ} (hc : B (5 / 8) (63 / 100) c) : B (695293726141196001 / 1000000000000000000) (139774667429967071 / 200000000000000000) (kappa c) := bkappa (sGlobal56_hz38 hc) (by norm_num) (by norm_num) sGlobal56_hz46.1 sGlobal56_hz54.2

theorem sGlobal56_hz56 : B 24450 24450 ((2 : ℝ) * (12225 : ℝ)) := bmul (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal56_hz57 {c : ℝ} (hc : B (5 / 8) (63 / 100) c) : B (60225332570032929 / 200000000000000000) (304706273858803999 / 1000000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (sGlobal56_hz55 hc) (by norm_num) (by norm_num)

theorem sGlobal56_hz58 {c : ℝ} (hc : B (5 / 8) (63 / 100) c) : B (29450187626746102281 / 4000000000000000) (149001367916955155511 / 20000000000000000) (((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) := bmul sGlobal56_hz56 (sGlobal56_hz57 hc) (by norm_num) (by norm_num)

theorem sGlobal56_hz59 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (4 : ℝ)) sGlobal56_hz10 (by norm_num) (by norm_num)

theorem sGlobal56_hz60 {c : ℝ} (hc : B (5 / 8) (63 / 100) c) : B (736254625228979755389 / 100000000000000000) (3725033870725514879597 / 500000000000000000) ((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bsub (sGlobal56_hz58 hc) sGlobal56_hz59 (by norm_num) (by norm_num)

theorem sGlobal56_hz61 {c : ℝ} (hc : B (5 / 8) (63 / 100) c) : B (42902640513987590557 / 500000000000000000) (2157844373073946591 / 25000000000000000) (√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) := bsqrt (sGlobal56_hz60 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal56_hz62 : B (30670756373515103 / 125000000000000000) (122683025494060423 / 500000000000000000) ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal56_hz7 (by norm_num) (by norm_num)

theorem sGlobal56_hz63 {c : ℝ} (hc : B (5 / 8) (63 / 100) c) : B (21389978744246765067 / 250000000000000000) (2689637777249054463 / 31250000000000000) ((√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) - ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))))) := bsub (sGlobal56_hz61 hc) sGlobal56_hz62 (by norm_num) (by norm_num)

theorem sGlobal56_hz64 {c : ℝ} (hc : B (5 / 8) (63 / 100) c) : B (21389978744246765067 / 250000000000000000) (2689637777249054463 / 31250000000000000) (s3dm 12225 46 c) := by
    convert (sGlobal56_hz63 hc) using 1 <;>
      norm_num [s3dm, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal56_hz65 : B (6126072185528622723889 / 500000000000000000) (2450428874211449090087 / 200000000000000000) ((s3ap 12225 46)^2) := bsq sGlobal56_hz9 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal56_hz66 : B (6126072185528622723889 / 250000000000000000) (2450428874211449090087 / 100000000000000000) ((2 : ℝ) * ((s3ap 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal56_hz65 (by norm_num) (by norm_num)

theorem sGlobal56_hz67 {c : ℝ} (hc : B (5 / 8) (63 / 100) c) : B (7320499050869254665789 / 1000000000000000000) (7407771005752559937017 / 1000000000000000000) ((s3dm 12225 46 c)^2) := bsq (sGlobal56_hz64 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal56_hz68 {c : ℝ} (hc : B (5 / 8) (63 / 100) c) : B (17096517736361930958539 / 1000000000000000000) (17183789691245236235081 / 1000000000000000000) (((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) := bsub sGlobal56_hz66 (sGlobal56_hz67 hc) (by norm_num) (by norm_num)

theorem sGlobal56_hz69 : B (1524735695971823534271 / 125000000000000000) (609894278388729413841 / 50000000000000000) ((s3am 12225 46)^2) := bsq sGlobal56_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal56_hz70 : B (1524735695971823534271 / 62500000000000000) (609894278388729413841 / 25000000000000000) ((2 : ℝ) * ((s3am 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal56_hz69 (by norm_num) (by norm_num)

theorem sGlobal56_hz71 {c : ℝ} (hc : B (5 / 8) (63 / 100) c) : B (175199603666648647 / 250000000000000000) (140875150826491057 / 200000000000000000) ((((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) / ((2 : ℝ) * ((s3am 12225 46)^2))) := bdiv (sGlobal56_hz68 hc) sGlobal56_hz70 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal56_hz72 {c : ℝ} (hc : B (5 / 8) (63 / 100) c) : B (175199603666648647 / 250000000000000000) (140875150826491057 / 200000000000000000) (s3c1 12225 46 c) := by
    convert (sGlobal56_hz71 hc) using 1 <;>
      norm_num [s3c1] <;> ring

theorem sGlobal56_hz73 {c : ℝ} (hc : B (5 / 8) (63 / 100) c) : B (142980208281654933 / 200000000000000000) (716945125200852757 / 1000000000000000000) (kdot c) := bkdot (sGlobal56_hz38 hc) sGlobal56_hz39.1 sGlobal56_hz47.2

theorem sGlobal56_hz74 : B (93396594493856599 / 125000000000000000) (149434551190170559 / 200000000000000000) (kdot ((175199603666648647 / 250000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (419426169323931461 / 1000000000000000000)) (a := (198570053133038659 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (20971308466196573 / 50000000000000000)) (a := (99285026566519329 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal56_hz75 : B (748772967853183563 / 1000000000000000000) (374386483926591783 / 500000000000000000) (kdot ((140875150826491057 / 200000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (208236739785694481 / 500000000000000000)) (a := (394626499287802669 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (416473479571388961 / 1000000000000000000)) (a := (394626499287802667 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal56_hz76 {c : ℝ} (hc : B (5 / 8) (63 / 100) c) : B (93396594493856599 / 125000000000000000) (374386483926591783 / 500000000000000000) (kdot (s3c1 12225 46 c)) := bkdot (sGlobal56_hz72 hc) sGlobal56_hz74.1 sGlobal56_hz75.2

theorem sGlobal56_hz77 {c : ℝ} (hc : B (5 / 8) (63 / 100) c) : B (25 / 64) (3969 / 10000) (c^2) := bsq (sGlobal56_hz38 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal56_hz78 {c : ℝ} (hc : B (5 / 8) (63 / 100) c) : B (6031 / 10000) (39 / 64) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (sGlobal56_hz77 hc) (by norm_num) (by norm_num)

theorem sGlobal56_hz79 {c : ℝ} (hc : B (5 / 8) (63 / 100) c) : B (776595132614156937 / 1000000000000000000) (24394523431243743 / 31250000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (sGlobal56_hz78 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal56_hz80 : B (39119999999999765769 / 1600000000000000) (3912000000000000489 / 160000000000000) ((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (149450625 : ℝ)) sGlobal56_hz10 (by norm_num) (by norm_num)

theorem sGlobal56_hz81 {c : ℝ} (hc : B (5 / 8) (63 / 100) c) : B (555188669058457963 / 1000000000000000000) (559665108980101809 / 1000000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (sGlobal56_hz79 hc) (sGlobal56_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal56_hz82 {c : ℝ} (hc : B (5 / 8) (63 / 100) c) : B (13574362958479215918851 / 1000000000000000000) (13683811914563490940527 / 1000000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) := bmul sGlobal56_hz80 (sGlobal56_hz81 hc) (by norm_num) (by norm_num)

theorem sGlobal56_hz83 {c : ℝ} (hc : B (5 / 8) (63 / 100) c) : B (271487259169584318377 / 40000000000000000) (855238244660218183783 / 125000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) / (2 : ℝ)) := bdiv (sGlobal56_hz82 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal56_hz84 {c : ℝ} (hc : B (5 / 8) (63 / 100) c) : B (271487259169584318377 / 40000000000000000) (855238244660218183783 / 125000000000000000) (s3Cpa 12225 c) := by
    convert (sGlobal56_hz83 hc) using 1 <;>
      norm_num [s3Cpa, mA] <;> ring

theorem sGlobal56_hz85 {c : ℝ} (hc : B (5 / 8) (63 / 100) c) : B (247197908273298117 / 1000000000000000000) (248480575261024337 / 1000000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (sGlobal56_hz79 hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal56_hz86 {c : ℝ} (hc : B (5 / 8) (63 / 100) c) : B (89362630176034333 / 200000000000000000) (451675428876537237 / 1000000000000000000) (c * (kdot c)) := bmul (sGlobal56_hz38 hc) (sGlobal56_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal56_hz87 {c : ℝ} (hc : B (5 / 8) (63 / 100) c) : B (-2555969007540489 / 12500000000000000) (-3098946494049177 / 15625000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (sGlobal56_hz85 hc) (sGlobal56_hz86 hc) (by norm_num) (by norm_num)

theorem sGlobal56_hz88 {c : ℝ} (hc : B (5 / 8) (63 / 100) c) : B (-999895075749839421787 / 200000000000000000) (-2424615736944061567413 / 500000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) := bmul sGlobal56_hz80 (sGlobal56_hz87 hc) (by norm_num) (by norm_num)

theorem sGlobal56_hz89 {c : ℝ} (hc : B (5 / 8) (63 / 100) c) : B (-624934422343649638617 / 250000000000000000) (-2424615736944061567413 / 1000000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) / (2 : ℝ)) := bdiv (sGlobal56_hz88 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal56_hz90 {c : ℝ} (hc : B (5 / 8) (63 / 100) c) : B (-624934422343649638617 / 250000000000000000) (-2424615736944061567413 / 1000000000000000000) (s3Cpp 12225 c) := by
    convert (sGlobal56_hz89 hc) using 1 <;>
      norm_num [s3Cpp, mA] <;> ring

theorem sGlobal56_hz91 {c : ℝ} (hc : B (5 / 8) (63 / 100) c) : B (3451163294586672833913 / 500000000000000000) (695705106721548388249 / 100000000000000000) ((s3Cpa 12225 c) + (s3r1 12225 46)) := badd (sGlobal56_hz84 hc) sGlobal56_hz33 (by norm_num) (by norm_num)

theorem sGlobal56_hz92 {c : ℝ} (hc : B (5 / 8) (63 / 100) c) : B (62496144684729033981 / 1000000000000000000) (31495819884684689219 / 500000000000000000) (((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) := bdiv (sGlobal56_hz91 hc) sGlobal56_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal56_hz93 {c : ℝ} (hc : B (5 / 8) (63 / 100) c) : B (62618827710223094393 / 1000000000000000000) (63114322794863438861 / 1000000000000000000) ((((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) + (s3e0 12225 46)) := badd (sGlobal56_hz92 hc) sGlobal56_hz16 (by norm_num) (by norm_num)

theorem sGlobal56_hz94 {c : ℝ} (hc : B (5 / 8) (63 / 100) c) : B (62618827710223094393 / 1000000000000000000) (63114322794863438861 / 1000000000000000000) (s3Lam 12225 46 c) := by
    convert (sGlobal56_hz93 hc) using 1 <;>
      norm_num [s3Lam] <;> ring

theorem sGlobal56_hz95 {c : ℝ} (hc : B (5 / 8) (63 / 100) c) : B (-605743570688026687217 / 250000000000000000) (-469570466064313858519 / 200000000000000000) ((s3Cpp 12225 c) + (s3rpp 12225 46)) := badd (sGlobal56_hz90 hc) sGlobal56_hz37 (by norm_num) (by norm_num)

theorem sGlobal56_hz96 {c : ℝ} (hc : B (5 / 8) (63 / 100) c) : B (-113391102795514608421 / 62500000000000000) (-1173926165160784646297 / 1000000000000000000) (if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) := bweaken (bfirst (sGlobal56_hz95 hc) (sGlobal56_hz76 hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem sGlobal56_hz97 {c : ℝ} (hc : B (5 / 8) (63 / 100) c) : B (122534924493831364463 / 31250000000000000) (3983417741854218684409 / 1000000000000000000) ((s3Lam 12225 46 c)^2) := bsq (sGlobal56_hz94 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal56_hz98 {c : ℝ} (hc : B (5 / 8) (63 / 100) c) : B (15347450562475383 / 31250000000000000) (496145203009665099 / 1000000000000000000) ((s3c1 12225 46 c)^2) := bsq (sGlobal56_hz72 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal56_hz99 {c : ℝ} (hc : B (5 / 8) (63 / 100) c) : B (503854796990334901 / 1000000000000000000) (15902549437524617 / 31250000000000000) ((1 : ℝ) - ((s3c1 12225 46 c)^2)) := bsub (bpoint (1 : ℝ)) (sGlobal56_hz98 hc) (by norm_num) (by norm_num)

theorem sGlobal56_hz100 {c : ℝ} (hc : B (5 / 8) (63 / 100) c) : B (70982730082065377 / 100000000000000000) (142671872771165059 / 200000000000000000) (√((1 : ℝ) - ((s3c1 12225 46 c)^2))) := bsqrt (sGlobal56_hz99 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal56_hz101 {c : ℝ} (hc : B (5 / 8) (63 / 100) c) : B (139374264598477381 / 62500000000000000) (560271134214737257 / 250000000000000000) (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))) := bmul pi_mem (sGlobal56_hz100 hc) (by norm_num) (by norm_num)

theorem sGlobal56_hz102 {c : ℝ} (hc : B (5 / 8) (63 / 100) c) : B (1749651795508949937141 / 1000000000000000000) (446573852036325856789 / 250000000000000000) (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2))))) := bdiv (sGlobal56_hz97 hc) (sGlobal56_hz101 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal56_hz103 {c : ℝ} (hc : B (5 / 8) (63 / 100) c) : B (-12921169843856759519 / 200000000000000000) (612369242984518780859 / 1000000000000000000) ((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) := badd (sGlobal56_hz96 hc) (sGlobal56_hz102 hc) (by norm_num) (by norm_num)

theorem sGlobal56_hz104 : B (3762781186094069 / 250000000000000000) (376278118609407 / 25000000000000000) ((s3e0 12225 46)^2) := bsq sGlobal56_hz16 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal56_hz105 {c : ℝ} (hc : B (5 / 8) (63 / 100) c) : B (-64590798094539421319 / 1000000000000000000) (612384294109263157139 / 1000000000000000000) (((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) := badd (sGlobal56_hz103 hc) sGlobal56_hz104 (by norm_num) (by norm_num)

theorem sGlobal56_hz106 {c : ℝ} (hc : B (5 / 8) (63 / 100) c) : B (-6523431160823037797 / 250000000000000000) (130176273512677485431 / 200000000000000000) ((((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) + (s3rs 12225 46 maskSlack)) := badd (sGlobal56_hz105 hc) sGlobal56_hz29 (by norm_num) (by norm_num)

theorem sGlobal56_hz107 {c : ℝ} (hc : B (5 / 8) (63 / 100) c) : B (-6523431160823037797 / 250000000000000000) (130176273512677485431 / 200000000000000000) (s3U 12225 46 maskSlack c) := by
    convert (sGlobal56_hz106 hc) using 1 <;>
      norm_num [s3U] <;> ring

theorem sGlobal56_hz108 {c : ℝ} (hc : B (5 / 8) (63 / 100) c) : B (-1288250547998545414643 / 500000000000000000) (-2501379143566553373013 / 1000000000000000000) ((s3Cpp 12225 c) - (s3rpp 12225 46)) := bsub (sGlobal56_hz90 hc) sGlobal56_hz37 (by norm_num) (by norm_num)

theorem sGlobal56_hz109 {c : ℝ} (hc : B (5 / 8) (63 / 100) c) : B (-1288250547998545414643 / 500000000000000000) (-2501379143566553373013 / 1000000000000000000) (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ)) := bweaken (bmin (sGlobal56_hz108 hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem sGlobal56_hz110 {c : ℝ} (hc : B (5 / 8) (63 / 100) c) : B (-1929214372326721916499 / 1000000000000000000) (-1868962348376605552079 / 1000000000000000000) ((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) := bmul (sGlobal56_hz76 hc) (sGlobal56_hz109 hc) (by norm_num) (by norm_num)

theorem sGlobal56_hz111 {c : ℝ} (hc : B (5 / 8) (63 / 100) c) : B (-1929229423451466292779 / 1000000000000000000) (-373795479900269985671 / 200000000000000000) (((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) := bsub (sGlobal56_hz110 hc) sGlobal56_hz104 (by norm_num) (by norm_num)

theorem sGlobal56_hz112 {c : ℝ} (hc : B (5 / 8) (63 / 100) c) : B (-393545299381118112559 / 200000000000000000) (-953737236476298599243 / 500000000000000000) ((((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) - (s3rs 12225 46 maskSlack)) := bsub (sGlobal56_hz111 hc) sGlobal56_hz29 (by norm_num) (by norm_num)

theorem sGlobal56_hz113 {c : ℝ} (hc : B (5 / 8) (63 / 100) c) : B (-393545299381118112559 / 200000000000000000) (-953737236476298599243 / 500000000000000000) (s3L 12225 46 maskSlack c) := by
    convert (sGlobal56_hz112 hc) using 1 <;>
      norm_num [s3L] <;> ring

theorem sGlobal56_hz114 {c : ℝ} (hc : B (5 / 8) (63 / 100) c) : B 0 (130176273512677485431 / 200000000000000000) |(s3U 12225 46 maskSlack c)| := bweaken (babs (sGlobal56_hz107 hc)) (by norm_num) (by norm_num)

theorem sGlobal56_hz115 {c : ℝ} (hc : B (5 / 8) (63 / 100) c) : B 0 (393545299381118112559 / 200000000000000000) |(s3L 12225 46 maskSlack c)| := bweaken (babs (sGlobal56_hz113 hc)) (by norm_num) (by norm_num)

theorem sGlobal56_hz116 {c : ℝ} (hc : B (5 / 8) (63 / 100) c) : B 0 (393545299381118112559 / 200000000000000000) (max |(s3U 12225 46 maskSlack c)| |(s3L 12225 46 maskSlack c)|) := bweaken (bmax (sGlobal56_hz114 hc) (sGlobal56_hz115 hc)) (by norm_num) (by norm_num)

theorem sGlobal56_hz117 {c : ℝ} (hc : B (5 / 8) (63 / 100) c) : B 0 (393545299381118112559 / 200000000000000000) (s3nks 12225 46 maskSlack c) := by
    convert (sGlobal56_hz116 hc) using 1 <;>
      norm_num [s3nks] <;> ring

theorem sGlobal56 {c : ℝ} (hc : B (5 / 8) (63 / 100) c) :
    0 < s3am 12225 46 ∧ 0 ≤ s3dm 12225 46 c ∧
    s3dm 12225 46 c ^ 2 ≤ 2 * s3ap 12225 46 ^ 2 ∧ s3c1 12225 46 c < 1 ∧
    0 ≤ s3Cpa 12225 c - s3r1 12225 46 ∧
    s3e0 12225 46 ≤ (s3Cpa 12225 c - s3r1 12225 46) / s3ap 12225 46 ∧
    s3nks 12225 46 maskSlack c ≤ 12225 * (503 / 3125) := by

  refine ⟨lt_of_lt_of_le (by norm_num) sGlobal56_hz14.1,
    le_trans (by norm_num) (sGlobal56_hz64 hc).1, ?_,
    lt_of_le_of_lt (sGlobal56_hz72 hc).2 (by norm_num), ?_, ?_,
    le_trans (sGlobal56_hz117 hc).2 (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (sGlobal56_hz64 hc).1) (sGlobal56_hz64 hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) sGlobal56_hz9.1 2
    nlinarith only [h1, h2]
  · linarith only [(sGlobal56_hz84 hc).1, sGlobal56_hz33.2]
  · have hap : 0 < s3ap 12225 46 := lt_of_lt_of_le (by norm_num) sGlobal56_hz9.1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul sGlobal56_hz16.2 sGlobal56_hz9.2 (le_trans (by norm_num) sGlobal56_hz9.1) (by norm_num)
    linarith only [h, (sGlobal56_hz84 hc).1, sGlobal56_hz33.2]

end BstLean.Part255
