import BstLean.Part255SGlobal24
import BstLean.Part255Numeric10
namespace BstLean.Part255
open Real BstLean.Part130 BstLean.Part182 BstLean.Part197 BstLean.Part246
theorem sGlobal28_hz0 : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal28_hz1 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) ((√(23 : ℝ)) / (12225 : ℝ)) := bdiv sGlobal28_hz0 (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal28_hz2 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) maskSlack := by
    convert sGlobal28_hz1 using 1 <;>
      norm_num [maskSlack] <;> ring

theorem sGlobal28_hz3 : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal28_hz4 : B (6395294793910793 / 500000000000000000) (12790589587821587 / 1000000000000000000) (√((2 / 12225) : ℝ)) := bsqrt (bpoint ((2 / 12225) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal28_hz5 : B (7230130686979 / 62500000000000000) (23136418198333 / 200000000000000000) (√((2 / 149450625) : ℝ)) := bsqrt (bpoint ((2 / 149450625) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal28_hz6 : B (2211334438749598093 / 20000000000000000) (110566721937479904651 / 1000000000000000000) (√(12225 : ℝ)) := bsqrt (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal28_hz7 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))) := bmul sGlobal28_hz3 sGlobal28_hz4 (by norm_num) (by norm_num)

theorem sGlobal28_hz8 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) ((√(12225 : ℝ)) + ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := badd sGlobal28_hz6 sGlobal28_hz7 (by norm_num) (by norm_num)

theorem sGlobal28_hz9 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) (s3ap 12225 46) := by
    convert sGlobal28_hz8 using 1 <;>
      norm_num [s3ap, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal28_hz10 : B (163599182004089 / 1000000000000000000) (16359918200409 / 100000000000000000) ((2 : ℝ) / (12225 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal28_hz11 : B (1222499983640081799591 / 100000000000000000) (12224999836400817995911 / 1000000000000000000) ((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ))) := bsub (bpoint (12225 : ℝ)) sGlobal28_hz10 (by norm_num) (by norm_num)

theorem sGlobal28_hz12 : B (110566721197658827907 / 1000000000000000000) (27641680299414706977 / 250000000000000000) (√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) := bsqrt sGlobal28_hz11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal28_hz13 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) ((√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) - ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bsub sGlobal28_hz12 sGlobal28_hz7 (by norm_num) (by norm_num)

theorem sGlobal28_hz14 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) (s3am 12225 46) := by
    convert sGlobal28_hz13 using 1 <;>
      norm_num [s3am, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal28_hz15 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√((2 / 12225) : ℝ)) * (√(92 : ℝ))) := bmul sGlobal28_hz4 sGlobal28_hz3 (by norm_num) (by norm_num)

theorem sGlobal28_hz16 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) (s3e0 12225 46) := by
    convert sGlobal28_hz15 using 1 <;>
      norm_num [s3e0, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal28_hz17 : B (250196148528560847 / 500000000000000000) (100078459411424339 / 200000000000000000) (((1 / 2) : ℝ) + maskSlack) := badd (bpoint ((1 / 2) : ℝ)) sGlobal28_hz2 (by norm_num) (by norm_num)

theorem sGlobal28_hz18 : B (59827153232297998295487 / 800000000000000) (23930861292919199366019 / 320000000000000) ((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack)) := bmul (bpoint (149450625 : ℝ)) sGlobal28_hz17 (by norm_num) (by norm_num)

theorem sGlobal28_hz19 : B (1729554180017180009583 / 200000000000000000) (8647770900085900056557 / 1000000000000000000) (√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) := bsqrt sGlobal28_hz18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal28_hz20 : B (4328681281566262743499 / 500000000000000000) (8657362563132525495641 / 1000000000000000000) ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))) := badd sGlobal28_hz19 sGlobal28_hz3 (by norm_num) (by norm_num)

theorem sGlobal28_hz21 : B (110732771457999278473 / 1000000000000000000) (55366385728999643621 / 500000000000000000) ((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ)))) := bmul sGlobal28_hz4 sGlobal28_hz20 (by norm_num) (by norm_num)

theorem sGlobal28_hz22 : B (209099159 / 15625000000000000) (13382346177 / 1000000000000000000) ((2 : ℝ) / (149450625 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (149450625 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal28_hz23 : B (2452349334953899930479 / 200000000000000000) (12261746674769501594427 / 1000000000000000000) (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2) := bsq sGlobal28_hz21 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal28_hz24 : B (82045469362091 / 500000000000000000) (32818187747289 / 200000000000000000) (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2)) := bmul sGlobal28_hz22 sGlobal28_hz23 (by norm_num) (by norm_num)

theorem sGlobal28_hz25 : B (82045469362091 / 250000000000000000) (32818187747289 / 100000000000000000) ((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) := bmul (bpoint (2 : ℝ)) sGlobal28_hz24 (by norm_num) (by norm_num)

theorem sGlobal28_hz26 : B (117258080744995992792057 / 1000000000000000000) (58629040372497996396029 / 500000000000000000) (√(13749457500 : ℝ)) := bsqrt (bpoint (13749457500 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal28_hz27 : B (117304080744995992792057 / 1000000000000000000) (58652040372497996396029 / 500000000000000000) ((√(13749457500 : ℝ)) + (46 : ℝ)) := badd sGlobal28_hz26 (bpoint (46 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal28_hz28 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal28_hz25 sGlobal28_hz27 (by norm_num) (by norm_num)

theorem sGlobal28_hz29 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (s3rs 12225 46 maskSlack) := by
    convert sGlobal28_hz28 using 1 <;>
      norm_num [s3rs, s3pp, s3K, mA, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal28_hz30 : B (490797546012267 / 1000000000000000000) (49079754601227 / 100000000000000000) ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (3 : ℝ)) sGlobal28_hz10 (by norm_num) (by norm_num)

theorem sGlobal28_hz31 : B (490797546012267 / 500000000000000000) (49079754601227 / 50000000000000000) ((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal28_hz30 (by norm_num) (by norm_num)

theorem sGlobal28_hz32 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal28_hz31 sGlobal28_hz27 (by norm_num) (by norm_num)

theorem sGlobal28_hz33 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (s3r1 12225 46) := by
    convert sGlobal28_hz32 using 1 <;>
      norm_num [s3r1, mA] <;> ring

theorem sGlobal28_hz34 : B (163599182004089 / 500000000000000000) (16359918200409 / 50000000000000000) ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (2 : ℝ)) sGlobal28_hz10 (by norm_num) (by norm_num)

theorem sGlobal28_hz35 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal28_hz34 (by norm_num) (by norm_num)

theorem sGlobal28_hz36 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal28_hz35 sGlobal28_hz27 (by norm_num) (by norm_num)

theorem sGlobal28_hz37 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (s3rpp 12225 46) := by
    convert sGlobal28_hz36 using 1 <;>
      norm_num [s3rpp, mA] <;> ring

theorem sGlobal28_hz38 {c : ℝ} (hc : B (97 / 200) (49 / 100) c) : B (97 / 200) (49 / 100) c := hc

theorem sGlobal28_hz39 : B (330590201135817737 / 500000000000000000) (661180402271775659 / 1000000000000000000) (kdot ((97 / 200))) := by
    constructor
    · apply bkdot_lower (q := (117779683613320477 / 200000000000000000)) (a := (106443315911567899 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (36806151129162649 / 62500000000000000)) (a := (106443315911523859 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal28_hz40 : B (9409 / 40000) (9409 / 40000) (((97 / 200) : ℝ)^2) := bsq (bpoint ((97 / 200) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal28_hz41 : B (30591 / 40000) (30591 / 40000) ((1 : ℝ) - (((97 / 200) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal28_hz40 (by norm_num) (by norm_num)

theorem sGlobal28_hz42 : B (43725707541445227 / 50000000000000000) (874514150828904541 / 1000000000000000000) (√((1 : ℝ) - (((97 / 200) : ℝ)^2))) := bsqrt sGlobal28_hz41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal28_hz43 : B (34795812477057869 / 125000000000000000) (139183249908231477 / 500000000000000000) ((√((1 : ℝ) - (((97 / 200) : ℝ)^2))) / Real.pi) := bdiv sGlobal28_hz42 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal28_hz44 : B (80168123775435801 / 250000000000000000) (64134499020362239 / 200000000000000000) (((97 / 200) : ℝ) * (kdot ((97 / 200)))) := bmul (bpoint ((97 / 200) : ℝ)) sGlobal28_hz39 (by norm_num) (by norm_num)

theorem sGlobal28_hz45 : B (149759748729551539 / 250000000000000000) (599038994918274149 / 1000000000000000000) (((√((1 : ℝ) - (((97 / 200) : ℝ)^2))) / Real.pi) + (((97 / 200) : ℝ) * (kdot ((97 / 200))))) := badd sGlobal28_hz43 sGlobal28_hz44 (by norm_num) (by norm_num)

theorem sGlobal28_hz46 : B (149759748729551539 / 250000000000000000) (599038994918274149 / 1000000000000000000) (kappa ((97 / 200))) := by rw [kappa_eq]; exact sGlobal28_hz45

theorem sGlobal28_hz47 : B (331501615486170743 / 500000000000000000) (331501615486221571 / 500000000000000000) (kdot ((49 / 100))) := by
    constructor
    · apply bkdot_lower (q := (117009722535288643 / 200000000000000000)) (a := (529353286930394177 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (292524306338221607 / 500000000000000000)) (a := (529353286930234499 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal28_hz48 : B (2401 / 10000) (2401 / 10000) (((49 / 100) : ℝ)^2) := bsq (bpoint ((49 / 100) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal28_hz49 : B (7599 / 10000) (7599 / 10000) ((1 : ℝ) - (((49 / 100) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal28_hz48 (by norm_num) (by norm_num)

theorem sGlobal28_hz50 : B (87172243288790039 / 100000000000000000) (871722432887900391 / 1000000000000000000) (√((1 : ℝ) - (((49 / 100) : ℝ)^2))) := bsqrt sGlobal28_hz49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal28_hz51 : B (11099114735856187 / 40000000000000000) (69369467099101169 / 250000000000000000) ((√((1 : ℝ) - (((49 / 100) : ℝ)^2))) / Real.pi) := bdiv sGlobal28_hz50 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal28_hz52 : B (10152236974263979 / 31250000000000000) (16243579158824857 / 50000000000000000) (((49 / 100) : ℝ) * (kdot ((49 / 100)))) := bmul (bpoint ((49 / 100) : ℝ)) sGlobal28_hz47 (by norm_num) (by norm_num)

theorem sGlobal28_hz53 : B (602349451572852003 / 1000000000000000000) (75293681446612727 / 125000000000000000) (((√((1 : ℝ) - (((49 / 100) : ℝ)^2))) / Real.pi) + (((49 / 100) : ℝ) * (kdot ((49 / 100))))) := badd sGlobal28_hz51 sGlobal28_hz52 (by norm_num) (by norm_num)

theorem sGlobal28_hz54 : B (602349451572852003 / 1000000000000000000) (75293681446612727 / 125000000000000000) (kappa ((49 / 100))) := by rw [kappa_eq]; exact sGlobal28_hz53

theorem sGlobal28_hz55 {c : ℝ} (hc : B (97 / 200) (49 / 100) c) : B (149759748729551539 / 250000000000000000) (75293681446612727 / 125000000000000000) (kappa c) := bkappa (sGlobal28_hz38 hc) (by norm_num) (by norm_num) sGlobal28_hz46.1 sGlobal28_hz54.2

theorem sGlobal28_hz56 : B 24450 24450 ((2 : ℝ) * (12225 : ℝ)) := bmul (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal28_hz57 {c : ℝ} (hc : B (97 / 200) (49 / 100) c) : B (49706318553387273 / 125000000000000000) (100240251270448461 / 250000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (sGlobal28_hz55 hc) (by norm_num) (by norm_num)

theorem sGlobal28_hz58 {c : ℝ} (hc : B (97 / 200) (49 / 100) c) : B (24306389772606376497 / 2500000000000000) (49017482871249297429 / 5000000000000000) (((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) := bmul sGlobal28_hz56 (sGlobal28_hz57 hc) (by norm_num) (by norm_num)

theorem sGlobal28_hz59 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (4 : ℝ)) sGlobal28_hz10 (by norm_num) (by norm_num)

theorem sGlobal28_hz60 {c : ℝ} (hc : B (97 / 200) (49 / 100) c) : B (243063881366145564561 / 25000000000000000) (2450873979963282867361 / 250000000000000000) ((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bsub (sGlobal28_hz58 hc) sGlobal28_hz59 (by norm_num) (by norm_num)

theorem sGlobal28_hz61 {c : ℝ} (hc : B (97 / 200) (49 / 100) c) : B (98603018486483579771 / 1000000000000000000) (99012604853387891613 / 1000000000000000000) (√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) := bsqrt (sGlobal28_hz60 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal28_hz62 : B (30670756373515103 / 125000000000000000) (122683025494060423 / 500000000000000000) ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal28_hz7 (by norm_num) (by norm_num)

theorem sGlobal28_hz63 {c : ℝ} (hc : B (97 / 200) (49 / 100) c) : B (3934306097419818357 / 40000000000000000) (98767238802399770789 / 1000000000000000000) ((√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) - ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))))) := bsub (sGlobal28_hz61 hc) sGlobal28_hz62 (by norm_num) (by norm_num)

theorem sGlobal28_hz64 {c : ℝ} (hc : B (97 / 200) (49 / 100) c) : B (3934306097419818357 / 40000000000000000) (98767238802399770789 / 1000000000000000000) (s3dm 12225 46 c) := by
    convert (sGlobal28_hz63 hc) using 1 <;>
      norm_num [s3dm, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal28_hz65 : B (6126072185528622723889 / 500000000000000000) (2450428874211449090087 / 200000000000000000) ((s3ap 12225 46)^2) := bsq sGlobal28_hz9 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal28_hz66 : B (6126072185528622723889 / 250000000000000000) (2450428874211449090087 / 100000000000000000) ((2 : ℝ) * ((s3ap 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal28_hz65 (by norm_num) (by norm_num)

theorem sGlobal28_hz67 {c : ℝ} (hc : B (97 / 200) (49 / 100) c) : B (9674227792621725782707 / 1000000000000000000) (9754967460650262909171 / 1000000000000000000) ((s3dm 12225 46 c)^2) := bsq (sGlobal28_hz64 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal28_hz68 {c : ℝ} (hc : B (97 / 200) (49 / 100) c) : B (2949864256292845597277 / 200000000000000000) (14830060949492765118163 / 1000000000000000000) (((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) := bsub sGlobal28_hz66 (sGlobal28_hz67 hc) (by norm_num) (by norm_num)

theorem sGlobal28_hz69 : B (1524735695971823534271 / 125000000000000000) (609894278388729413841 / 50000000000000000) ((s3am 12225 46)^2) := bsq sGlobal28_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal28_hz70 : B (1524735695971823534271 / 62500000000000000) (609894278388729413841 / 25000000000000000) ((2 : ℝ) * ((s3am 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal28_hz69 (by norm_num) (by norm_num)

theorem sGlobal28_hz71 {c : ℝ} (hc : B (97 / 200) (49 / 100) c) : B (120917032706309687 / 200000000000000000) (607894739915911397 / 1000000000000000000) ((((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) / ((2 : ℝ) * ((s3am 12225 46)^2))) := bdiv (sGlobal28_hz68 hc) sGlobal28_hz70 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal28_hz72 {c : ℝ} (hc : B (97 / 200) (49 / 100) c) : B (120917032706309687 / 200000000000000000) (607894739915911397 / 1000000000000000000) (s3c1 12225 46 c) := by
    convert (sGlobal28_hz71 hc) using 1 <;>
      norm_num [s3c1] <;> ring

theorem sGlobal28_hz73 {c : ℝ} (hc : B (97 / 200) (49 / 100) c) : B (330590201135817737 / 500000000000000000) (331501615486221571 / 500000000000000000) (kdot c) := bkdot (sGlobal28_hz38 hc) sGlobal28_hz39.1 sGlobal28_hz47.2

theorem sGlobal28_hz74 : B (176665272865596639 / 250000000000000000) (706661091462386591 / 1000000000000000000) (kdot ((120917032706309687 / 200000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (248207613273383669 / 500000000000000000)) (a := (57596960004613417 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (496415226546767337 / 1000000000000000000)) (a := (460775680036907283 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal28_hz75 : B (707985745169627759 / 1000000000000000000) (353992872584813893 / 500000000000000000) (kdot ((607894739915911397 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (98764875959093471 / 200000000000000000)) (a := (114673729714824403 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (246912189897733677 / 500000000000000000)) (a := (458694918859297571 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal28_hz76 {c : ℝ} (hc : B (97 / 200) (49 / 100) c) : B (176665272865596639 / 250000000000000000) (353992872584813893 / 500000000000000000) (kdot (s3c1 12225 46 c)) := bkdot (sGlobal28_hz72 hc) sGlobal28_hz74.1 sGlobal28_hz75.2

theorem sGlobal28_hz77 {c : ℝ} (hc : B (97 / 200) (49 / 100) c) : B (9409 / 40000) (2401 / 10000) (c^2) := bsq (sGlobal28_hz38 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal28_hz78 {c : ℝ} (hc : B (97 / 200) (49 / 100) c) : B (7599 / 10000) (30591 / 40000) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (sGlobal28_hz77 hc) (by norm_num) (by norm_num)

theorem sGlobal28_hz79 {c : ℝ} (hc : B (97 / 200) (49 / 100) c) : B (87172243288790039 / 100000000000000000) (874514150828904541 / 1000000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (sGlobal28_hz78 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal28_hz80 : B (39119999999999765769 / 1600000000000000) (3912000000000000489 / 160000000000000) ((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (149450625 : ℝ)) sGlobal28_hz10 (by norm_num) (by norm_num)

theorem sGlobal28_hz81 {c : ℝ} (hc : B (97 / 200) (49 / 100) c) : B (576365788846030737 / 1000000000000000000) (579805707530686177 / 1000000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (sGlobal28_hz79 hc) (sGlobal28_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal28_hz82 {c : ℝ} (hc : B (97 / 200) (49 / 100) c) : B (704607176864268357147 / 50000000000000000) (7088124774562639399841 / 500000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) := bmul sGlobal28_hz80 (sGlobal28_hz81 hc) (by norm_num) (by norm_num)

theorem sGlobal28_hz83 {c : ℝ} (hc : B (97 / 200) (49 / 100) c) : B (704607176864268357147 / 100000000000000000) (7088124774562639399841 / 1000000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) / (2 : ℝ)) := bdiv (sGlobal28_hz82 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal28_hz84 {c : ℝ} (hc : B (97 / 200) (49 / 100) c) : B (704607176864268357147 / 100000000000000000) (7088124774562639399841 / 1000000000000000000) (s3Cpa 12225 c) := by
    convert (sGlobal28_hz83 hc) using 1 <;>
      norm_num [s3Cpa, mA] <;> ring

theorem sGlobal28_hz85 {c : ℝ} (hc : B (97 / 200) (49 / 100) c) : B (11099114735856187 / 40000000000000000) (139183249908231477 / 500000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (sGlobal28_hz79 hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal28_hz86 {c : ℝ} (hc : B (97 / 200) (49 / 100) c) : B (80168123775435801 / 250000000000000000) (16243579158824857 / 50000000000000000) (c * (kdot c)) := bmul (sGlobal28_hz38 hc) (sGlobal28_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal28_hz87 {c : ℝ} (hc : B (97 / 200) (49 / 100) c) : B (-9478742956018493 / 200000000000000000) (-169223981141121 / 4000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (sGlobal28_hz85 hc) (sGlobal28_hz86 hc) (by norm_num) (by norm_num)

theorem sGlobal28_hz88 {c : ℝ} (hc : B (97 / 200) (49 / 100) c) : B (-579388163186630457049 / 500000000000000000) (-51719079236254795957 / 50000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) := bmul sGlobal28_hz80 (sGlobal28_hz87 hc) (by norm_num) (by norm_num)

theorem sGlobal28_hz89 {c : ℝ} (hc : B (97 / 200) (49 / 100) c) : B (-579388163186630457049 / 1000000000000000000) (-51719079236254795957 / 100000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) / (2 : ℝ)) := bdiv (sGlobal28_hz88 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal28_hz90 {c : ℝ} (hc : B (97 / 200) (49 / 100) c) : B (-579388163186630457049 / 1000000000000000000) (-51719079236254795957 / 100000000000000000) (s3Cpp 12225 c) := by
    convert (sGlobal28_hz89 hc) using 1 <;>
      norm_num [s3Cpp, mA] <;> ring

theorem sGlobal28_hz91 {c : ℝ} (hc : B (97 / 200) (49 / 100) c) : B (7161216878576421279871 / 1000000000000000000) (7203269884496377812067 / 1000000000000000000) ((s3Cpa 12225 c) + (s3r1 12225 46)) := badd (sGlobal28_hz84 hc) sGlobal28_hz33 (by norm_num) (by norm_num)

theorem sGlobal28_hz92 {c : ℝ} (hc : B (97 / 200) (49 / 100) c) : B (64840230374528845939 / 1000000000000000000) (32610496699095792969 / 500000000000000000) (((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) := bdiv (sGlobal28_hz91 hc) sGlobal28_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal28_hz93 {c : ℝ} (hc : B (97 / 200) (49 / 100) c) : B (64962913400022906351 / 1000000000000000000) (65343676423685646361 / 1000000000000000000) ((((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) + (s3e0 12225 46)) := badd (sGlobal28_hz92 hc) sGlobal28_hz16 (by norm_num) (by norm_num)

theorem sGlobal28_hz94 {c : ℝ} (hc : B (97 / 200) (49 / 100) c) : B (64962913400022906351 / 1000000000000000000) (65343676423685646361 / 1000000000000000000) (s3Lam 12225 46 c) := by
    convert (sGlobal28_hz93 hc) using 1 <;>
      norm_num [s3Lam] <;> ring

theorem sGlobal28_hz95 {c : ℝ} (hc : B (97 / 200) (49 / 100) c) : B (-502624756564138651449 / 1000000000000000000) (-27526711608753480297 / 62500000000000000) ((s3Cpp 12225 c) + (s3rpp 12225 46)) := badd (sGlobal28_hz90 hc) sGlobal28_hz37 (by norm_num) (by norm_num)

theorem sGlobal28_hz96 {c : ℝ} (hc : B (97 / 200) (49 / 100) c) : B (-14234046512670578723 / 40000000000000000) (-27526711608753480297 / 125000000000000000) (if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) := bweaken (bfirst (sGlobal28_hz95 hc) (sGlobal28_hz76 hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem sGlobal28_hz97 {c : ℝ} (hc : B (97 / 200) (49 / 100) c) : B (65940314334669932603 / 15625000000000000) (2134898024281665691419 / 500000000000000000) ((s3Lam 12225 46 c)^2) := bsq (sGlobal28_hz94 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal28_hz98 {c : ℝ} (hc : B (97 / 200) (49 / 100) c) : B (365523219962469163 / 1000000000000000000) (184768007408716781 / 500000000000000000) ((s3c1 12225 46 c)^2) := bsq (sGlobal28_hz72 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal28_hz99 {c : ℝ} (hc : B (97 / 200) (49 / 100) c) : B (315231992591283219 / 500000000000000000) (634476780037530837 / 1000000000000000000) ((1 : ℝ) - ((s3c1 12225 46 c)^2)) := bsub (bpoint (1 : ℝ)) (sGlobal28_hz98 hc) (by norm_num) (by norm_num)

theorem sGlobal28_hz100 {c : ℝ} (hc : B (97 / 200) (49 / 100) c) : B (49626101419710577 / 62500000000000000) (398270253734047667 / 500000000000000000) (√((1 : ℝ) - ((s3c1 12225 46 c)^2))) := bsqrt (sGlobal28_hz99 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal28_hz101 {c : ℝ} (hc : B (97 / 200) (49 / 100) c) : B (1247239965171718057 / 500000000000000000) (2502405806548454139 / 1000000000000000000) (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))) := bmul pi_mem (sGlobal28_hz100 hc) (by norm_num) (by norm_num)

theorem sGlobal28_hz102 {c : ℝ} (hc : B (97 / 200) (49 / 100) c) : B (843224569407416024073 / 500000000000000000) (1711697896072257638517 / 1000000000000000000) (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2))))) := bdiv (sGlobal28_hz97 hc) (sGlobal28_hz101 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal28_hz103 {c : ℝ} (hc : B (97 / 200) (49 / 100) c) : B (1330597975998067580071 / 1000000000000000000) (1491484203202229796141 / 1000000000000000000) ((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) := badd (sGlobal28_hz96 hc) (sGlobal28_hz102 hc) (by norm_num) (by norm_num)

theorem sGlobal28_hz104 : B (3762781186094069 / 250000000000000000) (376278118609407 / 25000000000000000) ((s3e0 12225 46)^2) := bsq sGlobal28_hz16 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal28_hz105 {c : ℝ} (hc : B (97 / 200) (49 / 100) c) : B (1330613027122811956347 / 1000000000000000000) (1491499254326974172421 / 1000000000000000000) (((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) := badd (sGlobal28_hz103 hc) sGlobal28_hz104 (by norm_num) (by norm_num)

theorem sGlobal28_hz106 {c : ℝ} (hc : B (97 / 200) (49 / 100) c) : B (684555050287029613239 / 500000000000000000) (1529996327781098442437 / 1000000000000000000) ((((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) + (s3rs 12225 46 maskSlack)) := badd (sGlobal28_hz105 hc) sGlobal28_hz29 (by norm_num) (by norm_num)

theorem sGlobal28_hz107 {c : ℝ} (hc : B (97 / 200) (49 / 100) c) : B (684555050287029613239 / 500000000000000000) (1529996327781098442437 / 1000000000000000000) (s3U 12225 46 maskSlack c) := by
    convert (sGlobal28_hz106 hc) using 1 <;>
      norm_num [s3U] <;> ring

theorem sGlobal28_hz108 {c : ℝ} (hc : B (97 / 200) (49 / 100) c) : B (-656151569809122731867 / 1000000000000000000) (-59395419898503976517 / 100000000000000000) ((s3Cpp 12225 c) - (s3rpp 12225 46)) := bsub (sGlobal28_hz90 hc) sGlobal28_hz37 (by norm_num) (by norm_num)

theorem sGlobal28_hz109 {c : ℝ} (hc : B (97 / 200) (49 / 100) c) : B (-656151569809122731867 / 1000000000000000000) (-59395419898503976517 / 100000000000000000) (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ)) := bweaken (bmin (sGlobal28_hz108 hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem sGlobal28_hz110 {c : ℝ} (hc : B (97 / 200) (49 / 100) c) : B (-92909191619106560637 / 200000000000000000) (-419724322533435729623 / 1000000000000000000) ((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) := bmul (sGlobal28_hz76 hc) (sGlobal28_hz109 hc) (by norm_num) (by norm_num)

theorem sGlobal28_hz111 {c : ℝ} (hc : B (97 / 200) (49 / 100) c) : B (-92912201844055435893 / 200000000000000000) (-419739373658180105899 / 1000000000000000000) (((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) := bsub (sGlobal28_hz110 hc) sGlobal28_hz104 (by norm_num) (by norm_num)

theorem sGlobal28_hz112 {c : ℝ} (hc : B (97 / 200) (49 / 100) c) : B (-503058082674401449481 / 1000000000000000000) (-45823644710942737603 / 100000000000000000) ((((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) - (s3rs 12225 46 maskSlack)) := bsub (sGlobal28_hz111 hc) sGlobal28_hz29 (by norm_num) (by norm_num)

theorem sGlobal28_hz113 {c : ℝ} (hc : B (97 / 200) (49 / 100) c) : B (-503058082674401449481 / 1000000000000000000) (-45823644710942737603 / 100000000000000000) (s3L 12225 46 maskSlack c) := by
    convert (sGlobal28_hz112 hc) using 1 <;>
      norm_num [s3L] <;> ring

theorem sGlobal28_hz114 {c : ℝ} (hc : B (97 / 200) (49 / 100) c) : B 0 (1529996327781098442437 / 1000000000000000000) |(s3U 12225 46 maskSlack c)| := bweaken (babs (sGlobal28_hz107 hc)) (by norm_num) (by norm_num)

theorem sGlobal28_hz115 {c : ℝ} (hc : B (97 / 200) (49 / 100) c) : B 0 (503058082674401449481 / 1000000000000000000) |(s3L 12225 46 maskSlack c)| := bweaken (babs (sGlobal28_hz113 hc)) (by norm_num) (by norm_num)

theorem sGlobal28_hz116 {c : ℝ} (hc : B (97 / 200) (49 / 100) c) : B 0 (1529996327781098442437 / 1000000000000000000) (max |(s3U 12225 46 maskSlack c)| |(s3L 12225 46 maskSlack c)|) := bweaken (bmax (sGlobal28_hz114 hc) (sGlobal28_hz115 hc)) (by norm_num) (by norm_num)

theorem sGlobal28_hz117 {c : ℝ} (hc : B (97 / 200) (49 / 100) c) : B 0 (1529996327781098442437 / 1000000000000000000) (s3nks 12225 46 maskSlack c) := by
    convert (sGlobal28_hz116 hc) using 1 <;>
      norm_num [s3nks] <;> ring

theorem sGlobal28 {c : ℝ} (hc : B (97 / 200) (49 / 100) c) :
    0 < s3am 12225 46 ∧ 0 ≤ s3dm 12225 46 c ∧
    s3dm 12225 46 c ^ 2 ≤ 2 * s3ap 12225 46 ^ 2 ∧ s3c1 12225 46 c < 1 ∧
    0 ≤ s3Cpa 12225 c - s3r1 12225 46 ∧
    s3e0 12225 46 ≤ (s3Cpa 12225 c - s3r1 12225 46) / s3ap 12225 46 ∧
    s3nks 12225 46 maskSlack c ≤ 12225 * (62577 / 500000) := by

  refine ⟨lt_of_lt_of_le (by norm_num) sGlobal28_hz14.1,
    le_trans (by norm_num) (sGlobal28_hz64 hc).1, ?_,
    lt_of_le_of_lt (sGlobal28_hz72 hc).2 (by norm_num), ?_, ?_,
    le_trans (sGlobal28_hz117 hc).2 (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (sGlobal28_hz64 hc).1) (sGlobal28_hz64 hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) sGlobal28_hz9.1 2
    nlinarith only [h1, h2]
  · linarith only [(sGlobal28_hz84 hc).1, sGlobal28_hz33.2]
  · have hap : 0 < s3ap 12225 46 := lt_of_lt_of_le (by norm_num) sGlobal28_hz9.1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul sGlobal28_hz16.2 sGlobal28_hz9.2 (le_trans (by norm_num) sGlobal28_hz9.1) (by norm_num)
    linarith only [h, (sGlobal28_hz84 hc).1, sGlobal28_hz33.2]

end BstLean.Part255
