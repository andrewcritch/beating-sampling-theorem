import BstLean.Part255SGlobal23
import BstLean.Part255Numeric10
namespace BstLean.Part255
open Real BstLean.Part130 BstLean.Part182 BstLean.Part197 BstLean.Part246
theorem sGlobal27_hz0 : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal27_hz1 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) ((√(23 : ℝ)) / (12225 : ℝ)) := bdiv sGlobal27_hz0 (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal27_hz2 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) maskSlack := by
    convert sGlobal27_hz1 using 1 <;>
      norm_num [maskSlack] <;> ring

theorem sGlobal27_hz3 : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal27_hz4 : B (6395294793910793 / 500000000000000000) (12790589587821587 / 1000000000000000000) (√((2 / 12225) : ℝ)) := bsqrt (bpoint ((2 / 12225) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal27_hz5 : B (7230130686979 / 62500000000000000) (23136418198333 / 200000000000000000) (√((2 / 149450625) : ℝ)) := bsqrt (bpoint ((2 / 149450625) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal27_hz6 : B (2211334438749598093 / 20000000000000000) (110566721937479904651 / 1000000000000000000) (√(12225 : ℝ)) := bsqrt (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal27_hz7 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))) := bmul sGlobal27_hz3 sGlobal27_hz4 (by norm_num) (by norm_num)

theorem sGlobal27_hz8 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) ((√(12225 : ℝ)) + ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := badd sGlobal27_hz6 sGlobal27_hz7 (by norm_num) (by norm_num)

theorem sGlobal27_hz9 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) (s3ap 12225 46) := by
    convert sGlobal27_hz8 using 1 <;>
      norm_num [s3ap, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal27_hz10 : B (163599182004089 / 1000000000000000000) (16359918200409 / 100000000000000000) ((2 : ℝ) / (12225 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal27_hz11 : B (1222499983640081799591 / 100000000000000000) (12224999836400817995911 / 1000000000000000000) ((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ))) := bsub (bpoint (12225 : ℝ)) sGlobal27_hz10 (by norm_num) (by norm_num)

theorem sGlobal27_hz12 : B (110566721197658827907 / 1000000000000000000) (27641680299414706977 / 250000000000000000) (√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) := bsqrt sGlobal27_hz11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal27_hz13 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) ((√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) - ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bsub sGlobal27_hz12 sGlobal27_hz7 (by norm_num) (by norm_num)

theorem sGlobal27_hz14 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) (s3am 12225 46) := by
    convert sGlobal27_hz13 using 1 <;>
      norm_num [s3am, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal27_hz15 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√((2 / 12225) : ℝ)) * (√(92 : ℝ))) := bmul sGlobal27_hz4 sGlobal27_hz3 (by norm_num) (by norm_num)

theorem sGlobal27_hz16 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) (s3e0 12225 46) := by
    convert sGlobal27_hz15 using 1 <;>
      norm_num [s3e0, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal27_hz17 : B (250196148528560847 / 500000000000000000) (100078459411424339 / 200000000000000000) (((1 / 2) : ℝ) + maskSlack) := badd (bpoint ((1 / 2) : ℝ)) sGlobal27_hz2 (by norm_num) (by norm_num)

theorem sGlobal27_hz18 : B (59827153232297998295487 / 800000000000000) (23930861292919199366019 / 320000000000000) ((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack)) := bmul (bpoint (149450625 : ℝ)) sGlobal27_hz17 (by norm_num) (by norm_num)

theorem sGlobal27_hz19 : B (1729554180017180009583 / 200000000000000000) (8647770900085900056557 / 1000000000000000000) (√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) := bsqrt sGlobal27_hz18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal27_hz20 : B (4328681281566262743499 / 500000000000000000) (8657362563132525495641 / 1000000000000000000) ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))) := badd sGlobal27_hz19 sGlobal27_hz3 (by norm_num) (by norm_num)

theorem sGlobal27_hz21 : B (110732771457999278473 / 1000000000000000000) (55366385728999643621 / 500000000000000000) ((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ)))) := bmul sGlobal27_hz4 sGlobal27_hz20 (by norm_num) (by norm_num)

theorem sGlobal27_hz22 : B (209099159 / 15625000000000000) (13382346177 / 1000000000000000000) ((2 : ℝ) / (149450625 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (149450625 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal27_hz23 : B (2452349334953899930479 / 200000000000000000) (12261746674769501594427 / 1000000000000000000) (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2) := bsq sGlobal27_hz21 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal27_hz24 : B (82045469362091 / 500000000000000000) (32818187747289 / 200000000000000000) (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2)) := bmul sGlobal27_hz22 sGlobal27_hz23 (by norm_num) (by norm_num)

theorem sGlobal27_hz25 : B (82045469362091 / 250000000000000000) (32818187747289 / 100000000000000000) ((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) := bmul (bpoint (2 : ℝ)) sGlobal27_hz24 (by norm_num) (by norm_num)

theorem sGlobal27_hz26 : B (117258080744995992792057 / 1000000000000000000) (58629040372497996396029 / 500000000000000000) (√(13749457500 : ℝ)) := bsqrt (bpoint (13749457500 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal27_hz27 : B (117304080744995992792057 / 1000000000000000000) (58652040372497996396029 / 500000000000000000) ((√(13749457500 : ℝ)) + (46 : ℝ)) := badd sGlobal27_hz26 (bpoint (46 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal27_hz28 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal27_hz25 sGlobal27_hz27 (by norm_num) (by norm_num)

theorem sGlobal27_hz29 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (s3rs 12225 46 maskSlack) := by
    convert sGlobal27_hz28 using 1 <;>
      norm_num [s3rs, s3pp, s3K, mA, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal27_hz30 : B (490797546012267 / 1000000000000000000) (49079754601227 / 100000000000000000) ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (3 : ℝ)) sGlobal27_hz10 (by norm_num) (by norm_num)

theorem sGlobal27_hz31 : B (490797546012267 / 500000000000000000) (49079754601227 / 50000000000000000) ((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal27_hz30 (by norm_num) (by norm_num)

theorem sGlobal27_hz32 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal27_hz31 sGlobal27_hz27 (by norm_num) (by norm_num)

theorem sGlobal27_hz33 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (s3r1 12225 46) := by
    convert sGlobal27_hz32 using 1 <;>
      norm_num [s3r1, mA] <;> ring

theorem sGlobal27_hz34 : B (163599182004089 / 500000000000000000) (16359918200409 / 50000000000000000) ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (2 : ℝ)) sGlobal27_hz10 (by norm_num) (by norm_num)

theorem sGlobal27_hz35 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal27_hz34 (by norm_num) (by norm_num)

theorem sGlobal27_hz36 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal27_hz35 sGlobal27_hz27 (by norm_num) (by norm_num)

theorem sGlobal27_hz37 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (s3rpp 12225 46) := by
    convert sGlobal27_hz36 using 1 <;>
      norm_num [s3rpp, mA] <;> ring

theorem sGlobal27_hz38 {c : ℝ} (hc : B (12 / 25) (97 / 200) c) : B (12 / 25) (97 / 200) c := hc

theorem sGlobal27_hz39 : B (659363344522858571 / 1000000000000000000) (82420418065381437 / 125000000000000000) (kdot ((12 / 25))) := by
    constructor
    · apply bkdot_lower (q := (296374489181909579 / 500000000000000000)) (a := (535070807195192459 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (592748978363819157 / 1000000000000000000)) (a := (267535403597444707 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal27_hz40 : B (144 / 625) (144 / 625) (((12 / 25) : ℝ)^2) := bsq (bpoint ((12 / 25) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal27_hz41 : B (481 / 625) (481 / 625) ((1 : ℝ) - (((12 / 25) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal27_hz40 (by norm_num) (by norm_num)

theorem sGlobal27_hz42 : B (6853660062331659 / 7812500000000000) (877268487978452353 / 1000000000000000000) (√((1 : ℝ) - (((12 / 25) : ℝ)^2))) := bsqrt sGlobal27_hz41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal27_hz43 : B (279243232561047303 / 1000000000000000000) (34905404070130913 / 125000000000000000) ((√((1 : ℝ) - (((12 / 25) : ℝ)^2))) / Real.pi) := bdiv sGlobal27_hz42 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal27_hz44 : B (158247202685486057 / 500000000000000000) (316494405371064719 / 1000000000000000000) (((12 / 25) : ℝ) * (kdot ((12 / 25)))) := bmul (bpoint ((12 / 25) : ℝ)) sGlobal27_hz39 (by norm_num) (by norm_num)

theorem sGlobal27_hz45 : B (595737637932019417 / 1000000000000000000) (595737637932112023 / 1000000000000000000) (((√((1 : ℝ) - (((12 / 25) : ℝ)^2))) / Real.pi) + (((12 / 25) : ℝ) * (kdot ((12 / 25))))) := badd sGlobal27_hz43 sGlobal27_hz44 (by norm_num) (by norm_num)

theorem sGlobal27_hz46 : B (595737637932019417 / 1000000000000000000) (595737637932112023 / 1000000000000000000) (kappa ((12 / 25))) := by rw [kappa_eq]; exact sGlobal27_hz45

theorem sGlobal27_hz47 : B (330590201135817737 / 500000000000000000) (661180402271775659 / 1000000000000000000) (kdot ((97 / 200))) := by
    constructor
    · apply bkdot_lower (q := (117779683613320477 / 200000000000000000)) (a := (106443315911567899 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (36806151129162649 / 62500000000000000)) (a := (106443315911523859 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal27_hz48 : B (9409 / 40000) (9409 / 40000) (((97 / 200) : ℝ)^2) := bsq (bpoint ((97 / 200) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal27_hz49 : B (30591 / 40000) (30591 / 40000) ((1 : ℝ) - (((97 / 200) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal27_hz48 (by norm_num) (by norm_num)

theorem sGlobal27_hz50 : B (43725707541445227 / 50000000000000000) (874514150828904541 / 1000000000000000000) (√((1 : ℝ) - (((97 / 200) : ℝ)^2))) := bsqrt sGlobal27_hz49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal27_hz51 : B (34795812477057869 / 125000000000000000) (139183249908231477 / 500000000000000000) ((√((1 : ℝ) - (((97 / 200) : ℝ)^2))) / Real.pi) := bdiv sGlobal27_hz50 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal27_hz52 : B (80168123775435801 / 250000000000000000) (64134499020362239 / 200000000000000000) (((97 / 200) : ℝ) * (kdot ((97 / 200)))) := bmul (bpoint ((97 / 200) : ℝ)) sGlobal27_hz47 (by norm_num) (by norm_num)

theorem sGlobal27_hz53 : B (149759748729551539 / 250000000000000000) (599038994918274149 / 1000000000000000000) (((√((1 : ℝ) - (((97 / 200) : ℝ)^2))) / Real.pi) + (((97 / 200) : ℝ) * (kdot ((97 / 200))))) := badd sGlobal27_hz51 sGlobal27_hz52 (by norm_num) (by norm_num)

theorem sGlobal27_hz54 : B (149759748729551539 / 250000000000000000) (599038994918274149 / 1000000000000000000) (kappa ((97 / 200))) := by rw [kappa_eq]; exact sGlobal27_hz53

theorem sGlobal27_hz55 {c : ℝ} (hc : B (12 / 25) (97 / 200) c) : B (595737637932019417 / 1000000000000000000) (599038994918274149 / 1000000000000000000) (kappa c) := bkappa (sGlobal27_hz38 hc) (by norm_num) (by norm_num) sGlobal27_hz46.1 sGlobal27_hz54.2

theorem sGlobal27_hz56 : B 24450 24450 ((2 : ℝ) * (12225 : ℝ)) := bmul (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal27_hz57 {c : ℝ} (hc : B (12 / 25) (97 / 200) c) : B (400961005081725851 / 1000000000000000000) (404262362067980583 / 1000000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (sGlobal27_hz55 hc) (by norm_num) (by norm_num)

theorem sGlobal27_hz58 {c : ℝ} (hc : B (12 / 25) (97 / 200) c) : B (196069931484963941139 / 20000000000000000) (197684295051242505087 / 20000000000000000) (((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) := bmul sGlobal27_hz56 (sGlobal27_hz57 hc) (by norm_num) (by norm_num)

theorem sGlobal27_hz59 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (4 : ℝ)) sGlobal27_hz10 (by norm_num) (by norm_num)

theorem sGlobal27_hz60 {c : ℝ} (hc : B (12 / 25) (97 / 200) c) : B (980349591985146904059 / 100000000000000000) (4942107049082698618997 / 500000000000000000) ((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bsub (sGlobal27_hz58 hc) sGlobal27_hz59 (by norm_num) (by norm_num)

theorem sGlobal27_hz61 {c : ℝ} (hc : B (12 / 25) (97 / 200) c) : B (3960504194135179863 / 40000000000000000) (99419384921479962041 / 1000000000000000000) (√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) := bsqrt (sGlobal27_hz60 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal27_hz62 : B (30670756373515103 / 125000000000000000) (122683025494060423 / 500000000000000000) ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal27_hz7 (by norm_num) (by norm_num)

theorem sGlobal27_hz63 {c : ℝ} (hc : B (12 / 25) (97 / 200) c) : B (98767238802391375729 / 1000000000000000000) (99174018870491841217 / 1000000000000000000) ((√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) - ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))))) := bsub (sGlobal27_hz61 hc) sGlobal27_hz62 (by norm_num) (by norm_num)

theorem sGlobal27_hz64 {c : ℝ} (hc : B (12 / 25) (97 / 200) c) : B (98767238802391375729 / 1000000000000000000) (99174018870491841217 / 1000000000000000000) (s3dm 12225 46 c) := by
    convert (sGlobal27_hz63 hc) using 1 <;>
      norm_num [s3dm, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal27_hz65 : B (6126072185528622723889 / 500000000000000000) (2450428874211449090087 / 200000000000000000) ((s3ap 12225 46)^2) := bsq sGlobal27_hz9 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal27_hz66 : B (6126072185528622723889 / 250000000000000000) (2450428874211449090087 / 100000000000000000) ((2 : ℝ) * ((s3ap 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal27_hz65 (by norm_num) (by norm_num)

theorem sGlobal27_hz67 {c : ℝ} (hc : B (12 / 25) (97 / 200) c) : B (9754967460648604595379 / 1000000000000000000) (2458871504731167954293 / 250000000000000000) ((s3dm 12225 46 c)^2) := bsq (sGlobal27_hz64 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal27_hz68 {c : ℝ} (hc : B (12 / 25) (97 / 200) c) : B (916800170199363692399 / 62500000000000000) (14749321281465886305491 / 1000000000000000000) (((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) := bsub sGlobal27_hz66 (sGlobal27_hz67 hc) (by norm_num) (by norm_num)

theorem sGlobal27_hz69 : B (1524735695971823534271 / 125000000000000000) (609894278388729413841 / 50000000000000000) ((s3am 12225 46)^2) := bsq sGlobal27_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal27_hz70 : B (1524735695971823534271 / 62500000000000000) (609894278388729413841 / 25000000000000000) ((2 : ℝ) * ((s3am 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal27_hz69 (by norm_num) (by norm_num)

theorem sGlobal27_hz71 {c : ℝ} (hc : B (12 / 25) (97 / 200) c) : B (601284650593177801 / 1000000000000000000) (151146290882904103 / 250000000000000000) ((((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) / ((2 : ℝ) * ((s3am 12225 46)^2))) := bdiv (sGlobal27_hz68 hc) sGlobal27_hz70 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal27_hz72 {c : ℝ} (hc : B (12 / 25) (97 / 200) c) : B (601284650593177801 / 1000000000000000000) (151146290882904103 / 250000000000000000) (s3c1 12225 46 c) := by
    convert (sGlobal27_hz71 hc) using 1 <;>
      norm_num [s3c1] <;> ring

theorem sGlobal27_hz73 {c : ℝ} (hc : B (12 / 25) (97 / 200) c) : B (659363344522858571 / 1000000000000000000) (661180402271775659 / 1000000000000000000) (kdot c) := bkdot (sGlobal27_hz38 hc) sGlobal27_hz39.1 sGlobal27_hz47.2

theorem sGlobal27_hz74 : B (352672109661407629 / 500000000000000000) (352672109661407651 / 500000000000000000) (kdot ((601284650593177801 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (249498082107558329 / 500000000000000000)) (a := (115711054489151117 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (498996164215116657 / 1000000000000000000)) (a := (1157110544891511 / 2500000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal27_hz75 : B (706661091462413721 / 1000000000000000000) (176665272865603439 / 250000000000000000) (kdot ((151146290882904103 / 250000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (496415226546714153 / 1000000000000000000)) (a := (230387840018432333 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (62051903318339269 / 125000000000000000)) (a := (460775680036864613 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal27_hz76 {c : ℝ} (hc : B (12 / 25) (97 / 200) c) : B (352672109661407629 / 500000000000000000) (176665272865603439 / 250000000000000000) (kdot (s3c1 12225 46 c)) := bkdot (sGlobal27_hz72 hc) sGlobal27_hz74.1 sGlobal27_hz75.2

theorem sGlobal27_hz77 {c : ℝ} (hc : B (12 / 25) (97 / 200) c) : B (144 / 625) (9409 / 40000) (c^2) := bsq (sGlobal27_hz38 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal27_hz78 {c : ℝ} (hc : B (12 / 25) (97 / 200) c) : B (30591 / 40000) (481 / 625) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (sGlobal27_hz77 hc) (by norm_num) (by norm_num)

theorem sGlobal27_hz79 {c : ℝ} (hc : B (12 / 25) (97 / 200) c) : B (43725707541445227 / 50000000000000000) (877268487978452353 / 1000000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (sGlobal27_hz78 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal27_hz80 : B (39119999999999765769 / 1600000000000000) (3912000000000000489 / 160000000000000) ((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (149450625 : ℝ)) sGlobal27_hz10 (by norm_num) (by norm_num)

theorem sGlobal27_hz81 {c : ℝ} (hc : B (12 / 25) (97 / 200) c) : B (72077821915389261 / 125000000000000000) (145008182945486379 / 250000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (sGlobal27_hz79 hc) (sGlobal27_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal27_hz82 {c : ℝ} (hc : B (12 / 25) (97 / 200) c) : B (7049210983325027518649 / 500000000000000000) (7090900146034284819463 / 500000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) := bmul sGlobal27_hz80 (sGlobal27_hz81 hc) (by norm_num) (by norm_num)

theorem sGlobal27_hz83 {c : ℝ} (hc : B (12 / 25) (97 / 200) c) : B (7049210983325027518649 / 1000000000000000000) (7090900146034284819463 / 1000000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) / (2 : ℝ)) := bdiv (sGlobal27_hz82 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal27_hz84 {c : ℝ} (hc : B (12 / 25) (97 / 200) c) : B (7049210983325027518649 / 1000000000000000000) (7090900146034284819463 / 1000000000000000000) (s3Cpa 12225 c) := by
    convert (sGlobal27_hz83 hc) using 1 <;>
      norm_num [s3Cpa, mA] <;> ring

theorem sGlobal27_hz85 {c : ℝ} (hc : B (12 / 25) (97 / 200) c) : B (34795812477057869 / 125000000000000000) (34905404070130913 / 125000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (sGlobal27_hz79 hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal27_hz86 {c : ℝ} (hc : B (12 / 25) (97 / 200) c) : B (158247202685486057 / 500000000000000000) (64134499020362239 / 200000000000000000) (c * (kdot c)) := bmul (sGlobal27_hz38 hc) (sGlobal27_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal27_hz87 {c : ℝ} (hc : B (12 / 25) (97 / 200) c) : B (-42305995285348243 / 1000000000000000000) (-3725117280992481 / 100000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (sGlobal27_hz85 hc) (sGlobal27_hz86 hc) (by norm_num) (by norm_num)

theorem sGlobal27_hz88 {c : ℝ} (hc : B (12 / 25) (97 / 200) c) : B (-129297698090845583831 / 125000000000000000) (-910791175202656151137 / 1000000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) := bmul sGlobal27_hz80 (sGlobal27_hz87 hc) (by norm_num) (by norm_num)

theorem sGlobal27_hz89 {c : ℝ} (hc : B (12 / 25) (97 / 200) c) : B (-129297698090845583831 / 250000000000000000) (-28462224225083004723 / 62500000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) / (2 : ℝ)) := bdiv (sGlobal27_hz88 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal27_hz90 {c : ℝ} (hc : B (12 / 25) (97 / 200) c) : B (-129297698090845583831 / 250000000000000000) (-28462224225083004723 / 62500000000000000) (s3Cpp 12225 c) := by
    convert (sGlobal27_hz89 hc) using 1 <;>
      norm_num [s3Cpp, mA] <;> ring

theorem sGlobal27_hz91 {c : ℝ} (hc : B (12 / 25) (97 / 200) c) : B (143287121865175304541 / 20000000000000000) (7206045255968023231689 / 1000000000000000000) ((s3Cpa 12225 c) + (s3r1 12225 46)) := badd (sGlobal27_hz84 hc) sGlobal27_hz33 (by norm_num) (by norm_num)

theorem sGlobal27_hz92 {c : ℝ} (hc : B (12 / 25) (97 / 200) c) : B (64868653952064560529 / 1000000000000000000) (65246122608582454253 / 1000000000000000000) (((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) := bdiv (sGlobal27_hz91 hc) sGlobal27_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal27_hz93 {c : ℝ} (hc : B (12 / 25) (97 / 200) c) : B (64991336977558620941 / 1000000000000000000) (16342201408519128669 / 250000000000000000) ((((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) + (s3e0 12225 46)) := badd (sGlobal27_hz92 hc) sGlobal27_hz16 (by norm_num) (by norm_num)

theorem sGlobal27_hz94 {c : ℝ} (hc : B (12 / 25) (97 / 200) c) : B (64991336977558620941 / 1000000000000000000) (16342201408519128669 / 250000000000000000) (s3Lam 12225 46 c) := by
    convert (sGlobal27_hz93 hc) using 1 <;>
      norm_num [s3Lam] <;> ring

theorem sGlobal27_hz95 {c : ℝ} (hc : B (12 / 25) (97 / 200) c) : B (-110106846435222632431 / 250000000000000000) (-1514528723915343203 / 4000000000000000) ((s3Cpp 12225 c) + (s3rpp 12225 46)) := badd (sGlobal27_hz90 hc) sGlobal27_hz37 (by norm_num) (by norm_num)

theorem sGlobal27_hz96 {c : ℝ} (hc : B (12 / 25) (97 / 200) c) : B (-311232897117595226733 / 1000000000000000000) (-1514528723915343203 / 8000000000000000) (if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) := bweaken (bfirst (sGlobal27_hz95 hc) (sGlobal27_hz76 hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem sGlobal27_hz97 {c : ℝ} (hc : B (12 / 25) (97 / 200) c) : B (4223873882130578542167 / 1000000000000000000) (1068270187506418371981 / 250000000000000000) ((s3Lam 12225 46 c)^2) := bsq (sGlobal27_hz94 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal27_hz98 {c : ℝ} (hc : B (12 / 25) (97 / 200) c) : B (361543231038959913 / 1000000000000000000) (1142260062382973 / 3125000000000000) ((s3c1 12225 46 c)^2) := bsq (sGlobal27_hz72 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal27_hz99 {c : ℝ} (hc : B (12 / 25) (97 / 200) c) : B (1982739937617027 / 3125000000000000) (638456768961040087 / 1000000000000000000) ((1 : ℝ) - ((s3c1 12225 46 c)^2)) := bsub (bpoint (1 : ℝ)) (sGlobal27_hz98 hc) (by norm_num) (by norm_num)

theorem sGlobal27_hz100 {c : ℝ} (hc : B (12 / 25) (97 / 200) c) : B (99567563433505467 / 125000000000000000) (799034898462539049 / 1000000000000000000) (√((1 : ℝ) - ((s3c1 12225 46 c)^2))) := bsqrt (sGlobal27_hz99 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal27_hz101 {c : ℝ} (hc : B (12 / 25) (97 / 200) c) : B (1251202903274146019 / 500000000000000000) (2510242166971779053 / 1000000000000000000) (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))) := bmul pi_mem (sGlobal27_hz100 hc) (by norm_num) (by norm_num)

theorem sGlobal27_hz102 {c : ℝ} (hc : B (12 / 25) (97 / 200) c) : B (168265593563270929077 / 100000000000000000) (42689726211111340513 / 25000000000000000) (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2))))) := bdiv (sGlobal27_hz97 hc) (sGlobal27_hz101 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal27_hz103 {c : ℝ} (hc : B (12 / 25) (97 / 200) c) : B (1371423038515114064037 / 1000000000000000000) (303654591591007144029 / 200000000000000000) ((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) := badd (sGlobal27_hz96 hc) (sGlobal27_hz102 hc) (by norm_num) (by norm_num)

theorem sGlobal27_hz104 : B (3762781186094069 / 250000000000000000) (376278118609407 / 25000000000000000) ((s3e0 12225 46)^2) := bsq sGlobal27_hz16 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal27_hz105 {c : ℝ} (hc : B (12 / 25) (97 / 200) c) : B (1371438089639858440313 / 1000000000000000000) (60731520363191203857 / 40000000000000000) (((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) := badd (sGlobal27_hz103 hc) sGlobal27_hz104 (by norm_num) (by norm_num)

theorem sGlobal27_hz106 {c : ℝ} (hc : B (12 / 25) (97 / 200) c) : B (352483790772776427611 / 250000000000000000) (1556785082533904366441 / 1000000000000000000) ((((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) + (s3rs 12225 46 maskSlack)) := badd (sGlobal27_hz105 hc) sGlobal27_hz29 (by norm_num) (by norm_num)

theorem sGlobal27_hz107 {c : ℝ} (hc : B (12 / 25) (97 / 200) c) : B (352483790772776427611 / 250000000000000000) (1556785082533904366441 / 1000000000000000000) (s3U 12225 46 maskSlack c) := by
    convert (sGlobal27_hz106 hc) using 1 <;>
      norm_num [s3U] <;> ring

theorem sGlobal27_hz108 {c : ℝ} (hc : B (12 / 25) (97 / 200) c) : B (-296977099492937305071 / 500000000000000000) (-33259937138988742573 / 62500000000000000) ((s3Cpp 12225 c) - (s3rpp 12225 46)) := bsub (sGlobal27_hz90 hc) sGlobal27_hz37 (by norm_num) (by norm_num)

theorem sGlobal27_hz109 {c : ℝ} (hc : B (12 / 25) (97 / 200) c) : B (-296977099492937305071 / 500000000000000000) (-33259937138988742573 / 62500000000000000) (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ)) := bweaken (bmin (sGlobal27_hz108 hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem sGlobal27_hz110 {c : ℝ} (hc : B (12 / 25) (97 / 200) c) : B (-209862161267020918819 / 500000000000000000) (-46919408792051848537 / 125000000000000000) ((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) := bmul (sGlobal27_hz76 hc) (sGlobal27_hz109 hc) (by norm_num) (by norm_num)

theorem sGlobal27_hz111 {c : ℝ} (hc : B (12 / 25) (97 / 200) c) : B (-209869686829393106959 / 500000000000000000) (-93842580365289791143 / 250000000000000000) (((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) := bsub (sGlobal27_hz110 hc) sGlobal27_hz104 (by norm_num) (by norm_num)

theorem sGlobal27_hz112 {c : ℝ} (hc : B (12 / 25) (97 / 200) c) : B (-229118223556455241967 / 500000000000000000) (-413867394912406434703 / 1000000000000000000) ((((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) - (s3rs 12225 46 maskSlack)) := bsub (sGlobal27_hz111 hc) sGlobal27_hz29 (by norm_num) (by norm_num)

theorem sGlobal27_hz113 {c : ℝ} (hc : B (12 / 25) (97 / 200) c) : B (-229118223556455241967 / 500000000000000000) (-413867394912406434703 / 1000000000000000000) (s3L 12225 46 maskSlack c) := by
    convert (sGlobal27_hz112 hc) using 1 <;>
      norm_num [s3L] <;> ring

theorem sGlobal27_hz114 {c : ℝ} (hc : B (12 / 25) (97 / 200) c) : B 0 (1556785082533904366441 / 1000000000000000000) |(s3U 12225 46 maskSlack c)| := bweaken (babs (sGlobal27_hz107 hc)) (by norm_num) (by norm_num)

theorem sGlobal27_hz115 {c : ℝ} (hc : B (12 / 25) (97 / 200) c) : B 0 (229118223556455241967 / 500000000000000000) |(s3L 12225 46 maskSlack c)| := bweaken (babs (sGlobal27_hz113 hc)) (by norm_num) (by norm_num)

theorem sGlobal27_hz116 {c : ℝ} (hc : B (12 / 25) (97 / 200) c) : B 0 (1556785082533904366441 / 1000000000000000000) (max |(s3U 12225 46 maskSlack c)| |(s3L 12225 46 maskSlack c)|) := bweaken (bmax (sGlobal27_hz114 hc) (sGlobal27_hz115 hc)) (by norm_num) (by norm_num)

theorem sGlobal27_hz117 {c : ℝ} (hc : B (12 / 25) (97 / 200) c) : B 0 (1556785082533904366441 / 1000000000000000000) (s3nks 12225 46 maskSlack c) := by
    convert (sGlobal27_hz116 hc) using 1 <;>
      norm_num [s3nks] <;> ring

theorem sGlobal27 {c : ℝ} (hc : B (12 / 25) (97 / 200) c) :
    0 < s3am 12225 46 ∧ 0 ≤ s3dm 12225 46 c ∧
    s3dm 12225 46 c ^ 2 ≤ 2 * s3ap 12225 46 ^ 2 ∧ s3c1 12225 46 c < 1 ∧
    0 ≤ s3Cpa 12225 c - s3r1 12225 46 ∧
    s3e0 12225 46 ≤ (s3Cpa 12225 c - s3r1 12225 46) / s3ap 12225 46 ∧
    s3nks 12225 46 maskSlack c ≤ 12225 * (25469 / 200000) := by

  refine ⟨lt_of_lt_of_le (by norm_num) sGlobal27_hz14.1,
    le_trans (by norm_num) (sGlobal27_hz64 hc).1, ?_,
    lt_of_le_of_lt (sGlobal27_hz72 hc).2 (by norm_num), ?_, ?_,
    le_trans (sGlobal27_hz117 hc).2 (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (sGlobal27_hz64 hc).1) (sGlobal27_hz64 hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) sGlobal27_hz9.1 2
    nlinarith only [h1, h2]
  · linarith only [(sGlobal27_hz84 hc).1, sGlobal27_hz33.2]
  · have hap : 0 < s3ap 12225 46 := lt_of_lt_of_le (by norm_num) sGlobal27_hz9.1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul sGlobal27_hz16.2 sGlobal27_hz9.2 (le_trans (by norm_num) sGlobal27_hz9.1) (by norm_num)
    linarith only [h, (sGlobal27_hz84 hc).1, sGlobal27_hz33.2]

end BstLean.Part255
