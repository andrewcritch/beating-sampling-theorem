import BstLean.Part255SGlobal41
import BstLean.Part255Numeric10
namespace BstLean.Part255
open Real BstLean.Part130 BstLean.Part182 BstLean.Part197 BstLean.Part246
theorem sGlobal45_hz0 : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal45_hz1 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) ((√(23 : ℝ)) / (12225 : ℝ)) := bdiv sGlobal45_hz0 (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal45_hz2 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) maskSlack := by
    convert sGlobal45_hz1 using 1 <;>
      norm_num [maskSlack] <;> ring

theorem sGlobal45_hz3 : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal45_hz4 : B (6395294793910793 / 500000000000000000) (12790589587821587 / 1000000000000000000) (√((2 / 12225) : ℝ)) := bsqrt (bpoint ((2 / 12225) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal45_hz5 : B (7230130686979 / 62500000000000000) (23136418198333 / 200000000000000000) (√((2 / 149450625) : ℝ)) := bsqrt (bpoint ((2 / 149450625) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal45_hz6 : B (2211334438749598093 / 20000000000000000) (110566721937479904651 / 1000000000000000000) (√(12225 : ℝ)) := bsqrt (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal45_hz7 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))) := bmul sGlobal45_hz3 sGlobal45_hz4 (by norm_num) (by norm_num)

theorem sGlobal45_hz8 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) ((√(12225 : ℝ)) + ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := badd sGlobal45_hz6 sGlobal45_hz7 (by norm_num) (by norm_num)

theorem sGlobal45_hz9 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) (s3ap 12225 46) := by
    convert sGlobal45_hz8 using 1 <;>
      norm_num [s3ap, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal45_hz10 : B (163599182004089 / 1000000000000000000) (16359918200409 / 100000000000000000) ((2 : ℝ) / (12225 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal45_hz11 : B (1222499983640081799591 / 100000000000000000) (12224999836400817995911 / 1000000000000000000) ((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ))) := bsub (bpoint (12225 : ℝ)) sGlobal45_hz10 (by norm_num) (by norm_num)

theorem sGlobal45_hz12 : B (110566721197658827907 / 1000000000000000000) (27641680299414706977 / 250000000000000000) (√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) := bsqrt sGlobal45_hz11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal45_hz13 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) ((√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) - ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bsub sGlobal45_hz12 sGlobal45_hz7 (by norm_num) (by norm_num)

theorem sGlobal45_hz14 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) (s3am 12225 46) := by
    convert sGlobal45_hz13 using 1 <;>
      norm_num [s3am, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal45_hz15 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√((2 / 12225) : ℝ)) * (√(92 : ℝ))) := bmul sGlobal45_hz4 sGlobal45_hz3 (by norm_num) (by norm_num)

theorem sGlobal45_hz16 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) (s3e0 12225 46) := by
    convert sGlobal45_hz15 using 1 <;>
      norm_num [s3e0, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal45_hz17 : B (250196148528560847 / 500000000000000000) (100078459411424339 / 200000000000000000) (((1 / 2) : ℝ) + maskSlack) := badd (bpoint ((1 / 2) : ℝ)) sGlobal45_hz2 (by norm_num) (by norm_num)

theorem sGlobal45_hz18 : B (59827153232297998295487 / 800000000000000) (23930861292919199366019 / 320000000000000) ((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack)) := bmul (bpoint (149450625 : ℝ)) sGlobal45_hz17 (by norm_num) (by norm_num)

theorem sGlobal45_hz19 : B (1729554180017180009583 / 200000000000000000) (8647770900085900056557 / 1000000000000000000) (√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) := bsqrt sGlobal45_hz18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal45_hz20 : B (4328681281566262743499 / 500000000000000000) (8657362563132525495641 / 1000000000000000000) ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))) := badd sGlobal45_hz19 sGlobal45_hz3 (by norm_num) (by norm_num)

theorem sGlobal45_hz21 : B (110732771457999278473 / 1000000000000000000) (55366385728999643621 / 500000000000000000) ((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ)))) := bmul sGlobal45_hz4 sGlobal45_hz20 (by norm_num) (by norm_num)

theorem sGlobal45_hz22 : B (209099159 / 15625000000000000) (13382346177 / 1000000000000000000) ((2 : ℝ) / (149450625 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (149450625 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal45_hz23 : B (2452349334953899930479 / 200000000000000000) (12261746674769501594427 / 1000000000000000000) (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2) := bsq sGlobal45_hz21 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal45_hz24 : B (82045469362091 / 500000000000000000) (32818187747289 / 200000000000000000) (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2)) := bmul sGlobal45_hz22 sGlobal45_hz23 (by norm_num) (by norm_num)

theorem sGlobal45_hz25 : B (82045469362091 / 250000000000000000) (32818187747289 / 100000000000000000) ((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) := bmul (bpoint (2 : ℝ)) sGlobal45_hz24 (by norm_num) (by norm_num)

theorem sGlobal45_hz26 : B (117258080744995992792057 / 1000000000000000000) (58629040372497996396029 / 500000000000000000) (√(13749457500 : ℝ)) := bsqrt (bpoint (13749457500 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal45_hz27 : B (117304080744995992792057 / 1000000000000000000) (58652040372497996396029 / 500000000000000000) ((√(13749457500 : ℝ)) + (46 : ℝ)) := badd sGlobal45_hz26 (bpoint (46 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal45_hz28 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal45_hz25 sGlobal45_hz27 (by norm_num) (by norm_num)

theorem sGlobal45_hz29 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (s3rs 12225 46 maskSlack) := by
    convert sGlobal45_hz28 using 1 <;>
      norm_num [s3rs, s3pp, s3K, mA, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal45_hz30 : B (490797546012267 / 1000000000000000000) (49079754601227 / 100000000000000000) ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (3 : ℝ)) sGlobal45_hz10 (by norm_num) (by norm_num)

theorem sGlobal45_hz31 : B (490797546012267 / 500000000000000000) (49079754601227 / 50000000000000000) ((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal45_hz30 (by norm_num) (by norm_num)

theorem sGlobal45_hz32 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal45_hz31 sGlobal45_hz27 (by norm_num) (by norm_num)

theorem sGlobal45_hz33 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (s3r1 12225 46) := by
    convert sGlobal45_hz32 using 1 <;>
      norm_num [s3r1, mA] <;> ring

theorem sGlobal45_hz34 : B (163599182004089 / 500000000000000000) (16359918200409 / 50000000000000000) ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (2 : ℝ)) sGlobal45_hz10 (by norm_num) (by norm_num)

theorem sGlobal45_hz35 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal45_hz34 (by norm_num) (by norm_num)

theorem sGlobal45_hz36 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal45_hz35 sGlobal45_hz27 (by norm_num) (by norm_num)

theorem sGlobal45_hz37 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (s3rpp 12225 46) := by
    convert sGlobal45_hz36 using 1 <;>
      norm_num [s3rpp, mA] <;> ring

theorem sGlobal45_hz38 {c : ℝ} (hc : B (57 / 100) (23 / 40) c) : B (57 / 100) (23 / 40) c := hc

theorem sGlobal45_hz39 : B (173264202435670071 / 250000000000000000) (346528404871340359 / 500000000000000000) (kdot ((57 / 100))) := by
    constructor
    · apply bkdot_lower (q := (10466811363896291 / 20000000000000000)) (a := (120536308947726227 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (523340568194814549 / 1000000000000000000)) (a := (120536308947726057 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal45_hz40 : B (3249 / 10000) (3249 / 10000) (((57 / 100) : ℝ)^2) := bsq (bpoint ((57 / 100) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal45_hz41 : B (6751 / 10000) (6751 / 10000) ((1 : ℝ) - (((57 / 100) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal45_hz40 (by norm_num) (by norm_num)

theorem sGlobal45_hz42 : B (410822346032929421 / 500000000000000000) (821644692065858843 / 1000000000000000000) (√((1 : ℝ) - (((57 / 100) : ℝ)^2))) := bsqrt sGlobal45_hz41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal45_hz43 : B (130768814207499631 / 500000000000000000) (261537628414999263 / 1000000000000000000) ((√((1 : ℝ) - (((57 / 100) : ℝ)^2))) / Real.pi) := bdiv sGlobal45_hz42 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal45_hz44 : B (395042381553327761 / 1000000000000000000) (39504238155332801 / 100000000000000000) (((57 / 100) : ℝ) * (kdot ((57 / 100)))) := bmul (bpoint ((57 / 100) : ℝ)) sGlobal45_hz39 (by norm_num) (by norm_num)

theorem sGlobal45_hz45 : B (656580009968327023 / 1000000000000000000) (656580009968327273 / 1000000000000000000) (((√((1 : ℝ) - (((57 / 100) : ℝ)^2))) / Real.pi) + (((57 / 100) : ℝ) * (kdot ((57 / 100))))) := badd sGlobal45_hz43 sGlobal45_hz44 (by norm_num) (by norm_num)

theorem sGlobal45_hz46 : B (656580009968327023 / 1000000000000000000) (656580009968327273 / 1000000000000000000) (kappa ((57 / 100))) := by rw [kappa_eq]; exact sGlobal45_hz45

theorem sGlobal45_hz47 : B (138999591328215007 / 200000000000000000) (347498978320537669 / 500000000000000000) (kdot ((23 / 40))) := by
    constructor
    · apply bkdot_lower (q := (259731240824659867 / 500000000000000000)) (a := (239548044686568563 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (519462481649319733 / 1000000000000000000)) (a := (479096089373136653 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal45_hz48 : B (529 / 1600) (529 / 1600) (((23 / 40) : ℝ)^2) := bsq (bpoint ((23 / 40) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal45_hz49 : B (1071 / 1600) (1071 / 1600) ((1 : ℝ) - (((23 / 40) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal45_hz48 (by norm_num) (by norm_num)

theorem sGlobal45_hz50 : B (40907670429883929 / 50000000000000000) (818153408597678581 / 1000000000000000000) (√((1 : ℝ) - (((23 / 40) : ℝ)^2))) := bsqrt sGlobal45_hz49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal45_hz51 : B (260426318371607453 / 1000000000000000000) (130213159185803727 / 500000000000000000) ((√((1 : ℝ) - (((23 / 40) : ℝ)^2))) / Real.pi) := bdiv sGlobal45_hz50 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal45_hz52 : B (79924765013723629 / 200000000000000000) (4995297813357729 / 12500000000000000) (((23 / 40) : ℝ) * (kdot ((23 / 40)))) := bmul (bpoint ((23 / 40) : ℝ)) sGlobal45_hz47 (by norm_num) (by norm_num)

theorem sGlobal45_hz53 : B (330025071720112799 / 500000000000000000) (330025071720112887 / 500000000000000000) (((√((1 : ℝ) - (((23 / 40) : ℝ)^2))) / Real.pi) + (((23 / 40) : ℝ) * (kdot ((23 / 40))))) := badd sGlobal45_hz51 sGlobal45_hz52 (by norm_num) (by norm_num)

theorem sGlobal45_hz54 : B (330025071720112799 / 500000000000000000) (330025071720112887 / 500000000000000000) (kappa ((23 / 40))) := by rw [kappa_eq]; exact sGlobal45_hz53

theorem sGlobal45_hz55 {c : ℝ} (hc : B (57 / 100) (23 / 40) c) : B (656580009968327023 / 1000000000000000000) (330025071720112887 / 500000000000000000) (kappa c) := bkappa (sGlobal45_hz38 hc) (by norm_num) (by norm_num) sGlobal45_hz46.1 sGlobal45_hz54.2

theorem sGlobal45_hz56 : B 24450 24450 ((2 : ℝ) * (12225 : ℝ)) := bmul (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal45_hz57 {c : ℝ} (hc : B (57 / 100) (23 / 40) c) : B (169974928279887113 / 500000000000000000) (343419990031672977 / 1000000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (sGlobal45_hz55 hc) (by norm_num) (by norm_num)

theorem sGlobal45_hz58 {c : ℝ} (hc : B (57 / 100) (23 / 40) c) : B (83117739928864798257 / 10000000000000000) (167932375125488085753 / 20000000000000000) (((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) := bmul sGlobal45_hz56 (sGlobal45_hz57 hc) (by norm_num) (by norm_num)

theorem sGlobal45_hz59 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (4 : ℝ)) sGlobal45_hz10 (by norm_num) (by norm_num)

theorem sGlobal45_hz60 {c : ℝ} (hc : B (57 / 100) (23 / 40) c) : B (415588666924487590467 / 50000000000000000) (4198309050938838135647 / 500000000000000000) ((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bsub (sGlobal45_hz58 hc) sGlobal45_hz59 (by norm_num) (by norm_num)

theorem sGlobal45_hz61 {c : ℝ} (hc : B (57 / 100) (23 / 40) c) : B (45584463741744708083 / 500000000000000000) (45816531137455387543 / 500000000000000000) (√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) := bsqrt (sGlobal45_hz60 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal45_hz62 : B (30670756373515103 / 125000000000000000) (122683025494060423 / 500000000000000000) ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal45_hz7 (by norm_num) (by norm_num)

theorem sGlobal45_hz63 {c : ℝ} (hc : B (57 / 100) (23 / 40) c) : B (2273089035812532383 / 25000000000000000) (45693848111961327131 / 500000000000000000) ((√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) - ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))))) := bsub (sGlobal45_hz61 hc) sGlobal45_hz62 (by norm_num) (by norm_num)

theorem sGlobal45_hz64 {c : ℝ} (hc : B (57 / 100) (23 / 40) c) : B (2273089035812532383 / 25000000000000000) (45693848111961327131 / 500000000000000000) (s3dm 12225 46 c) := by
    convert (sGlobal45_hz63 hc) using 1 <;>
      norm_num [s3dm, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal45_hz65 : B (6126072185528622723889 / 500000000000000000) (2450428874211449090087 / 200000000000000000) ((s3ap 12225 46)^2) := bsq sGlobal45_hz9 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal45_hz66 : B (6126072185528622723889 / 250000000000000000) (2450428874211449090087 / 100000000000000000) ((2 : ℝ) * ((s3ap 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal45_hz65 (by norm_num) (by norm_num)

theorem sGlobal45_hz67 {c : ℝ} (hc : B (57 / 100) (23 / 40) c) : B (8267094023569837002271 / 1000000000000000000) (8351711021115966960559 / 1000000000000000000) ((s3dm 12225 46 c)^2) := bsq (sGlobal45_hz64 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal45_hz68 {c : ℝ} (hc : B (57 / 100) (23 / 40) c) : B (16152577720998523934997 / 1000000000000000000) (16237194718544653898599 / 1000000000000000000) (((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) := bsub sGlobal45_hz66 (sGlobal45_hz67 hc) (by norm_num) (by norm_num)

theorem sGlobal45_hz69 : B (1524735695971823534271 / 125000000000000000) (609894278388729413841 / 50000000000000000) ((s3am 12225 46)^2) := bsq sGlobal45_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal45_hz70 : B (1524735695971823534271 / 62500000000000000) (609894278388729413841 / 25000000000000000) ((2 : ℝ) * ((s3am 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal45_hz69 (by norm_num) (by norm_num)

theorem sGlobal45_hz71 {c : ℝ} (hc : B (57 / 100) (23 / 40) c) : B (82763205307441653 / 125000000000000000) (66557415333692981 / 100000000000000000) ((((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) / ((2 : ℝ) * ((s3am 12225 46)^2))) := bdiv (sGlobal45_hz68 hc) sGlobal45_hz70 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal45_hz72 {c : ℝ} (hc : B (57 / 100) (23 / 40) c) : B (82763205307441653 / 125000000000000000) (66557415333692981 / 100000000000000000) (s3c1 12225 46 c) := by
    convert (sGlobal45_hz71 hc) using 1 <;>
      norm_num [s3c1] <;> ring

theorem sGlobal45_hz73 {c : ℝ} (hc : B (57 / 100) (23 / 40) c) : B (173264202435670071 / 250000000000000000) (347498978320537669 / 500000000000000000) (kdot c) := bkdot (sGlobal45_hz38 hc) sGlobal45_hz39.1 sGlobal45_hz47.2

theorem sGlobal45_hz74 : B (730336996931509291 / 1000000000000000000) (365168498465754647 / 500000000000000000) (kdot ((82763205307441653 / 125000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (450880193578172951 / 1000000000000000000)) (a := (21179282734623307 / 50000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (9017603871563459 / 20000000000000000)) (a := (211792827346233069 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal45_hz75 : B (365906633214944641 / 500000000000000000) (182953316607472321 / 250000000000000000) (kdot ((66557415333692981 / 100000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (224046382231734207 / 500000000000000000)) (a := (421266735987051507 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (448092764463468413 / 1000000000000000000)) (a := (84253347197410301 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal45_hz76 {c : ℝ} (hc : B (57 / 100) (23 / 40) c) : B (730336996931509291 / 1000000000000000000) (182953316607472321 / 250000000000000000) (kdot (s3c1 12225 46 c)) := bkdot (sGlobal45_hz72 hc) sGlobal45_hz74.1 sGlobal45_hz75.2

theorem sGlobal45_hz77 {c : ℝ} (hc : B (57 / 100) (23 / 40) c) : B (3249 / 10000) (529 / 1600) (c^2) := bsq (sGlobal45_hz38 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal45_hz78 {c : ℝ} (hc : B (57 / 100) (23 / 40) c) : B (1071 / 1600) (6751 / 10000) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (sGlobal45_hz77 hc) (by norm_num) (by norm_num)

theorem sGlobal45_hz79 {c : ℝ} (hc : B (57 / 100) (23 / 40) c) : B (40907670429883929 / 50000000000000000) (821644692065858843 / 1000000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (sGlobal45_hz78 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal45_hz80 : B (39119999999999765769 / 1600000000000000) (3912000000000000489 / 160000000000000) ((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (149450625 : ℝ)) sGlobal45_hz10 (by norm_num) (by norm_num)

theorem sGlobal45_hz81 {c : ℝ} (hc : B (57 / 100) (23 / 40) c) : B (567026791242806687 / 1000000000000000000) (285520691035378731 / 500000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (sGlobal45_hz79 hc) (sGlobal45_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal45_hz82 {c : ℝ} (hc : B (57 / 100) (23 / 40) c) : B (13863805045886540487617 / 1000000000000000000) (6980980895815010845573 / 500000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) := bmul sGlobal45_hz80 (sGlobal45_hz81 hc) (by norm_num) (by norm_num)

theorem sGlobal45_hz83 {c : ℝ} (hc : B (57 / 100) (23 / 40) c) : B (216621953841977195119 / 31250000000000000) (6980980895815010845573 / 1000000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) / (2 : ℝ)) := bdiv (sGlobal45_hz82 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal45_hz84 {c : ℝ} (hc : B (57 / 100) (23 / 40) c) : B (216621953841977195119 / 31250000000000000) (6980980895815010845573 / 1000000000000000000) (s3Cpa 12225 c) := by
    convert (sGlobal45_hz83 hc) using 1 <;>
      norm_num [s3Cpa, mA] <;> ring

theorem sGlobal45_hz85 {c : ℝ} (hc : B (57 / 100) (23 / 40) c) : B (260426318371607453 / 1000000000000000000) (261537628414999263 / 1000000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (sGlobal45_hz79 hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal45_hz86 {c : ℝ} (hc : B (57 / 100) (23 / 40) c) : B (395042381553327761 / 1000000000000000000) (4995297813357729 / 12500000000000000) (c * (kdot c)) := bmul (sGlobal45_hz38 hc) (sGlobal45_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal45_hz87 {c : ℝ} (hc : B (57 / 100) (23 / 40) c) : B (-139197506697010867 / 1000000000000000000) (-66752376569164249 / 500000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (sGlobal45_hz85 hc) (sGlobal45_hz86 hc) (by norm_num) (by norm_num)

theorem sGlobal45_hz88 {c : ℝ} (hc : B (57 / 100) (23 / 40) c) : B (-3403379038741916123573 / 1000000000000000000) (-652838242846422446351 / 200000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) := bmul sGlobal45_hz80 (sGlobal45_hz87 hc) (by norm_num) (by norm_num)

theorem sGlobal45_hz89 {c : ℝ} (hc : B (57 / 100) (23 / 40) c) : B (-1701689519370958061787 / 1000000000000000000) (-1632095607116056115877 / 1000000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) / (2 : ℝ)) := bdiv (sGlobal45_hz88 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal45_hz90 {c : ℝ} (hc : B (57 / 100) (23 / 40) c) : B (-1701689519370958061787 / 1000000000000000000) (-1632095607116056115877 / 1000000000000000000) (s3Cpp 12225 c) := by
    convert (sGlobal45_hz89 hc) using 1 <;>
      norm_num [s3Cpp, mA] <;> ring

theorem sGlobal45_hz91 {c : ℝ} (hc : B (57 / 100) (23 / 40) c) : B (7047047632877007952209 / 1000000000000000000) (7096126005748749257799 / 1000000000000000000) ((s3Cpa 12225 c) + (s3r1 12225 46)) := badd (sGlobal45_hz84 hc) sGlobal45_hz33 (by norm_num) (by norm_num)

theorem sGlobal45_hz92 {c : ℝ} (hc : B (57 / 100) (23 / 40) c) : B (63806501007250174441 / 1000000000000000000) (16062718556811125549 / 250000000000000000) (((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) := bdiv (sGlobal45_hz91 hc) sGlobal45_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal45_hz93 {c : ℝ} (hc : B (57 / 100) (23 / 40) c) : B (63929184032744234853 / 1000000000000000000) (64373557252738562619 / 1000000000000000000) ((((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) + (s3e0 12225 46)) := badd (sGlobal45_hz92 hc) sGlobal45_hz16 (by norm_num) (by norm_num)

theorem sGlobal45_hz94 {c : ℝ} (hc : B (57 / 100) (23 / 40) c) : B (63929184032744234853 / 1000000000000000000) (64373557252738562619 / 1000000000000000000) (s3Lam 12225 46 c) := by
    convert (sGlobal45_hz93 hc) using 1 <;>
      norm_num [s3Lam] <;> ring

theorem sGlobal45_hz95 {c : ℝ} (hc : B (57 / 100) (23 / 40) c) : B (-1624926112748466256187 / 1000000000000000000) (-1555332200493563841059 / 1000000000000000000) ((s3Cpp 12225 c) + (s3rpp 12225 46)) := badd (sGlobal45_hz90 hc) sGlobal45_hz37 (by norm_num) (by norm_num)

theorem sGlobal45_hz96 {c : ℝ} (hc : B (57 / 100) (23 / 40) c) : B (-594571243138838825297 / 500000000000000000) (-777666100246781920529 / 1000000000000000000) (if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) := bweaken (bfirst (sGlobal45_hz95 hc) (sGlobal45_hz76 hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem sGlobal45_hz97 {c : ℝ} (hc : B (57 / 100) (23 / 40) c) : B (817388114218496086157 / 200000000000000000) (2071977436685804798791 / 500000000000000000) ((s3Lam 12225 46 c)^2) := bsq (sGlobal45_hz94 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal45_hz98 {c : ℝ} (hc : B (57 / 100) (23 / 40) c) : B (109595970444187811 / 250000000000000000) (88597790718034191 / 200000000000000000) ((s3c1 12225 46 c)^2) := bsq (sGlobal45_hz72 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal45_hz99 {c : ℝ} (hc : B (57 / 100) (23 / 40) c) : B (111402209281965809 / 200000000000000000) (140404029555812189 / 250000000000000000) ((1 : ℝ) - ((s3c1 12225 46 c)^2)) := bsub (bpoint (1 : ℝ)) (sGlobal45_hz98 hc) (by norm_num) (by norm_num)

theorem sGlobal45_hz100 {c : ℝ} (hc : B (57 / 100) (23 / 40) c) : B (46645732924227857 / 62500000000000000) (749410513819527859 / 1000000000000000000) (√((1 : ℝ) - ((s3c1 12225 46 c)^2))) := bsqrt (sGlobal45_hz99 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal45_hz101 {c : ℝ} (hc : B (57 / 100) (23 / 40) c) : B (1172335135008526233 / 500000000000000000) (147146410296148809 / 62500000000000000) (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))) := bmul pi_mem (sGlobal45_hz100 hc) (by norm_num) (by norm_num)

theorem sGlobal45_hz102 {c : ℝ} (hc : B (57 / 100) (23 / 40) c) : B (433978962142519508029 / 250000000000000000) (1767393448180443376757 / 1000000000000000000) (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2))))) := bdiv (sGlobal45_hz97 hc) (sGlobal45_hz101 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal45_hz103 {c : ℝ} (hc : B (57 / 100) (23 / 40) c) : B (273386681146200190761 / 500000000000000000) (247431836983415364057 / 250000000000000000) ((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) := badd (sGlobal45_hz96 hc) (sGlobal45_hz102 hc) (by norm_num) (by norm_num)

theorem sGlobal45_hz104 : B (3762781186094069 / 250000000000000000) (376278118609407 / 25000000000000000) ((s3e0 12225 46)^2) := bsq sGlobal45_hz16 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal45_hz105 {c : ℝ} (hc : B (57 / 100) (23 / 40) c) : B (273394206708572378899 / 500000000000000000) (247435599764601458127 / 250000000000000000) (((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) := badd (sGlobal45_hz103 hc) sGlobal45_hz104 (by norm_num) (by norm_num)

theorem sGlobal45_hz106 {c : ℝ} (hc : B (57 / 100) (23 / 40) c) : B (585285486868392027929 / 1000000000000000000) (257059868128132525631 / 250000000000000000) ((((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) + (s3rs 12225 46 maskSlack)) := badd (sGlobal45_hz105 hc) sGlobal45_hz29 (by norm_num) (by norm_num)

theorem sGlobal45_hz107 {c : ℝ} (hc : B (57 / 100) (23 / 40) c) : B (585285486868392027929 / 1000000000000000000) (257059868128132525631 / 250000000000000000) (s3U 12225 46 maskSlack c) := by
    convert (sGlobal45_hz106 hc) using 1 <;>
      norm_num [s3U] <;> ring

theorem sGlobal45_hz108 {c : ℝ} (hc : B (57 / 100) (23 / 40) c) : B (-355690585198690067321 / 200000000000000000) (-1708859013738547921477 / 1000000000000000000) ((s3Cpp 12225 c) - (s3rpp 12225 46)) := bsub (sGlobal45_hz90 hc) sGlobal45_hz37 (by norm_num) (by norm_num)

theorem sGlobal45_hz109 {c : ℝ} (hc : B (57 / 100) (23 / 40) c) : B (-355690585198690067321 / 200000000000000000) (-1708859013738547921477 / 1000000000000000000) (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ)) := bweaken (bmin (sGlobal45_hz108 hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem sGlobal45_hz110 {c : ℝ} (hc : B (57 / 100) (23 / 40) c) : B (-1301495444963061040423 / 1000000000000000000) (-31201074006828796667 / 25000000000000000) ((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) := bmul (sGlobal45_hz76 hc) (sGlobal45_hz109 hc) (by norm_num) (by norm_num)

theorem sGlobal45_hz111 {c : ℝ} (hc : B (57 / 100) (23 / 40) c) : B (-1301510496087805416703 / 1000000000000000000) (-312014502849474060739 / 250000000000000000) (((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) := bsub (sGlobal45_hz110 hc) sGlobal45_hz104 (by norm_num) (by norm_num)

theorem sGlobal45_hz112 {c : ℝ} (hc : B (57 / 100) (23 / 40) c) : B (-1340007569541929686719 / 1000000000000000000) (-1286555084849143513087 / 1000000000000000000) ((((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) - (s3rs 12225 46 maskSlack)) := bsub (sGlobal45_hz111 hc) sGlobal45_hz29 (by norm_num) (by norm_num)

theorem sGlobal45_hz113 {c : ℝ} (hc : B (57 / 100) (23 / 40) c) : B (-1340007569541929686719 / 1000000000000000000) (-1286555084849143513087 / 1000000000000000000) (s3L 12225 46 maskSlack c) := by
    convert (sGlobal45_hz112 hc) using 1 <;>
      norm_num [s3L] <;> ring

theorem sGlobal45_hz114 {c : ℝ} (hc : B (57 / 100) (23 / 40) c) : B 0 (257059868128132525631 / 250000000000000000) |(s3U 12225 46 maskSlack c)| := bweaken (babs (sGlobal45_hz107 hc)) (by norm_num) (by norm_num)

theorem sGlobal45_hz115 {c : ℝ} (hc : B (57 / 100) (23 / 40) c) : B 0 (1340007569541929686719 / 1000000000000000000) |(s3L 12225 46 maskSlack c)| := bweaken (babs (sGlobal45_hz113 hc)) (by norm_num) (by norm_num)

theorem sGlobal45_hz116 {c : ℝ} (hc : B (57 / 100) (23 / 40) c) : B 0 (1340007569541929686719 / 1000000000000000000) (max |(s3U 12225 46 maskSlack c)| |(s3L 12225 46 maskSlack c)|) := bweaken (bmax (sGlobal45_hz114 hc) (sGlobal45_hz115 hc)) (by norm_num) (by norm_num)

theorem sGlobal45_hz117 {c : ℝ} (hc : B (57 / 100) (23 / 40) c) : B 0 (1340007569541929686719 / 1000000000000000000) (s3nks 12225 46 maskSlack c) := by
    convert (sGlobal45_hz116 hc) using 1 <;>
      norm_num [s3nks] <;> ring

theorem sGlobal45 {c : ℝ} (hc : B (57 / 100) (23 / 40) c) :
    0 < s3am 12225 46 ∧ 0 ≤ s3dm 12225 46 c ∧
    s3dm 12225 46 c ^ 2 ≤ 2 * s3ap 12225 46 ^ 2 ∧ s3c1 12225 46 c < 1 ∧
    0 ≤ s3Cpa 12225 c - s3r1 12225 46 ∧
    s3e0 12225 46 ≤ (s3Cpa 12225 c - s3r1 12225 46) / s3ap 12225 46 ∧
    s3nks 12225 46 maskSlack c ≤ 12225 * (109613 / 1000000) := by

  refine ⟨lt_of_lt_of_le (by norm_num) sGlobal45_hz14.1,
    le_trans (by norm_num) (sGlobal45_hz64 hc).1, ?_,
    lt_of_le_of_lt (sGlobal45_hz72 hc).2 (by norm_num), ?_, ?_,
    le_trans (sGlobal45_hz117 hc).2 (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (sGlobal45_hz64 hc).1) (sGlobal45_hz64 hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) sGlobal45_hz9.1 2
    nlinarith only [h1, h2]
  · linarith only [(sGlobal45_hz84 hc).1, sGlobal45_hz33.2]
  · have hap : 0 < s3ap 12225 46 := lt_of_lt_of_le (by norm_num) sGlobal45_hz9.1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul sGlobal45_hz16.2 sGlobal45_hz9.2 (le_trans (by norm_num) sGlobal45_hz9.1) (by norm_num)
    linarith only [h, (sGlobal45_hz84 hc).1, sGlobal45_hz33.2]

end BstLean.Part255
