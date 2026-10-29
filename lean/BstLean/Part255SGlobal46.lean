import BstLean.Part255SGlobal42
import BstLean.Part255Numeric10
namespace BstLean.Part255
open Real BstLean.Part130 BstLean.Part182 BstLean.Part197 BstLean.Part246
theorem sGlobal46_hz0 : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal46_hz1 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) ((√(23 : ℝ)) / (12225 : ℝ)) := bdiv sGlobal46_hz0 (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal46_hz2 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) maskSlack := by
    convert sGlobal46_hz1 using 1 <;>
      norm_num [maskSlack] <;> ring

theorem sGlobal46_hz3 : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal46_hz4 : B (6395294793910793 / 500000000000000000) (12790589587821587 / 1000000000000000000) (√((2 / 12225) : ℝ)) := bsqrt (bpoint ((2 / 12225) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal46_hz5 : B (7230130686979 / 62500000000000000) (23136418198333 / 200000000000000000) (√((2 / 149450625) : ℝ)) := bsqrt (bpoint ((2 / 149450625) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal46_hz6 : B (2211334438749598093 / 20000000000000000) (110566721937479904651 / 1000000000000000000) (√(12225 : ℝ)) := bsqrt (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal46_hz7 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))) := bmul sGlobal46_hz3 sGlobal46_hz4 (by norm_num) (by norm_num)

theorem sGlobal46_hz8 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) ((√(12225 : ℝ)) + ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := badd sGlobal46_hz6 sGlobal46_hz7 (by norm_num) (by norm_num)

theorem sGlobal46_hz9 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) (s3ap 12225 46) := by
    convert sGlobal46_hz8 using 1 <;>
      norm_num [s3ap, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal46_hz10 : B (163599182004089 / 1000000000000000000) (16359918200409 / 100000000000000000) ((2 : ℝ) / (12225 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal46_hz11 : B (1222499983640081799591 / 100000000000000000) (12224999836400817995911 / 1000000000000000000) ((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ))) := bsub (bpoint (12225 : ℝ)) sGlobal46_hz10 (by norm_num) (by norm_num)

theorem sGlobal46_hz12 : B (110566721197658827907 / 1000000000000000000) (27641680299414706977 / 250000000000000000) (√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) := bsqrt sGlobal46_hz11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal46_hz13 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) ((√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) - ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bsub sGlobal46_hz12 sGlobal46_hz7 (by norm_num) (by norm_num)

theorem sGlobal46_hz14 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) (s3am 12225 46) := by
    convert sGlobal46_hz13 using 1 <;>
      norm_num [s3am, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal46_hz15 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√((2 / 12225) : ℝ)) * (√(92 : ℝ))) := bmul sGlobal46_hz4 sGlobal46_hz3 (by norm_num) (by norm_num)

theorem sGlobal46_hz16 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) (s3e0 12225 46) := by
    convert sGlobal46_hz15 using 1 <;>
      norm_num [s3e0, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal46_hz17 : B (250196148528560847 / 500000000000000000) (100078459411424339 / 200000000000000000) (((1 / 2) : ℝ) + maskSlack) := badd (bpoint ((1 / 2) : ℝ)) sGlobal46_hz2 (by norm_num) (by norm_num)

theorem sGlobal46_hz18 : B (59827153232297998295487 / 800000000000000) (23930861292919199366019 / 320000000000000) ((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack)) := bmul (bpoint (149450625 : ℝ)) sGlobal46_hz17 (by norm_num) (by norm_num)

theorem sGlobal46_hz19 : B (1729554180017180009583 / 200000000000000000) (8647770900085900056557 / 1000000000000000000) (√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) := bsqrt sGlobal46_hz18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal46_hz20 : B (4328681281566262743499 / 500000000000000000) (8657362563132525495641 / 1000000000000000000) ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))) := badd sGlobal46_hz19 sGlobal46_hz3 (by norm_num) (by norm_num)

theorem sGlobal46_hz21 : B (110732771457999278473 / 1000000000000000000) (55366385728999643621 / 500000000000000000) ((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ)))) := bmul sGlobal46_hz4 sGlobal46_hz20 (by norm_num) (by norm_num)

theorem sGlobal46_hz22 : B (209099159 / 15625000000000000) (13382346177 / 1000000000000000000) ((2 : ℝ) / (149450625 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (149450625 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal46_hz23 : B (2452349334953899930479 / 200000000000000000) (12261746674769501594427 / 1000000000000000000) (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2) := bsq sGlobal46_hz21 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal46_hz24 : B (82045469362091 / 500000000000000000) (32818187747289 / 200000000000000000) (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2)) := bmul sGlobal46_hz22 sGlobal46_hz23 (by norm_num) (by norm_num)

theorem sGlobal46_hz25 : B (82045469362091 / 250000000000000000) (32818187747289 / 100000000000000000) ((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) := bmul (bpoint (2 : ℝ)) sGlobal46_hz24 (by norm_num) (by norm_num)

theorem sGlobal46_hz26 : B (117258080744995992792057 / 1000000000000000000) (58629040372497996396029 / 500000000000000000) (√(13749457500 : ℝ)) := bsqrt (bpoint (13749457500 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal46_hz27 : B (117304080744995992792057 / 1000000000000000000) (58652040372497996396029 / 500000000000000000) ((√(13749457500 : ℝ)) + (46 : ℝ)) := badd sGlobal46_hz26 (bpoint (46 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal46_hz28 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal46_hz25 sGlobal46_hz27 (by norm_num) (by norm_num)

theorem sGlobal46_hz29 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (s3rs 12225 46 maskSlack) := by
    convert sGlobal46_hz28 using 1 <;>
      norm_num [s3rs, s3pp, s3K, mA, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal46_hz30 : B (490797546012267 / 1000000000000000000) (49079754601227 / 100000000000000000) ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (3 : ℝ)) sGlobal46_hz10 (by norm_num) (by norm_num)

theorem sGlobal46_hz31 : B (490797546012267 / 500000000000000000) (49079754601227 / 50000000000000000) ((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal46_hz30 (by norm_num) (by norm_num)

theorem sGlobal46_hz32 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal46_hz31 sGlobal46_hz27 (by norm_num) (by norm_num)

theorem sGlobal46_hz33 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (s3r1 12225 46) := by
    convert sGlobal46_hz32 using 1 <;>
      norm_num [s3r1, mA] <;> ring

theorem sGlobal46_hz34 : B (163599182004089 / 500000000000000000) (16359918200409 / 50000000000000000) ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (2 : ℝ)) sGlobal46_hz10 (by norm_num) (by norm_num)

theorem sGlobal46_hz35 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal46_hz34 (by norm_num) (by norm_num)

theorem sGlobal46_hz36 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal46_hz35 sGlobal46_hz27 (by norm_num) (by norm_num)

theorem sGlobal46_hz37 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (s3rpp 12225 46) := by
    convert sGlobal46_hz36 using 1 <;>
      norm_num [s3rpp, mA] <;> ring

theorem sGlobal46_hz38 {c : ℝ} (hc : B (23 / 40) (29 / 50) c) : B (23 / 40) (29 / 50) c := hc

theorem sGlobal46_hz39 : B (138999591328215007 / 200000000000000000) (347498978320537669 / 500000000000000000) (kdot ((23 / 40))) := by
    constructor
    · apply bkdot_lower (q := (259731240824659867 / 500000000000000000)) (a := (239548044686568563 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (519462481649319733 / 1000000000000000000)) (a := (479096089373136653 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal46_hz40 : B (529 / 1600) (529 / 1600) (((23 / 40) : ℝ)^2) := bsq (bpoint ((23 / 40) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal46_hz41 : B (1071 / 1600) (1071 / 1600) ((1 : ℝ) - (((23 / 40) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal46_hz40 (by norm_num) (by norm_num)

theorem sGlobal46_hz42 : B (40907670429883929 / 50000000000000000) (818153408597678581 / 1000000000000000000) (√((1 : ℝ) - (((23 / 40) : ℝ)^2))) := bsqrt sGlobal46_hz41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal46_hz43 : B (260426318371607453 / 1000000000000000000) (130213159185803727 / 500000000000000000) ((√((1 : ℝ) - (((23 / 40) : ℝ)^2))) / Real.pi) := bdiv sGlobal46_hz42 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal46_hz44 : B (79924765013723629 / 200000000000000000) (4995297813357729 / 12500000000000000) (((23 / 40) : ℝ) * (kdot ((23 / 40)))) := bmul (bpoint ((23 / 40) : ℝ)) sGlobal46_hz39 (by norm_num) (by norm_num)

theorem sGlobal46_hz45 : B (330025071720112799 / 500000000000000000) (330025071720112887 / 500000000000000000) (((√((1 : ℝ) - (((23 / 40) : ℝ)^2))) / Real.pi) + (((23 / 40) : ℝ) * (kdot ((23 / 40))))) := badd sGlobal46_hz43 sGlobal46_hz44 (by norm_num) (by norm_num)

theorem sGlobal46_hz46 : B (330025071720112799 / 500000000000000000) (330025071720112887 / 500000000000000000) (kappa ((23 / 40))) := by rw [kappa_eq]; exact sGlobal46_hz45

theorem sGlobal46_hz47 : B (2722451012134883 / 3906250000000000) (696947459106530257 / 1000000000000000000) (kdot ((29 / 50))) := by
    constructor
    · apply bkdot_lower (q := (515580046947248127 / 1000000000000000000)) (a := (238016909030661399 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (257790023473624063 / 500000000000000000)) (a := (47603381806132247 / 100000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal46_hz48 : B (841 / 2500) (841 / 2500) (((29 / 50) : ℝ)^2) := bsq (bpoint ((29 / 50) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal46_hz49 : B (1659 / 2500) (1659 / 2500) ((1 : ℝ) - (((29 / 50) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal46_hz48 (by norm_num) (by norm_num)

theorem sGlobal46_hz50 : B (20365411854416301 / 25000000000000000) (814616474176652041 / 1000000000000000000) (√((1 : ℝ) - (((29 / 50) : ℝ)^2))) := bsqrt sGlobal46_hz49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal46_hz51 : B (259300477178610963 / 1000000000000000000) (64825119294652741 / 250000000000000000) ((√((1 : ℝ) - (((29 / 50) : ℝ)^2))) / Real.pi) := bdiv sGlobal46_hz50 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal46_hz52 : B (404229526281787427 / 1000000000000000000) (8084590525635751 / 20000000000000000) (((29 / 50) : ℝ) * (kdot ((29 / 50)))) := bmul (bpoint ((29 / 50) : ℝ)) sGlobal46_hz47 (by norm_num) (by norm_num)

theorem sGlobal46_hz53 : B (66353000346039839 / 100000000000000000) (331765001730199257 / 500000000000000000) (((√((1 : ℝ) - (((29 / 50) : ℝ)^2))) / Real.pi) + (((29 / 50) : ℝ) * (kdot ((29 / 50))))) := badd sGlobal46_hz51 sGlobal46_hz52 (by norm_num) (by norm_num)

theorem sGlobal46_hz54 : B (66353000346039839 / 100000000000000000) (331765001730199257 / 500000000000000000) (kappa ((29 / 50))) := by rw [kappa_eq]; exact sGlobal46_hz53

theorem sGlobal46_hz55 {c : ℝ} (hc : B (23 / 40) (29 / 50) c) : B (330025071720112799 / 500000000000000000) (331765001730199257 / 500000000000000000) (kappa c) := bkappa (sGlobal46_hz38 hc) (by norm_num) (by norm_num) sGlobal46_hz46.1 sGlobal46_hz54.2

theorem sGlobal46_hz56 : B 24450 24450 ((2 : ℝ) * (12225 : ℝ)) := bmul (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal46_hz57 {c : ℝ} (hc : B (23 / 40) (29 / 50) c) : B (168234998269800743 / 500000000000000000) (169974928279887201 / 500000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (sGlobal46_hz55 hc) (by norm_num) (by norm_num)

theorem sGlobal46_hz58 {c : ℝ} (hc : B (23 / 40) (29 / 50) c) : B (82266914153932563327 / 10000000000000000) (83117739928864841289 / 10000000000000000) (((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) := bmul sGlobal46_hz56 (sGlobal46_hz57 hc) (by norm_num) (by norm_num)

theorem sGlobal46_hz59 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (4 : ℝ)) sGlobal46_hz10 (by norm_num) (by norm_num)

theorem sGlobal46_hz60 {c : ℝ} (hc : B (23 / 40) (29 / 50) c) : B (411334538049826415817 / 50000000000000000) (259742916827804878517 / 31250000000000000) ((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bsub (sGlobal46_hz58 hc) sGlobal46_hz59 (by norm_num) (by norm_num)

theorem sGlobal46_hz61 {c : ℝ} (hc : B (23 / 40) (29 / 50) c) : B (90701106724209977063 / 1000000000000000000) (11396115935436179971 / 125000000000000000) (√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) := bsqrt (sGlobal46_hz60 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal46_hz62 : B (30670756373515103 / 125000000000000000) (122683025494060423 / 500000000000000000) ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal46_hz7 (by norm_num) (by norm_num)

theorem sGlobal46_hz63 {c : ℝ} (hc : B (23 / 40) (29 / 50) c) : B (90455740673221856217 / 1000000000000000000) (2841361294765666217 / 31250000000000000) ((√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) - ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))))) := bsub (sGlobal46_hz61 hc) sGlobal46_hz62 (by norm_num) (by norm_num)

theorem sGlobal46_hz64 {c : ℝ} (hc : B (23 / 40) (29 / 50) c) : B (90455740673221856217 / 1000000000000000000) (2841361294765666217 / 31250000000000000) (s3dm 12225 46 c) := by
    convert (sGlobal46_hz63 hc) using 1 <;>
      norm_num [s3dm, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal46_hz65 : B (6126072185528622723889 / 500000000000000000) (2450428874211449090087 / 200000000000000000) ((s3ap 12225 46)^2) := bsq sGlobal46_hz9 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal46_hz66 : B (6126072185528622723889 / 250000000000000000) (2450428874211449090087 / 100000000000000000) ((2 : ℝ) * ((s3ap 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal46_hz65 (by norm_num) (by norm_num)

theorem sGlobal46_hz67 {c : ℝ} (hc : B (23 / 40) (29 / 50) c) : B (255695031898161338431 / 31250000000000000) (2066773505892460324557 / 250000000000000000) ((s3dm 12225 46 c)^2) := bsq (sGlobal46_hz64 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal46_hz68 {c : ℝ} (hc : B (23 / 40) (29 / 50) c) : B (1014824669909040599833 / 62500000000000000) (8161023860686664035539 / 500000000000000000) (((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) := bsub sGlobal46_hz66 (sGlobal46_hz67 hc) (by norm_num) (by norm_num)

theorem sGlobal46_hz69 : B (1524735695971823534271 / 125000000000000000) (609894278388729413841 / 50000000000000000) ((s3am 12225 46)^2) := bsq sGlobal46_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal46_hz70 : B (1524735695971823534271 / 62500000000000000) (609894278388729413841 / 25000000000000000) ((2 : ℝ) * ((s3am 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal46_hz69 (by norm_num) (by norm_num)

theorem sGlobal46_hz71 {c : ℝ} (hc : B (23 / 40) (29 / 50) c) : B (665574153336929633 / 1000000000000000000) (334526169119308313 / 500000000000000000) ((((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) / ((2 : ℝ) * ((s3am 12225 46)^2))) := bdiv (sGlobal46_hz68 hc) sGlobal46_hz70 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal46_hz72 {c : ℝ} (hc : B (23 / 40) (29 / 50) c) : B (665574153336929633 / 1000000000000000000) (334526169119308313 / 500000000000000000) (s3c1 12225 46 c) := by
    convert (sGlobal46_hz71 hc) using 1 <;>
      norm_num [s3c1] <;> ring

theorem sGlobal46_hz73 {c : ℝ} (hc : B (23 / 40) (29 / 50) c) : B (138999591328215007 / 200000000000000000) (696947459106530257 / 1000000000000000000) (kdot c) := bkdot (sGlobal46_hz38 hc) sGlobal46_hz39.1 sGlobal46_hz47.2

theorem sGlobal46_hz74 : B (365906633214944603 / 500000000000000000) (91476658303736151 / 125000000000000000) (kdot ((665574153336929633 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (448092764463468557 / 1000000000000000000)) (a := (210633367993525813 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (112023191115867139 / 250000000000000000)) (a := (52658341998381453 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal46_hz75 : B (146659962095910873 / 200000000000000000) (733299810479554367 / 1000000000000000000) (kdot ((334526169119308313 / 500000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (222645891300009649 / 500000000000000000)) (a := (13091614939194337 / 31250000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (445291782600019297 / 1000000000000000000)) (a := (209465839027109391 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal46_hz76 {c : ℝ} (hc : B (23 / 40) (29 / 50) c) : B (365906633214944603 / 500000000000000000) (733299810479554367 / 1000000000000000000) (kdot (s3c1 12225 46 c)) := bkdot (sGlobal46_hz72 hc) sGlobal46_hz74.1 sGlobal46_hz75.2

theorem sGlobal46_hz77 {c : ℝ} (hc : B (23 / 40) (29 / 50) c) : B (529 / 1600) (841 / 2500) (c^2) := bsq (sGlobal46_hz38 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal46_hz78 {c : ℝ} (hc : B (23 / 40) (29 / 50) c) : B (1659 / 2500) (1071 / 1600) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (sGlobal46_hz77 hc) (by norm_num) (by norm_num)

theorem sGlobal46_hz79 {c : ℝ} (hc : B (23 / 40) (29 / 50) c) : B (20365411854416301 / 25000000000000000) (818153408597678581 / 1000000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (sGlobal46_hz78 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal46_hz80 : B (39119999999999765769 / 1600000000000000) (3912000000000000489 / 160000000000000) ((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (149450625 : ℝ)) sGlobal46_hz10 (by norm_num) (by norm_num)

theorem sGlobal46_hz81 {c : ℝ} (hc : B (23 / 40) (29 / 50) c) : B (113231356999786047 / 200000000000000000) (285104969640749467 / 500000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (sGlobal46_hz79 hc) (sGlobal46_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal46_hz82 {c : ℝ} (hc : B (23 / 40) (29 / 50) c) : B (13842533393223761363581 / 1000000000000000000) (2788326603086530135801 / 200000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) := bmul sGlobal46_hz80 (sGlobal46_hz81 hc) (by norm_num) (by norm_num)

theorem sGlobal46_hz83 {c : ℝ} (hc : B (23 / 40) (29 / 50) c) : B (692126669661188068179 / 100000000000000000) (6970816507716325339503 / 1000000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) / (2 : ℝ)) := bdiv (sGlobal46_hz82 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal46_hz84 {c : ℝ} (hc : B (23 / 40) (29 / 50) c) : B (692126669661188068179 / 100000000000000000) (6970816507716325339503 / 1000000000000000000) (s3Cpa 12225 c) := by
    convert (sGlobal46_hz83 hc) using 1 <;>
      norm_num [s3Cpa, mA] <;> ring

theorem sGlobal46_hz85 {c : ℝ} (hc : B (23 / 40) (29 / 50) c) : B (259300477178610963 / 1000000000000000000) (130213159185803727 / 500000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (sGlobal46_hz79 hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal46_hz86 {c : ℝ} (hc : B (23 / 40) (29 / 50) c) : B (79924765013723629 / 200000000000000000) (8084590525635751 / 20000000000000000) (c * (kdot c)) := bmul (sGlobal46_hz38 hc) (sGlobal46_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal46_hz87 {c : ℝ} (hc : B (23 / 40) (29 / 50) c) : B (-144929049103176587 / 1000000000000000000) (-139197506697010691 / 1000000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (sGlobal46_hz85 hc) (sGlobal46_hz86 hc) (by norm_num) (by norm_num)

theorem sGlobal46_hz88 {c : ℝ} (hc : B (23 / 40) (29 / 50) c) : B (-354351525057266799509 / 100000000000000000) (-1701689519370945508609 / 500000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) := bmul sGlobal46_hz80 (sGlobal46_hz87 hc) (by norm_num) (by norm_num)

theorem sGlobal46_hz89 {c : ℝ} (hc : B (23 / 40) (29 / 50) c) : B (-354351525057266799509 / 200000000000000000) (-1701689519370945508609 / 1000000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) / (2 : ℝ)) := bdiv (sGlobal46_hz88 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal46_hz90 {c : ℝ} (hc : B (23 / 40) (29 / 50) c) : B (-354351525057266799509 / 200000000000000000) (-1701689519370945508609 / 1000000000000000000) (s3Cpp 12225 c) := by
    convert (sGlobal46_hz89 hc) using 1 <;>
      norm_num [s3Cpp, mA] <;> ring

theorem sGlobal46_hz91 {c : ℝ} (hc : B (23 / 40) (29 / 50) c) : B (7036411806545618390191 / 1000000000000000000) (7085961617650063751729 / 1000000000000000000) ((s3Cpa 12225 c) + (s3r1 12225 46)) := badd (sGlobal46_hz84 hc) sGlobal46_hz33 (by norm_num) (by norm_num)

theorem sGlobal46_hz92 {c : ℝ} (hc : B (23 / 40) (29 / 50) c) : B (2548408016583735031 / 40000000000000000) (801985527571457909 / 12500000000000000) (((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) := bdiv (sGlobal46_hz91 hc) sGlobal46_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal46_hz93 {c : ℝ} (hc : B (23 / 40) (29 / 50) c) : B (63832883440087436187 / 1000000000000000000) (64281525231210693143 / 1000000000000000000) ((((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) + (s3e0 12225 46)) := badd (sGlobal46_hz92 hc) sGlobal46_hz16 (by norm_num) (by norm_num)

theorem sGlobal46_hz94 {c : ℝ} (hc : B (23 / 40) (29 / 50) c) : B (63832883440087436187 / 1000000000000000000) (64281525231210693143 / 1000000000000000000) (s3Lam 12225 46 c) := by
    convert (sGlobal46_hz93 hc) using 1 <;>
      norm_num [s3Lam] <;> ring

theorem sGlobal46_hz95 {c : ℝ} (hc : B (23 / 40) (29 / 50) c) : B (-338998843732768438389 / 200000000000000000) (-1624926112748453233791 / 1000000000000000000) ((s3Cpp 12225 c) + (s3rpp 12225 46)) := badd (sGlobal46_hz90 hc) sGlobal46_hz37 (by norm_num) (by norm_num)

theorem sGlobal46_hz96 {c : ℝ} (hc : B (23 / 40) (29 / 50) c) : B (-155367367413766976603 / 125000000000000000) (-162492611274845323379 / 200000000000000000) (if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) := bweaken (bfirst (sGlobal46_hz95 hc) (sGlobal46_hz76 hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem sGlobal46_hz97 {c : ℝ} (hc : B (23 / 40) (29 / 50) c) : B (2037318504137894420733 / 500000000000000000) (4132114486050776956537 / 1000000000000000000) ((s3Lam 12225 46 c)^2) := bsq (sGlobal46_hz94 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal46_hz98 {c : ℝ} (hc : B (23 / 40) (29 / 50) c) : B (442988953590170719 / 1000000000000000000) (111907757825640067 / 250000000000000000) ((s3c1 12225 46 c)^2) := bsq (sGlobal46_hz72 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal46_hz99 {c : ℝ} (hc : B (23 / 40) (29 / 50) c) : B (138092242174359933 / 250000000000000000) (557011046409829281 / 1000000000000000000) ((1 : ℝ) - ((s3c1 12225 46 c)^2)) := bsub (bpoint (1 : ℝ)) (sGlobal46_hz98 hc) (by norm_num) (by norm_num)

theorem sGlobal46_hz100 {c : ℝ} (hc : B (23 / 40) (29 / 50) c) : B (14864305818940079 / 20000000000000000) (746331726787645871 / 1000000000000000000) (√((1 : ℝ) - ((s3c1 12225 46 c)^2))) := bsqrt (sGlobal46_hz99 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal46_hz101 {c : ℝ} (hc : B (23 / 40) (29 / 50) c) : B (18679037584597667 / 8000000000000000) (1172335135008526483 / 500000000000000000) (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))) := bmul pi_mem (sGlobal46_hz100 hc) (by norm_num) (by norm_num)

theorem sGlobal46_hz102 {c : ℝ} (hc : B (23 / 40) (29 / 50) c) : B (868914717003289698217 / 500000000000000000) (353946671381658743881 / 200000000000000000) (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2))))) := bdiv (sGlobal46_hz97 hc) (sGlobal46_hz101 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal46_hz103 {c : ℝ} (hc : B (23 / 40) (29 / 50) c) : B (49489049469644358361 / 100000000000000000) (95727030053406710251 / 100000000000000000) ((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) := badd (sGlobal46_hz96 hc) (sGlobal46_hz102 hc) (by norm_num) (by norm_num)

theorem sGlobal46_hz104 : B (3762781186094069 / 250000000000000000) (376278118609407 / 25000000000000000) ((s3e0 12225 46)^2) := bsq sGlobal46_hz16 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal46_hz105 {c : ℝ} (hc : B (23 / 40) (29 / 50) c) : B (247452772910593979943 / 500000000000000000) (95728535165881147879 / 100000000000000000) (((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) := badd (sGlobal46_hz103 hc) sGlobal46_hz104 (by norm_num) (by norm_num)

theorem sGlobal46_hz106 {c : ℝ} (hc : B (23 / 40) (29 / 50) c) : B (533402619272435230017 / 1000000000000000000) (497891212556467874403 / 500000000000000000) ((((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) + (s3rs 12225 46 maskSlack)) := badd (sGlobal46_hz105 hc) sGlobal46_hz29 (by norm_num) (by norm_num)

theorem sGlobal46_hz107 {c : ℝ} (hc : B (23 / 40) (29 / 50) c) : B (533402619272435230017 / 1000000000000000000) (497891212556467874403 / 500000000000000000) (s3U 12225 46 maskSlack c) := by
    convert (sGlobal46_hz106 hc) using 1 <;>
      norm_num [s3U] <;> ring

theorem sGlobal46_hz108 {c : ℝ} (hc : B (23 / 40) (29 / 50) c) : B (-1848521031908826272363 / 1000000000000000000) (-1778452925993437314209 / 1000000000000000000) ((s3Cpp 12225 c) - (s3rpp 12225 46)) := bsub (sGlobal46_hz90 hc) sGlobal46_hz37 (by norm_num) (by norm_num)

theorem sGlobal46_hz109 {c : ℝ} (hc : B (23 / 40) (29 / 50) c) : B (-1848521031908826272363 / 1000000000000000000) (-1778452925993437314209 / 1000000000000000000) (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ)) := bweaken (bmin (sGlobal46_hz108 hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem sGlobal46_hz110 {c : ℝ} (hc : B (23 / 40) (29 / 50) c) : B (-1355520122366212576191 / 1000000000000000000) (-1301495444963051371741 / 1000000000000000000) ((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) := bmul (sGlobal46_hz76 hc) (sGlobal46_hz109 hc) (by norm_num) (by norm_num)

theorem sGlobal46_hz111 {c : ℝ} (hc : B (23 / 40) (29 / 50) c) : B (-1355535173490956952471 / 1000000000000000000) (-1301510496087795748017 / 1000000000000000000) (((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) := bsub (sGlobal46_hz110 hc) sGlobal46_hz104 (by norm_num) (by norm_num)

theorem sGlobal46_hz112 {c : ℝ} (hc : B (23 / 40) (29 / 50) c) : B (-1394032246945081222487 / 1000000000000000000) (-335001892384760754537 / 250000000000000000) ((((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) - (s3rs 12225 46 maskSlack)) := bsub (sGlobal46_hz111 hc) sGlobal46_hz29 (by norm_num) (by norm_num)

theorem sGlobal46_hz113 {c : ℝ} (hc : B (23 / 40) (29 / 50) c) : B (-1394032246945081222487 / 1000000000000000000) (-335001892384760754537 / 250000000000000000) (s3L 12225 46 maskSlack c) := by
    convert (sGlobal46_hz112 hc) using 1 <;>
      norm_num [s3L] <;> ring

theorem sGlobal46_hz114 {c : ℝ} (hc : B (23 / 40) (29 / 50) c) : B 0 (497891212556467874403 / 500000000000000000) |(s3U 12225 46 maskSlack c)| := bweaken (babs (sGlobal46_hz107 hc)) (by norm_num) (by norm_num)

theorem sGlobal46_hz115 {c : ℝ} (hc : B (23 / 40) (29 / 50) c) : B 0 (1394032246945081222487 / 1000000000000000000) |(s3L 12225 46 maskSlack c)| := bweaken (babs (sGlobal46_hz113 hc)) (by norm_num) (by norm_num)

theorem sGlobal46_hz116 {c : ℝ} (hc : B (23 / 40) (29 / 50) c) : B 0 (1394032246945081222487 / 1000000000000000000) (max |(s3U 12225 46 maskSlack c)| |(s3L 12225 46 maskSlack c)|) := bweaken (bmax (sGlobal46_hz114 hc) (sGlobal46_hz115 hc)) (by norm_num) (by norm_num)

theorem sGlobal46_hz117 {c : ℝ} (hc : B (23 / 40) (29 / 50) c) : B 0 (1394032246945081222487 / 1000000000000000000) (s3nks 12225 46 maskSlack c) := by
    convert (sGlobal46_hz116 hc) using 1 <;>
      norm_num [s3nks] <;> ring

theorem sGlobal46 {c : ℝ} (hc : B (23 / 40) (29 / 50) c) :
    0 < s3am 12225 46 ∧ 0 ≤ s3dm 12225 46 c ∧
    s3dm 12225 46 c ^ 2 ≤ 2 * s3ap 12225 46 ^ 2 ∧ s3c1 12225 46 c < 1 ∧
    0 ≤ s3Cpa 12225 c - s3r1 12225 46 ∧
    s3e0 12225 46 ≤ (s3Cpa 12225 c - s3r1 12225 46) / s3ap 12225 46 ∧
    s3nks 12225 46 maskSlack c ≤ 12225 * (7127 / 62500) := by

  refine ⟨lt_of_lt_of_le (by norm_num) sGlobal46_hz14.1,
    le_trans (by norm_num) (sGlobal46_hz64 hc).1, ?_,
    lt_of_le_of_lt (sGlobal46_hz72 hc).2 (by norm_num), ?_, ?_,
    le_trans (sGlobal46_hz117 hc).2 (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (sGlobal46_hz64 hc).1) (sGlobal46_hz64 hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) sGlobal46_hz9.1 2
    nlinarith only [h1, h2]
  · linarith only [(sGlobal46_hz84 hc).1, sGlobal46_hz33.2]
  · have hap : 0 < s3ap 12225 46 := lt_of_lt_of_le (by norm_num) sGlobal46_hz9.1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul sGlobal46_hz16.2 sGlobal46_hz9.2 (le_trans (by norm_num) sGlobal46_hz9.1) (by norm_num)
    linarith only [h, (sGlobal46_hz84 hc).1, sGlobal46_hz33.2]

end BstLean.Part255
