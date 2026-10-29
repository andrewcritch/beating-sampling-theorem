import BstLean.Part255SGlobal61
import BstLean.Part255Numeric10
namespace BstLean.Part255
open Real BstLean.Part130 BstLean.Part182 BstLean.Part197 BstLean.Part246
theorem sGlobal65_hz0 : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal65_hz1 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) ((√(23 : ℝ)) / (12225 : ℝ)) := bdiv sGlobal65_hz0 (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal65_hz2 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) maskSlack := by
    convert sGlobal65_hz1 using 1 <;>
      norm_num [maskSlack] <;> ring

theorem sGlobal65_hz3 : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal65_hz4 : B (6395294793910793 / 500000000000000000) (12790589587821587 / 1000000000000000000) (√((2 / 12225) : ℝ)) := bsqrt (bpoint ((2 / 12225) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal65_hz5 : B (7230130686979 / 62500000000000000) (23136418198333 / 200000000000000000) (√((2 / 149450625) : ℝ)) := bsqrt (bpoint ((2 / 149450625) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal65_hz6 : B (2211334438749598093 / 20000000000000000) (110566721937479904651 / 1000000000000000000) (√(12225 : ℝ)) := bsqrt (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal65_hz7 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))) := bmul sGlobal65_hz3 sGlobal65_hz4 (by norm_num) (by norm_num)

theorem sGlobal65_hz8 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) ((√(12225 : ℝ)) + ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := badd sGlobal65_hz6 sGlobal65_hz7 (by norm_num) (by norm_num)

theorem sGlobal65_hz9 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) (s3ap 12225 46) := by
    convert sGlobal65_hz8 using 1 <;>
      norm_num [s3ap, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal65_hz10 : B (163599182004089 / 1000000000000000000) (16359918200409 / 100000000000000000) ((2 : ℝ) / (12225 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal65_hz11 : B (1222499983640081799591 / 100000000000000000) (12224999836400817995911 / 1000000000000000000) ((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ))) := bsub (bpoint (12225 : ℝ)) sGlobal65_hz10 (by norm_num) (by norm_num)

theorem sGlobal65_hz12 : B (110566721197658827907 / 1000000000000000000) (27641680299414706977 / 250000000000000000) (√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) := bsqrt sGlobal65_hz11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal65_hz13 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) ((√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) - ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bsub sGlobal65_hz12 sGlobal65_hz7 (by norm_num) (by norm_num)

theorem sGlobal65_hz14 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) (s3am 12225 46) := by
    convert sGlobal65_hz13 using 1 <;>
      norm_num [s3am, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal65_hz15 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√((2 / 12225) : ℝ)) * (√(92 : ℝ))) := bmul sGlobal65_hz4 sGlobal65_hz3 (by norm_num) (by norm_num)

theorem sGlobal65_hz16 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) (s3e0 12225 46) := by
    convert sGlobal65_hz15 using 1 <;>
      norm_num [s3e0, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal65_hz17 : B (250196148528560847 / 500000000000000000) (100078459411424339 / 200000000000000000) (((1 / 2) : ℝ) + maskSlack) := badd (bpoint ((1 / 2) : ℝ)) sGlobal65_hz2 (by norm_num) (by norm_num)

theorem sGlobal65_hz18 : B (59827153232297998295487 / 800000000000000) (23930861292919199366019 / 320000000000000) ((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack)) := bmul (bpoint (149450625 : ℝ)) sGlobal65_hz17 (by norm_num) (by norm_num)

theorem sGlobal65_hz19 : B (1729554180017180009583 / 200000000000000000) (8647770900085900056557 / 1000000000000000000) (√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) := bsqrt sGlobal65_hz18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal65_hz20 : B (4328681281566262743499 / 500000000000000000) (8657362563132525495641 / 1000000000000000000) ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))) := badd sGlobal65_hz19 sGlobal65_hz3 (by norm_num) (by norm_num)

theorem sGlobal65_hz21 : B (110732771457999278473 / 1000000000000000000) (55366385728999643621 / 500000000000000000) ((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ)))) := bmul sGlobal65_hz4 sGlobal65_hz20 (by norm_num) (by norm_num)

theorem sGlobal65_hz22 : B (209099159 / 15625000000000000) (13382346177 / 1000000000000000000) ((2 : ℝ) / (149450625 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (149450625 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal65_hz23 : B (2452349334953899930479 / 200000000000000000) (12261746674769501594427 / 1000000000000000000) (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2) := bsq sGlobal65_hz21 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal65_hz24 : B (82045469362091 / 500000000000000000) (32818187747289 / 200000000000000000) (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2)) := bmul sGlobal65_hz22 sGlobal65_hz23 (by norm_num) (by norm_num)

theorem sGlobal65_hz25 : B (82045469362091 / 250000000000000000) (32818187747289 / 100000000000000000) ((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) := bmul (bpoint (2 : ℝ)) sGlobal65_hz24 (by norm_num) (by norm_num)

theorem sGlobal65_hz26 : B (117258080744995992792057 / 1000000000000000000) (58629040372497996396029 / 500000000000000000) (√(13749457500 : ℝ)) := bsqrt (bpoint (13749457500 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal65_hz27 : B (117304080744995992792057 / 1000000000000000000) (58652040372497996396029 / 500000000000000000) ((√(13749457500 : ℝ)) + (46 : ℝ)) := badd sGlobal65_hz26 (bpoint (46 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal65_hz28 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal65_hz25 sGlobal65_hz27 (by norm_num) (by norm_num)

theorem sGlobal65_hz29 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (s3rs 12225 46 maskSlack) := by
    convert sGlobal65_hz28 using 1 <;>
      norm_num [s3rs, s3pp, s3K, mA, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal65_hz30 : B (490797546012267 / 1000000000000000000) (49079754601227 / 100000000000000000) ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (3 : ℝ)) sGlobal65_hz10 (by norm_num) (by norm_num)

theorem sGlobal65_hz31 : B (490797546012267 / 500000000000000000) (49079754601227 / 50000000000000000) ((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal65_hz30 (by norm_num) (by norm_num)

theorem sGlobal65_hz32 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal65_hz31 sGlobal65_hz27 (by norm_num) (by norm_num)

theorem sGlobal65_hz33 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (s3r1 12225 46) := by
    convert sGlobal65_hz32 using 1 <;>
      norm_num [s3r1, mA] <;> ring

theorem sGlobal65_hz34 : B (163599182004089 / 500000000000000000) (16359918200409 / 50000000000000000) ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (2 : ℝ)) sGlobal65_hz10 (by norm_num) (by norm_num)

theorem sGlobal65_hz35 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal65_hz34 (by norm_num) (by norm_num)

theorem sGlobal65_hz36 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal65_hz35 sGlobal65_hz27 (by norm_num) (by norm_num)

theorem sGlobal65_hz37 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (s3rpp 12225 46) := by
    convert sGlobal65_hz36 using 1 <;>
      norm_num [s3rpp, mA] <;> ring

theorem sGlobal65_hz38 {c : ℝ} (hc : B (67 / 100) (27 / 40) c) : B (67 / 100) (27 / 40) c := hc

theorem sGlobal65_hz39 : B (73370591556941763 / 100000000000000000) (22928309861544301 / 31250000000000000) (kdot ((67 / 100))) := by
    constructor
    · apply bkdot_lower (q := (222263801831945679 / 500000000000000000)) (a := (52286721208846107 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (444527603663891357 / 1000000000000000000)) (a := (209146884835384427 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal65_hz40 : B (4489 / 10000) (4489 / 10000) (((67 / 100) : ℝ)^2) := bsq (bpoint ((67 / 100) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal65_hz41 : B (5511 / 10000) (5511 / 10000) ((1 : ℝ) - (((67 / 100) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal65_hz40 (by norm_num) (by norm_num)

theorem sGlobal65_hz42 : B (371180549059349283 / 500000000000000000) (742361098118698567 / 1000000000000000000) (√((1 : ℝ) - (((67 / 100) : ℝ)^2))) := bsqrt sGlobal65_hz41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal65_hz43 : B (236300876649436799 / 1000000000000000000) (236300876649436801 / 1000000000000000000) ((√((1 : ℝ) - (((67 / 100) : ℝ)^2))) / Real.pi) := bdiv sGlobal65_hz42 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal65_hz44 : B (122895740857877453 / 250000000000000000) (245791481715754907 / 500000000000000000) (((67 / 100) : ℝ) * (kdot ((67 / 100)))) := bmul (bpoint ((67 / 100) : ℝ)) sGlobal65_hz39 (by norm_num) (by norm_num)

theorem sGlobal65_hz45 : B (727883840080946611 / 1000000000000000000) (145576768016189323 / 200000000000000000) (((√((1 : ℝ) - (((67 / 100) : ℝ)^2))) / Real.pi) + (((67 / 100) : ℝ) * (kdot ((67 / 100))))) := badd sGlobal65_hz43 sGlobal65_hz44 (by norm_num) (by norm_num)

theorem sGlobal65_hz46 : B (727883840080946611 / 1000000000000000000) (145576768016189323 / 200000000000000000) (kappa ((67 / 100))) := by rw [kappa_eq]; exact sGlobal65_hz45

theorem sGlobal65_hz47 : B (147171278004889929 / 200000000000000000) (735856390024449647 / 1000000000000000000) (kdot ((27 / 40))) := by
    constructor
    · apply bkdot_lower (q := (440488195921603167 / 1000000000000000000)) (a := (41491581229593831 / 100000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (220244097960801583 / 500000000000000000)) (a := (103728953073984577 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal65_hz48 : B (729 / 1600) (729 / 1600) (((27 / 40) : ℝ)^2) := bsq (bpoint ((27 / 40) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal65_hz49 : B (871 / 1600) (871 / 1600) ((1 : ℝ) - (((27 / 40) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal65_hz48 (by norm_num) (by norm_num)

theorem sGlobal65_hz50 : B (92227216021085663 / 125000000000000000) (147563545633737061 / 200000000000000000) (√((1 : ℝ) - (((27 / 40) : ℝ)^2))) := bsqrt sGlobal65_hz49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal65_hz51 : B (234854677077757223 / 1000000000000000000) (29356834634719653 / 125000000000000000) ((√((1 : ℝ) - (((27 / 40) : ℝ)^2))) / Real.pi) := bdiv sGlobal65_hz50 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal65_hz52 : B (49670306326650351 / 100000000000000000) (62087882908312939 / 125000000000000000) (((27 / 40) : ℝ) * (kdot ((27 / 40)))) := bmul (bpoint ((27 / 40) : ℝ)) sGlobal65_hz47 (by norm_num) (by norm_num)

theorem sGlobal65_hz53 : B (731557740344260733 / 1000000000000000000) (5715294846439537 / 7812500000000000) (((√((1 : ℝ) - (((27 / 40) : ℝ)^2))) / Real.pi) + (((27 / 40) : ℝ) * (kdot ((27 / 40))))) := badd sGlobal65_hz51 sGlobal65_hz52 (by norm_num) (by norm_num)

theorem sGlobal65_hz54 : B (731557740344260733 / 1000000000000000000) (5715294846439537 / 7812500000000000) (kappa ((27 / 40))) := by rw [kappa_eq]; exact sGlobal65_hz53

theorem sGlobal65_hz55 {c : ℝ} (hc : B (67 / 100) (27 / 40) c) : B (727883840080946611 / 1000000000000000000) (5715294846439537 / 7812500000000000) (kappa c) := bkappa (sGlobal65_hz38 hc) (by norm_num) (by norm_num) sGlobal65_hz46.1 sGlobal65_hz54.2

theorem sGlobal65_hz56 : B 24450 24450 ((2 : ℝ) * (12225 : ℝ)) := bmul (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal65_hz57 {c : ℝ} (hc : B (67 / 100) (27 / 40) c) : B (2097205153560463 / 7812500000000000) (272116159919053389 / 1000000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (sGlobal65_hz55 hc) (by norm_num) (by norm_num)

theorem sGlobal65_hz58 {c : ℝ} (hc : B (67 / 100) (27 / 40) c) : B (1025533320091066407 / 156250000000000) (133064802200417107221 / 20000000000000000) (((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) := bmul sGlobal65_hz56 (sGlobal65_hz57 hc) (by norm_num) (by norm_num)

theorem sGlobal65_hz59 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (4 : ℝ)) sGlobal65_hz10 (by norm_num) (by norm_num)

theorem sGlobal65_hz60 {c : ℝ} (hc : B (67 / 100) (27 / 40) c) : B (164085314854652424711 / 25000000000000000) (3326619727812063672347 / 500000000000000000) ((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bsub (sGlobal65_hz58 hc) sGlobal65_hz59 (by norm_num) (by norm_num)

theorem sGlobal65_hz61 {c : ℝ} (hc : B (67 / 100) (27 / 40) c) : B (16202978237578543373 / 200000000000000000) (81567392109985515613 / 1000000000000000000) (√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) := bsqrt (sGlobal65_hz60 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal65_hz62 : B (30670756373515103 / 125000000000000000) (122683025494060423 / 500000000000000000) ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal65_hz7 (by norm_num) (by norm_num)

theorem sGlobal65_hz63 {c : ℝ} (hc : B (67 / 100) (27 / 40) c) : B (80769525136904596019 / 1000000000000000000) (81322026058997394789 / 1000000000000000000) ((√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) - ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))))) := bsub (sGlobal65_hz61 hc) sGlobal65_hz62 (by norm_num) (by norm_num)

theorem sGlobal65_hz64 {c : ℝ} (hc : B (67 / 100) (27 / 40) c) : B (80769525136904596019 / 1000000000000000000) (81322026058997394789 / 1000000000000000000) (s3dm 12225 46 c) := by
    convert (sGlobal65_hz63 hc) using 1 <;>
      norm_num [s3dm, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal65_hz65 : B (6126072185528622723889 / 500000000000000000) (2450428874211449090087 / 200000000000000000) ((s3ap 12225 46)^2) := bsq sGlobal65_hz9 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal65_hz66 : B (6126072185528622723889 / 250000000000000000) (2450428874211449090087 / 100000000000000000) ((2 : ℝ) * ((s3ap 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal65_hz65 (by norm_num) (by norm_num)

theorem sGlobal65_hz67 {c : ℝ} (hc : B (67 / 100) (27 / 40) c) : B (1304743238168212680057 / 200000000000000000) (206664747573132854669 / 31250000000000000) ((s3dm 12225 46 c)^2) := bsq (sGlobal65_hz64 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal65_hz68 {c : ℝ} (hc : B (67 / 100) (27 / 40) c) : B (4472754204943559886537 / 250000000000000000) (3596114510254685500117 / 200000000000000000) (((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) := bsub sGlobal65_hz66 (sGlobal65_hz67 hc) (by norm_num) (by norm_num)

theorem sGlobal65_hz69 : B (1524735695971823534271 / 125000000000000000) (609894278388729413841 / 50000000000000000) ((s3am 12225 46)^2) := bsq sGlobal65_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal65_hz70 : B (1524735695971823534271 / 62500000000000000) (609894278388729413841 / 25000000000000000) ((2 : ℝ) * ((s3am 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal65_hz69 (by norm_num) (by norm_num)

theorem sGlobal65_hz71 {c : ℝ} (hc : B (67 / 100) (27 / 40) c) : B (733365496846447293 / 1000000000000000000) (368518224969580663 / 500000000000000000) ((((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) / ((2 : ℝ) * ((s3am 12225 46)^2))) := bdiv (sGlobal65_hz68 hc) sGlobal65_hz70 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal65_hz72 {c : ℝ} (hc : B (67 / 100) (27 / 40) c) : B (733365496846447293 / 1000000000000000000) (368518224969580663 / 500000000000000000) (s3c1 12225 46 c) := by
    convert (sGlobal65_hz71 hc) using 1 <;>
      norm_num [s3c1] <;> ring

theorem sGlobal65_hz73 {c : ℝ} (hc : B (67 / 100) (27 / 40) c) : B (73370591556941763 / 100000000000000000) (735856390024449647 / 1000000000000000000) (kdot c) := bkdot (sGlobal65_hz38 hc) sGlobal65_hz39.1 sGlobal65_hz47.2

theorem sGlobal65_hz74 : B (762051569853086557 / 1000000000000000000) (762051569853086559 / 1000000000000000000) (kdot ((733365496846447293 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (392204976537529717 / 1000000000000000000)) (a := (373768520041383679 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (98051244134382429 / 250000000000000000)) (a := (373768520041383677 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal65_hz75 : B (381887707563831743 / 500000000000000000) (5966995430684871 / 7812500000000000) (kdot ((368518224969580663 / 500000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (38908394551847361 / 100000000000000000)) (a := (185530355108057749 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (389083945518473609 / 1000000000000000000)) (a := (46382588777014437 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal65_hz76 {c : ℝ} (hc : B (67 / 100) (27 / 40) c) : B (762051569853086557 / 1000000000000000000) (5966995430684871 / 7812500000000000) (kdot (s3c1 12225 46 c)) := bkdot (sGlobal65_hz72 hc) sGlobal65_hz74.1 sGlobal65_hz75.2

theorem sGlobal65_hz77 {c : ℝ} (hc : B (67 / 100) (27 / 40) c) : B (4489 / 10000) (729 / 1600) (c^2) := bsq (sGlobal65_hz38 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal65_hz78 {c : ℝ} (hc : B (67 / 100) (27 / 40) c) : B (871 / 1600) (5511 / 10000) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (sGlobal65_hz77 hc) (by norm_num) (by norm_num)

theorem sGlobal65_hz79 {c : ℝ} (hc : B (67 / 100) (27 / 40) c) : B (92227216021085663 / 125000000000000000) (742361098118698567 / 1000000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (sGlobal65_hz78 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal65_hz80 : B (39119999999999765769 / 1600000000000000) (3912000000000000489 / 160000000000000) ((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (149450625 : ℝ)) sGlobal65_hz10 (by norm_num) (by norm_num)

theorem sGlobal65_hz81 {c : ℝ} (hc : B (67 / 100) (27 / 40) c) : B (541341231769352947 / 1000000000000000000) (273135578878105893 / 500000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (sGlobal65_hz79 hc) (sGlobal65_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal65_hz82 {c : ℝ} (hc : B (67 / 100) (27 / 40) c) : B (6617896558380300152419 / 500000000000000000) (6678164903569689918621 / 500000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) := bmul sGlobal65_hz80 (sGlobal65_hz81 hc) (by norm_num) (by norm_num)

theorem sGlobal65_hz83 {c : ℝ} (hc : B (67 / 100) (27 / 40) c) : B (6617896558380300152419 / 1000000000000000000) (6678164903569689918621 / 1000000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) / (2 : ℝ)) := bdiv (sGlobal65_hz82 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal65_hz84 {c : ℝ} (hc : B (67 / 100) (27 / 40) c) : B (6617896558380300152419 / 1000000000000000000) (6678164903569689918621 / 1000000000000000000) (s3Cpa 12225 c) := by
    convert (sGlobal65_hz83 hc) using 1 <;>
      norm_num [s3Cpa, mA] <;> ring

theorem sGlobal65_hz85 {c : ℝ} (hc : B (67 / 100) (27 / 40) c) : B (234854677077757223 / 1000000000000000000) (236300876649436801 / 1000000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (sGlobal65_hz79 hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal65_hz86 {c : ℝ} (hc : B (67 / 100) (27 / 40) c) : B (122895740857877453 / 250000000000000000) (62087882908312939 / 125000000000000000) (c * (kdot c)) := bmul (sGlobal65_hz38 hc) (sGlobal65_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal65_hz87 {c : ℝ} (hc : B (67 / 100) (27 / 40) c) : B (-261848386188746289 / 1000000000000000000) (-255282086782073011 / 1000000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (sGlobal65_hz85 hc) (sGlobal65_hz86 hc) (by norm_num) (by norm_num)

theorem sGlobal65_hz88 {c : ℝ} (hc : B (67 / 100) (27 / 40) c) : B (-256087721692593902653 / 40000000000000000) (-390102938863852984193 / 62500000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) := bmul sGlobal65_hz80 (sGlobal65_hz87 hc) (by norm_num) (by norm_num)

theorem sGlobal65_hz89 {c : ℝ} (hc : B (67 / 100) (27 / 40) c) : B (-3201096521157423783163 / 1000000000000000000) (-390102938863852984193 / 125000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) / (2 : ℝ)) := bdiv (sGlobal65_hz88 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal65_hz90 {c : ℝ} (hc : B (67 / 100) (27 / 40) c) : B (-3201096521157423783163 / 1000000000000000000) (-390102938863852984193 / 125000000000000000) (s3Cpp 12225 c) := by
    convert (sGlobal65_hz89 hc) using 1 <;>
      norm_num [s3Cpp, mA] <;> ring

theorem sGlobal65_hz91 {c : ℝ} (hc : B (67 / 100) (27 / 40) c) : B (336652083415701893041 / 50000000000000000) (6793310013503428330847 / 1000000000000000000) ((s3Cpa 12225 c) + (s3r1 12225 46)) := badd (sGlobal65_hz84 hc) sGlobal65_hz33 (by norm_num) (by norm_num)

theorem sGlobal65_hz92 {c : ℝ} (hc : B (67 / 100) (27 / 40) c) : B (12192675638712688191 / 200000000000000000) (61509069443057973777 / 1000000000000000000) (((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) := bdiv (sGlobal65_hz91 hc) sGlobal65_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal65_hz93 {c : ℝ} (hc : B (67 / 100) (27 / 40) c) : B (61086061219057501367 / 1000000000000000000) (308158762342760171 / 5000000000000000) ((((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) + (s3e0 12225 46)) := badd (sGlobal65_hz92 hc) sGlobal65_hz16 (by norm_num) (by norm_num)

theorem sGlobal65_hz94 {c : ℝ} (hc : B (67 / 100) (27 / 40) c) : B (61086061219057501367 / 1000000000000000000) (308158762342760171 / 5000000000000000) (s3Lam 12225 46 c) := by
    convert (sGlobal65_hz93 hc) using 1 <;>
      norm_num [s3Lam] <;> ring

theorem sGlobal65_hz95 {c : ℝ} (hc : B (67 / 100) (27 / 40) c) : B (-3124333114534931977563 / 1000000000000000000) (-1522030052144165799363 / 500000000000000000) ((s3Cpp 12225 c) + (s3rpp 12225 46)) := badd (sGlobal65_hz90 hc) sGlobal65_hz37 (by norm_num) (by norm_num)

theorem sGlobal65_hz96 {c : ℝ} (hc : B (67 / 100) (27 / 40) c) : B (-596572205387755866559 / 250000000000000000) (-1522030052144165799363 / 1000000000000000000) (if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) := bweaken (bfirst (sGlobal65_hz95 hc) (sGlobal65_hz76 hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem sGlobal65_hz97 {c : ℝ} (hc : B (67 / 100) (27 / 40) c) : B (373150687525844083001 / 100000000000000000) (3798472912344869761361 / 1000000000000000000) ((s3Lam 12225 46 c)^2) := bsq (sGlobal65_hz94 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal65_hz98 {c : ℝ} (hc : B (67 / 100) (27 / 40) c) : B (268912475982418247 / 500000000000000000) (27161136426946093 / 50000000000000000) ((s3c1 12225 46 c)^2) := bsq (sGlobal65_hz72 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal65_hz99 {c : ℝ} (hc : B (67 / 100) (27 / 40) c) : B (22838863573053907 / 50000000000000000) (231087524017581753 / 500000000000000000) ((1 : ℝ) - ((s3c1 12225 46 c)^2)) := bsub (bpoint (1 : ℝ)) (sGlobal65_hz98 hc) (by norm_num) (by norm_num)

theorem sGlobal65_hz100 {c : ℝ} (hc : B (67 / 100) (27 / 40) c) : B (135170599090346291 / 200000000000000000) (679834574021624401 / 1000000000000000000) (√((1 : ℝ) - ((s3c1 12225 46 c)^2))) := bsqrt (sGlobal65_hz99 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal65_hz101 {c : ℝ} (hc : B (67 / 100) (27 / 40) c) : B (1061627402708907741 / 500000000000000000) (2135763303402681717 / 1000000000000000000) (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))) := bmul pi_mem (sGlobal65_hz100 hc) (by norm_num) (by norm_num)

theorem sGlobal65_hz102 {c : ℝ} (hc : B (67 / 100) (27 / 40) c) : B (436788438741483278039 / 250000000000000000) (894492950787742066267 / 500000000000000000) (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2))))) := bdiv (sGlobal65_hz97 hc) (sGlobal65_hz101 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal65_hz103 {c : ℝ} (hc : B (67 / 100) (27 / 40) c) : B (-3994594166156814713 / 6250000000000000) (266955849431318333171 / 1000000000000000000) ((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) := badd (sGlobal65_hz96 hc) (sGlobal65_hz102 hc) (by norm_num) (by norm_num)

theorem sGlobal65_hz104 : B (3762781186094069 / 250000000000000000) (376278118609407 / 25000000000000000) ((s3e0 12225 46)^2) := bsq sGlobal65_hz16 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal65_hz105 {c : ℝ} (hc : B (67 / 100) (27 / 40) c) : B (-159780003865086494451 / 250000000000000000) (266970900556062709451 / 1000000000000000000) (((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) := badd (sGlobal65_hz103 hc) sGlobal65_hz104 (by norm_num) (by norm_num)

theorem sGlobal65_hz106 {c : ℝ} (hc : B (67 / 100) (27 / 40) c) : B (-600622942009098707673 / 1000000000000000000) (305467974010186979467 / 1000000000000000000) ((((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) + (s3rs 12225 46 maskSlack)) := badd (sGlobal65_hz105 hc) sGlobal65_hz29 (by norm_num) (by norm_num)

theorem sGlobal65_hz107 {c : ℝ} (hc : B (67 / 100) (27 / 40) c) : B (-600622942009098707673 / 1000000000000000000) (305467974010186979467 / 1000000000000000000) (s3U 12225 46 maskSlack c) := by
    convert (sGlobal65_hz106 hc) using 1 <;>
      norm_num [s3U] <;> ring

theorem sGlobal65_hz108 {c : ℝ} (hc : B (67 / 100) (27 / 40) c) : B (-3277859927779916057981 / 1000000000000000000) (-399698364691664459893 / 125000000000000000) ((s3Cpp 12225 c) - (s3rpp 12225 46)) := bsub (sGlobal65_hz90 hc) sGlobal65_hz37 (by norm_num) (by norm_num)

theorem sGlobal65_hz109 {c : ℝ} (hc : B (67 / 100) (27 / 40) c) : B (-3277859927779916057981 / 1000000000000000000) (-399698364691664459893 / 125000000000000000) (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ)) := bweaken (bmin (sGlobal65_hz108 hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem sGlobal65_hz110 {c : ℝ} (hc : B (67 / 100) (27 / 40) c) : B (-1251774413535219223703 / 500000000000000000) (-9746904520991820949 / 4000000000000000) ((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) := bmul (sGlobal65_hz76 hc) (sGlobal65_hz109 hc) (by norm_num) (by norm_num)

theorem sGlobal65_hz111 {c : ℝ} (hc : B (67 / 100) (27 / 40) c) : B (-1251781939097591411843 / 500000000000000000) (-1218370590686349806763 / 500000000000000000) (((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) := bsub (sGlobal65_hz110 hc) sGlobal65_hz104 (by norm_num) (by norm_num)

theorem sGlobal65_hz112 {c : ℝ} (hc : B (67 / 100) (27 / 40) c) : B (-1271030475824653546851 / 500000000000000000) (-2475238254823946883657 / 1000000000000000000) ((((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) - (s3rs 12225 46 maskSlack)) := bsub (sGlobal65_hz111 hc) sGlobal65_hz29 (by norm_num) (by norm_num)

theorem sGlobal65_hz113 {c : ℝ} (hc : B (67 / 100) (27 / 40) c) : B (-1271030475824653546851 / 500000000000000000) (-2475238254823946883657 / 1000000000000000000) (s3L 12225 46 maskSlack c) := by
    convert (sGlobal65_hz112 hc) using 1 <;>
      norm_num [s3L] <;> ring

theorem sGlobal65_hz114 {c : ℝ} (hc : B (67 / 100) (27 / 40) c) : B 0 (600622942009098707673 / 1000000000000000000) |(s3U 12225 46 maskSlack c)| := bweaken (babs (sGlobal65_hz107 hc)) (by norm_num) (by norm_num)

theorem sGlobal65_hz115 {c : ℝ} (hc : B (67 / 100) (27 / 40) c) : B 0 (1271030475824653546851 / 500000000000000000) |(s3L 12225 46 maskSlack c)| := bweaken (babs (sGlobal65_hz113 hc)) (by norm_num) (by norm_num)

theorem sGlobal65_hz116 {c : ℝ} (hc : B (67 / 100) (27 / 40) c) : B 0 (1271030475824653546851 / 500000000000000000) (max |(s3U 12225 46 maskSlack c)| |(s3L 12225 46 maskSlack c)|) := bweaken (bmax (sGlobal65_hz114 hc) (sGlobal65_hz115 hc)) (by norm_num) (by norm_num)

theorem sGlobal65_hz117 {c : ℝ} (hc : B (67 / 100) (27 / 40) c) : B 0 (1271030475824653546851 / 500000000000000000) (s3nks 12225 46 maskSlack c) := by
    convert (sGlobal65_hz116 hc) using 1 <;>
      norm_num [s3nks] <;> ring

theorem sGlobal65 {c : ℝ} (hc : B (67 / 100) (27 / 40) c) :
    0 < s3am 12225 46 ∧ 0 ≤ s3dm 12225 46 c ∧
    s3dm 12225 46 c ^ 2 ≤ 2 * s3ap 12225 46 ^ 2 ∧ s3c1 12225 46 c < 1 ∧
    0 ≤ s3Cpa 12225 c - s3r1 12225 46 ∧
    s3e0 12225 46 ≤ (s3Cpa 12225 c - s3r1 12225 46) / s3ap 12225 46 ∧
    s3nks 12225 46 maskSlack c ≤ 12225 * (10397 / 50000) := by

  refine ⟨lt_of_lt_of_le (by norm_num) sGlobal65_hz14.1,
    le_trans (by norm_num) (sGlobal65_hz64 hc).1, ?_,
    lt_of_le_of_lt (sGlobal65_hz72 hc).2 (by norm_num), ?_, ?_,
    le_trans (sGlobal65_hz117 hc).2 (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (sGlobal65_hz64 hc).1) (sGlobal65_hz64 hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) sGlobal65_hz9.1 2
    nlinarith only [h1, h2]
  · linarith only [(sGlobal65_hz84 hc).1, sGlobal65_hz33.2]
  · have hap : 0 < s3ap 12225 46 := lt_of_lt_of_le (by norm_num) sGlobal65_hz9.1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul sGlobal65_hz16.2 sGlobal65_hz9.2 (le_trans (by norm_num) sGlobal65_hz9.1) (by norm_num)
    linarith only [h, (sGlobal65_hz84 hc).1, sGlobal65_hz33.2]

end BstLean.Part255
