import BstLean.Part255SGlobal55
import BstLean.Part255Numeric10
namespace BstLean.Part255
open Real BstLean.Part130 BstLean.Part182 BstLean.Part197 BstLean.Part246
theorem sGlobal59_hz0 : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal59_hz1 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) ((√(23 : ℝ)) / (12225 : ℝ)) := bdiv sGlobal59_hz0 (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal59_hz2 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) maskSlack := by
    convert sGlobal59_hz1 using 1 <;>
      norm_num [maskSlack] <;> ring

theorem sGlobal59_hz3 : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal59_hz4 : B (6395294793910793 / 500000000000000000) (12790589587821587 / 1000000000000000000) (√((2 / 12225) : ℝ)) := bsqrt (bpoint ((2 / 12225) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal59_hz5 : B (7230130686979 / 62500000000000000) (23136418198333 / 200000000000000000) (√((2 / 149450625) : ℝ)) := bsqrt (bpoint ((2 / 149450625) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal59_hz6 : B (2211334438749598093 / 20000000000000000) (110566721937479904651 / 1000000000000000000) (√(12225 : ℝ)) := bsqrt (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal59_hz7 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))) := bmul sGlobal59_hz3 sGlobal59_hz4 (by norm_num) (by norm_num)

theorem sGlobal59_hz8 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) ((√(12225 : ℝ)) + ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := badd sGlobal59_hz6 sGlobal59_hz7 (by norm_num) (by norm_num)

theorem sGlobal59_hz9 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) (s3ap 12225 46) := by
    convert sGlobal59_hz8 using 1 <;>
      norm_num [s3ap, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal59_hz10 : B (163599182004089 / 1000000000000000000) (16359918200409 / 100000000000000000) ((2 : ℝ) / (12225 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal59_hz11 : B (1222499983640081799591 / 100000000000000000) (12224999836400817995911 / 1000000000000000000) ((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ))) := bsub (bpoint (12225 : ℝ)) sGlobal59_hz10 (by norm_num) (by norm_num)

theorem sGlobal59_hz12 : B (110566721197658827907 / 1000000000000000000) (27641680299414706977 / 250000000000000000) (√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) := bsqrt sGlobal59_hz11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal59_hz13 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) ((√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) - ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bsub sGlobal59_hz12 sGlobal59_hz7 (by norm_num) (by norm_num)

theorem sGlobal59_hz14 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) (s3am 12225 46) := by
    convert sGlobal59_hz13 using 1 <;>
      norm_num [s3am, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal59_hz15 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√((2 / 12225) : ℝ)) * (√(92 : ℝ))) := bmul sGlobal59_hz4 sGlobal59_hz3 (by norm_num) (by norm_num)

theorem sGlobal59_hz16 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) (s3e0 12225 46) := by
    convert sGlobal59_hz15 using 1 <;>
      norm_num [s3e0, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal59_hz17 : B (250196148528560847 / 500000000000000000) (100078459411424339 / 200000000000000000) (((1 / 2) : ℝ) + maskSlack) := badd (bpoint ((1 / 2) : ℝ)) sGlobal59_hz2 (by norm_num) (by norm_num)

theorem sGlobal59_hz18 : B (59827153232297998295487 / 800000000000000) (23930861292919199366019 / 320000000000000) ((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack)) := bmul (bpoint (149450625 : ℝ)) sGlobal59_hz17 (by norm_num) (by norm_num)

theorem sGlobal59_hz19 : B (1729554180017180009583 / 200000000000000000) (8647770900085900056557 / 1000000000000000000) (√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) := bsqrt sGlobal59_hz18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal59_hz20 : B (4328681281566262743499 / 500000000000000000) (8657362563132525495641 / 1000000000000000000) ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))) := badd sGlobal59_hz19 sGlobal59_hz3 (by norm_num) (by norm_num)

theorem sGlobal59_hz21 : B (110732771457999278473 / 1000000000000000000) (55366385728999643621 / 500000000000000000) ((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ)))) := bmul sGlobal59_hz4 sGlobal59_hz20 (by norm_num) (by norm_num)

theorem sGlobal59_hz22 : B (209099159 / 15625000000000000) (13382346177 / 1000000000000000000) ((2 : ℝ) / (149450625 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (149450625 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal59_hz23 : B (2452349334953899930479 / 200000000000000000) (12261746674769501594427 / 1000000000000000000) (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2) := bsq sGlobal59_hz21 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal59_hz24 : B (82045469362091 / 500000000000000000) (32818187747289 / 200000000000000000) (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2)) := bmul sGlobal59_hz22 sGlobal59_hz23 (by norm_num) (by norm_num)

theorem sGlobal59_hz25 : B (82045469362091 / 250000000000000000) (32818187747289 / 100000000000000000) ((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) := bmul (bpoint (2 : ℝ)) sGlobal59_hz24 (by norm_num) (by norm_num)

theorem sGlobal59_hz26 : B (117258080744995992792057 / 1000000000000000000) (58629040372497996396029 / 500000000000000000) (√(13749457500 : ℝ)) := bsqrt (bpoint (13749457500 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal59_hz27 : B (117304080744995992792057 / 1000000000000000000) (58652040372497996396029 / 500000000000000000) ((√(13749457500 : ℝ)) + (46 : ℝ)) := badd sGlobal59_hz26 (bpoint (46 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal59_hz28 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal59_hz25 sGlobal59_hz27 (by norm_num) (by norm_num)

theorem sGlobal59_hz29 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (s3rs 12225 46 maskSlack) := by
    convert sGlobal59_hz28 using 1 <;>
      norm_num [s3rs, s3pp, s3K, mA, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal59_hz30 : B (490797546012267 / 1000000000000000000) (49079754601227 / 100000000000000000) ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (3 : ℝ)) sGlobal59_hz10 (by norm_num) (by norm_num)

theorem sGlobal59_hz31 : B (490797546012267 / 500000000000000000) (49079754601227 / 50000000000000000) ((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal59_hz30 (by norm_num) (by norm_num)

theorem sGlobal59_hz32 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal59_hz31 sGlobal59_hz27 (by norm_num) (by norm_num)

theorem sGlobal59_hz33 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (s3r1 12225 46) := by
    convert sGlobal59_hz32 using 1 <;>
      norm_num [s3r1, mA] <;> ring

theorem sGlobal59_hz34 : B (163599182004089 / 500000000000000000) (16359918200409 / 50000000000000000) ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (2 : ℝ)) sGlobal59_hz10 (by norm_num) (by norm_num)

theorem sGlobal59_hz35 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal59_hz34 (by norm_num) (by norm_num)

theorem sGlobal59_hz36 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal59_hz35 sGlobal59_hz27 (by norm_num) (by norm_num)

theorem sGlobal59_hz37 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (s3rpp 12225 46) := by
    convert sGlobal59_hz36 using 1 <;>
      norm_num [s3rpp, mA] <;> ring

theorem sGlobal59_hz38 {c : ℝ} (hc : B (16 / 25) (129 / 200) c) : B (16 / 25) (129 / 200) c := hc

theorem sGlobal59_hz39 : B (5633325499112727 / 7812500000000000) (721065663886429061 / 1000000000000000000) (kdot ((16 / 25))) := by
    constructor
    · apply bkdot_lower (q := (468521285665818197 / 1000000000000000000)) (a := (438149030584170317 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (117130321416454549 / 250000000000000000)) (a := (54768628823021289 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal59_hz40 : B (256 / 625) (256 / 625) (((16 / 25) : ℝ)^2) := bsq (bpoint ((16 / 25) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal59_hz41 : B (369 / 625) (369 / 625) ((1 : ℝ) - (((16 / 25) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal59_hz40 (by norm_num) (by norm_num)

theorem sGlobal59_hz42 : B (384187454245970921 / 500000000000000000) (768374908491941843 / 1000000000000000000) (√((1 : ℝ) - (((16 / 25) : ℝ)^2))) := bsqrt sGlobal59_hz41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal59_hz43 : B (12229066483427529 / 50000000000000000) (244581329668550581 / 1000000000000000000) ((√((1 : ℝ) - (((16 / 25) : ℝ)^2))) / Real.pi) := bdiv sGlobal59_hz42 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal59_hz44 : B (92296404977462919 / 200000000000000000) (2307410124436573 / 5000000000000000) (((16 / 25) : ℝ) * (kdot ((16 / 25)))) := bmul (bpoint ((16 / 25) : ℝ)) sGlobal59_hz39 (by norm_num) (by norm_num)

theorem sGlobal59_hz45 : B (28242534182234607 / 40000000000000000) (706063354555865181 / 1000000000000000000) (((√((1 : ℝ) - (((16 / 25) : ℝ)^2))) / Real.pi) + (((16 / 25) : ℝ) * (kdot ((16 / 25))))) := badd sGlobal59_hz43 sGlobal59_hz44 (by norm_num) (by norm_num)

theorem sGlobal59_hz46 : B (28242534182234607 / 40000000000000000) (706063354555865181 / 1000000000000000000) (kappa ((16 / 25))) := by rw [kappa_eq]; exact sGlobal59_hz45

theorem sGlobal59_hz47 : B (72314264149627533 / 100000000000000000) (723142641496275333 / 1000000000000000000) (kdot ((129 / 200))) := by
    constructor
    · apply bkdot_lower (q := (92909734931194387 / 200000000000000000)) (a := (434886521783788547 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (232274337327985967 / 500000000000000000)) (a := (434886521783788543 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal59_hz48 : B (16641 / 40000) (16641 / 40000) (((129 / 200) : ℝ)^2) := bsq (bpoint ((129 / 200) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal59_hz49 : B (23359 / 40000) (23359 / 40000) ((1 : ℝ) - (((129 / 200) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal59_hz48 (by norm_num) (by norm_num)

theorem sGlobal59_hz50 : B (764182569809073831 / 1000000000000000000) (95522821226134229 / 125000000000000000) (√((1 : ℝ) - (((129 / 200) : ℝ)^2))) := bsqrt sGlobal59_hz49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal59_hz51 : B (3040585835244537 / 12500000000000000) (243246866819562961 / 1000000000000000000) ((√((1 : ℝ) - (((129 / 200) : ℝ)^2))) / Real.pi) := bdiv sGlobal59_hz50 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal59_hz52 : B (466427003765097587 / 1000000000000000000) (46642700376509759 / 100000000000000000) (((129 / 200) : ℝ) * (kdot ((129 / 200)))) := bmul (bpoint ((129 / 200) : ℝ)) sGlobal59_hz47 (by norm_num) (by norm_num)

theorem sGlobal59_hz53 : B (709673870584660547 / 1000000000000000000) (709673870584660551 / 1000000000000000000) (((√((1 : ℝ) - (((129 / 200) : ℝ)^2))) / Real.pi) + (((129 / 200) : ℝ) * (kdot ((129 / 200))))) := badd sGlobal59_hz51 sGlobal59_hz52 (by norm_num) (by norm_num)

theorem sGlobal59_hz54 : B (709673870584660547 / 1000000000000000000) (709673870584660551 / 1000000000000000000) (kappa ((129 / 200))) := by rw [kappa_eq]; exact sGlobal59_hz53

theorem sGlobal59_hz55 {c : ℝ} (hc : B (16 / 25) (129 / 200) c) : B (28242534182234607 / 40000000000000000) (709673870584660551 / 1000000000000000000) (kappa c) := bkappa (sGlobal59_hz38 hc) (by norm_num) (by norm_num) sGlobal59_hz46.1 sGlobal59_hz54.2

theorem sGlobal59_hz56 : B 24450 24450 ((2 : ℝ) * (12225 : ℝ)) := bmul (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal59_hz57 {c : ℝ} (hc : B (16 / 25) (129 / 200) c) : B (290326129415339449 / 1000000000000000000) (11757465817765393 / 40000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (sGlobal59_hz55 hc) (by norm_num) (by norm_num)

theorem sGlobal59_hz58 {c : ℝ} (hc : B (16 / 25) (129 / 200) c) : B (141969477284100990561 / 20000000000000000) (5749400784887277177 / 800000000000000) (((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) := bmul sGlobal59_hz56 (sGlobal59_hz57 hc) (by norm_num) (by norm_num)

theorem sGlobal59_hz59 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (4 : ℝ)) sGlobal59_hz10 (by norm_num) (by norm_num)

theorem sGlobal59_hz60 {c : ℝ} (hc : B (16 / 25) (129 / 200) c) : B (709847320980832151169 / 100000000000000000) (3593375163356184227447 / 500000000000000000) ((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bsub (sGlobal59_hz58 hc) sGlobal59_hz59 (by norm_num) (by norm_num)

theorem sGlobal59_hz61 {c : ℝ} (hc : B (16 / 25) (129 / 200) c) : B (42126218705837821469 / 500000000000000000) (84774703341930772309 / 1000000000000000000) (√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) := bsqrt (sGlobal59_hz60 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal59_hz62 : B (30670756373515103 / 125000000000000000) (122683025494060423 / 500000000000000000) ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal59_hz7 (by norm_num) (by norm_num)

theorem sGlobal59_hz63 {c : ℝ} (hc : B (16 / 25) (129 / 200) c) : B (21001767840171880523 / 250000000000000000) (16905867458188530297 / 200000000000000000) ((√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) - ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))))) := bsub (sGlobal59_hz61 hc) sGlobal59_hz62 (by norm_num) (by norm_num)

theorem sGlobal59_hz64 {c : ℝ} (hc : B (16 / 25) (129 / 200) c) : B (21001767840171880523 / 250000000000000000) (16905867458188530297 / 200000000000000000) (s3dm 12225 46 c) := by
    convert (sGlobal59_hz63 hc) using 1 <;>
      norm_num [s3dm, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal59_hz65 : B (6126072185528622723889 / 500000000000000000) (2450428874211449090087 / 200000000000000000) ((s3ap 12225 46)^2) := bsq sGlobal59_hz9 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal59_hz66 : B (6126072185528622723889 / 250000000000000000) (2450428874211449090087 / 100000000000000000) ((2 : ℝ) * ((s3ap 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal59_hz65 (by norm_num) (by norm_num)

theorem sGlobal59_hz67 {c : ℝ} (hc : B (16 / 25) (129 / 200) c) : B (882148504824955710561 / 125000000000000000) (3572604431422973977373 / 500000000000000000) ((s3dm 12225 46 c)^2) := bsq (sGlobal59_hz64 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal59_hz68 {c : ℝ} (hc : B (16 / 25) (129 / 200) c) : B (1735907987926854294081 / 100000000000000000) (8723550351757422608191 / 500000000000000000) (((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) := bsub sGlobal59_hz66 (sGlobal59_hz67 hc) (by norm_num) (by norm_num)

theorem sGlobal59_hz69 : B (1524735695971823534271 / 125000000000000000) (609894278388729413841 / 50000000000000000) ((s3am 12225 46)^2) := bsq sGlobal59_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal59_hz70 : B (1524735695971823534271 / 62500000000000000) (609894278388729413841 / 25000000000000000) ((2 : ℝ) * ((s3am 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal59_hz69 (by norm_num) (by norm_num)

theorem sGlobal59_hz71 {c : ℝ} (hc : B (16 / 25) (129 / 200) c) : B (142312204708078561 / 200000000000000000) (71516905969375873 / 100000000000000000) ((((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) / ((2 : ℝ) * ((s3am 12225 46)^2))) := bdiv (sGlobal59_hz68 hc) sGlobal59_hz70 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal59_hz72 {c : ℝ} (hc : B (16 / 25) (129 / 200) c) : B (142312204708078561 / 200000000000000000) (71516905969375873 / 100000000000000000) (s3c1 12225 46 c) := by
    convert (sGlobal59_hz71 hc) using 1 <;>
      norm_num [s3c1] <;> ring

theorem sGlobal59_hz73 {c : ℝ} (hc : B (16 / 25) (129 / 200) c) : B (5633325499112727 / 7812500000000000) (723142641496275333 / 1000000000000000000) (kdot c) := bkdot (sGlobal59_hz38 hc) sGlobal59_hz39.1 sGlobal59_hz47.2

theorem sGlobal59_hz74 : B (752011482438597157 / 1000000000000000000) (752011482438597159 / 1000000000000000000) (kdot ((142312204708078561 / 200000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (410516652546119637 / 1000000000000000000)) (a := (389539452472763299 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (102629163136529909 / 250000000000000000)) (a := (389539452472763297 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal59_hz75 : B (376825155359415261 / 500000000000000000) (30146012428753221 / 40000000000000000) (kdot ((71516905969375873 / 100000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (407511730694627759 / 1000000000000000000)) (a := (386965187029925131 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (203755865347313879 / 500000000000000000)) (a := (386965187029925129 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal59_hz76 {c : ℝ} (hc : B (16 / 25) (129 / 200) c) : B (752011482438597157 / 1000000000000000000) (30146012428753221 / 40000000000000000) (kdot (s3c1 12225 46 c)) := bkdot (sGlobal59_hz72 hc) sGlobal59_hz74.1 sGlobal59_hz75.2

theorem sGlobal59_hz77 {c : ℝ} (hc : B (16 / 25) (129 / 200) c) : B (256 / 625) (16641 / 40000) (c^2) := bsq (sGlobal59_hz38 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal59_hz78 {c : ℝ} (hc : B (16 / 25) (129 / 200) c) : B (23359 / 40000) (369 / 625) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (sGlobal59_hz77 hc) (by norm_num) (by norm_num)

theorem sGlobal59_hz79 {c : ℝ} (hc : B (16 / 25) (129 / 200) c) : B (764182569809073831 / 1000000000000000000) (768374908491941843 / 1000000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (sGlobal59_hz78 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal59_hz80 : B (39119999999999765769 / 1600000000000000) (3912000000000000489 / 160000000000000) ((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (149450625 : ℝ)) sGlobal59_hz10 (by norm_num) (by norm_num)

theorem sGlobal59_hz81 {c : ℝ} (hc : B (16 / 25) (129 / 200) c) : B (551025812029817239 / 1000000000000000000) (277822330493160833 / 500000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (sGlobal59_hz79 hc) (sGlobal59_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal59_hz82 {c : ℝ} (hc : B (16 / 25) (129 / 200) c) : B (1347258110412895082647 / 100000000000000000) (13585511961115566431889 / 1000000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) := bmul sGlobal59_hz80 (sGlobal59_hz81 hc) (by norm_num) (by norm_num)

theorem sGlobal59_hz83 {c : ℝ} (hc : B (16 / 25) (129 / 200) c) : B (1347258110412895082647 / 200000000000000000) (1358551196111556643189 / 200000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) / (2 : ℝ)) := bdiv (sGlobal59_hz82 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal59_hz84 {c : ℝ} (hc : B (16 / 25) (129 / 200) c) : B (1347258110412895082647 / 200000000000000000) (1358551196111556643189 / 200000000000000000) (s3Cpa 12225 c) := by
    convert (sGlobal59_hz83 hc) using 1 <;>
      norm_num [s3Cpa, mA] <;> ring

theorem sGlobal59_hz85 {c : ℝ} (hc : B (16 / 25) (129 / 200) c) : B (3040585835244537 / 12500000000000000) (244581329668550581 / 1000000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (sGlobal59_hz79 hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal59_hz86 {c : ℝ} (hc : B (16 / 25) (129 / 200) c) : B (92296404977462919 / 200000000000000000) (46642700376509759 / 100000000000000000) (c * (kdot c)) := bmul (sGlobal59_hz38 hc) (sGlobal59_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal59_hz87 {c : ℝ} (hc : B (16 / 25) (129 / 200) c) : B (-22318013694553463 / 100000000000000000) (-108450347609382007 / 500000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (sGlobal59_hz85 hc) (sGlobal59_hz86 hc) (by norm_num) (by norm_num)

theorem sGlobal59_hz88 {c : ℝ} (hc : B (16 / 25) (129 / 200) c) : B (-1091350869663664477119 / 200000000000000000) (-2651610999049374194629 / 500000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) := bmul sGlobal59_hz80 (sGlobal59_hz87 hc) (by norm_num) (by norm_num)

theorem sGlobal59_hz89 {c : ℝ} (hc : B (16 / 25) (129 / 200) c) : B (-1364188587079580596399 / 500000000000000000) (-2651610999049374194629 / 1000000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) / (2 : ℝ)) := bdiv (sGlobal59_hz88 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal59_hz90 {c : ℝ} (hc : B (16 / 25) (129 / 200) c) : B (-1364188587079580596399 / 500000000000000000) (-2651610999049374194629 / 1000000000000000000) (s3Cpp 12225 c) := by
    convert (sGlobal59_hz89 hc) using 1 <;>
      norm_num [s3Cpp, mA] <;> ring

theorem sGlobal59_hz91 {c : ℝ} (hc : B (16 / 25) (129 / 200) c) : B (1712858915499553280409 / 250000000000000000) (6907901090491521628171 / 1000000000000000000) ((s3Cpa 12225 c) + (s3r1 12225 46)) := badd (sGlobal59_hz84 hc) sGlobal59_hz33 (by norm_num) (by norm_num)

theorem sGlobal59_hz92 {c : ℝ} (hc : B (16 / 25) (129 / 200) c) : B (31017679973444604587 / 500000000000000000) (6254661822237247107 / 100000000000000000) (((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) := bdiv (sGlobal59_hz91 hc) sGlobal59_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal59_hz93 {c : ℝ} (hc : B (16 / 25) (129 / 200) c) : B (31079021486191634793 / 500000000000000000) (62669301247866531493 / 1000000000000000000) ((((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) + (s3e0 12225 46)) := badd (sGlobal59_hz92 hc) sGlobal59_hz16 (by norm_num) (by norm_num)

theorem sGlobal59_hz94 {c : ℝ} (hc : B (16 / 25) (129 / 200) c) : B (31079021486191634793 / 500000000000000000) (62669301247866531493 / 1000000000000000000) (s3Lam 12225 46 c) := by
    convert (sGlobal59_hz93 hc) using 1 <;>
      norm_num [s3Lam] <;> ring

theorem sGlobal59_hz95 {c : ℝ} (hc : B (16 / 25) (129 / 200) c) : B (-1325806883768334693599 / 500000000000000000) (-2574847592426881919811 / 1000000000000000000) ((s3Cpp 12225 c) + (s3rpp 12225 46)) := badd (sGlobal59_hz90 hc) sGlobal59_hz37 (by norm_num) (by norm_num)

theorem sGlobal59_hz96 {c : ℝ} (hc : B (16 / 25) (129 / 200) c) : B (-399677907962067947329 / 200000000000000000) (-257484759242688191981 / 200000000000000000) (if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) := bweaken (bfirst (sGlobal59_hz95 hc) (sGlobal59_hz76 hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem sGlobal59_hz97 {c : ℝ} (hc : B (16 / 25) (129 / 200) c) : B (3863622306156645167577 / 1000000000000000000) (49093016486198070017 / 12500000000000000) ((s3Lam 12225 46 c)^2) := bsq (sGlobal59_hz94 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal59_hz98 {c : ℝ} (hc : B (16 / 25) (129 / 200) c) : B (506319090221851443 / 1000000000000000000) (255733391971627519 / 500000000000000000) ((s3c1 12225 46 c)^2) := bsq (sGlobal59_hz72 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal59_hz99 {c : ℝ} (hc : B (16 / 25) (129 / 200) c) : B (244266608028372481 / 500000000000000000) (493680909778148557 / 1000000000000000000) ((1 : ℝ) - ((s3c1 12225 46 c)^2)) := bsub (bpoint (1 : ℝ)) (sGlobal59_hz98 hc) (by norm_num) (by norm_num)

theorem sGlobal59_hz100 {c : ℝ} (hc : B (16 / 25) (129 / 200) c) : B (21842234748427529 / 31250000000000000) (351312151006106163 / 500000000000000000) (√((1 : ℝ) - ((s3c1 12225 46 c)^2))) := bsqrt (sGlobal59_hz99 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal59_hz101 {c : ℝ} (hc : B (16 / 25) (129 / 200) c) : B (274477616894574523 / 125000000000000000) (2207359345435222423 / 1000000000000000000) (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))) := bmul pi_mem (sGlobal59_hz100 hc) (by norm_num) (by norm_num)

theorem sGlobal59_hz102 {c : ℝ} (hc : B (16 / 25) (129 / 200) c) : B (875168402948650696891 / 500000000000000000) (1788598175750500325897 / 1000000000000000000) (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2))))) := bdiv (sGlobal59_hz97 hc) (sGlobal59_hz101 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal59_hz103 {c : ℝ} (hc : B (16 / 25) (129 / 200) c) : B (-248052733913038342863 / 1000000000000000000) (62646797442132420749 / 125000000000000000) ((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) := badd (sGlobal59_hz96 hc) (sGlobal59_hz102 hc) (by norm_num) (by norm_num)

theorem sGlobal59_hz104 : B (3762781186094069 / 250000000000000000) (376278118609407 / 25000000000000000) ((s3e0 12225 46)^2) := bsq sGlobal59_hz16 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal59_hz105 {c : ℝ} (hc : B (16 / 25) (129 / 200) c) : B (-248037682788293966587 / 1000000000000000000) (7831084854090683473 / 15625000000000000) (((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) := badd (sGlobal59_hz103 hc) sGlobal59_hz104 (by norm_num) (by norm_num)

theorem sGlobal59_hz106 {c : ℝ} (hc : B (16 / 25) (129 / 200) c) : B (-26192576167130837057 / 125000000000000000) (1054075203351421899 / 1953125000000000) ((((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) + (s3rs 12225 46 maskSlack)) := badd (sGlobal59_hz105 hc) sGlobal59_hz29 (by norm_num) (by norm_num)

theorem sGlobal59_hz107 {c : ℝ} (hc : B (16 / 25) (129 / 200) c) : B (-26192576167130837057 / 125000000000000000) (1054075203351421899 / 1953125000000000) (s3U 12225 46 maskSlack c) := by
    convert (sGlobal59_hz106 hc) using 1 <;>
      norm_num [s3U] <;> ring

theorem sGlobal59_hz108 {c : ℝ} (hc : B (16 / 25) (129 / 200) c) : B (-87660643149426670863 / 31250000000000000) (-2728374405671866000229 / 1000000000000000000) ((s3Cpp 12225 c) - (s3rpp 12225 46)) := bsub (sGlobal59_hz90 hc) sGlobal59_hz37 (by norm_num) (by norm_num)

theorem sGlobal59_hz109 {c : ℝ} (hc : B (16 / 25) (129 / 200) c) : B (-87660643149426670863 / 31250000000000000) (-2728374405671866000229 / 1000000000000000000) (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ)) := bweaken (bmin (sGlobal59_hz108 hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem sGlobal59_hz110 {c : ℝ} (hc : B (16 / 25) (129 / 200) c) : B (-528523767579023463641 / 250000000000000000) (-128235555091051650881 / 62500000000000000) ((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) := bmul (sGlobal59_hz76 hc) (sGlobal59_hz109 hc) (by norm_num) (by norm_num)

theorem sGlobal59_hz111 {c : ℝ} (hc : B (16 / 25) (129 / 200) c) : B (-528527530360209557711 / 250000000000000000) (-512945983145392697593 / 250000000000000000) (((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) := bsub (sGlobal59_hz110 hc) sGlobal59_hz104 (by norm_num) (by norm_num)

theorem sGlobal59_hz112 {c : ℝ} (hc : B (16 / 25) (129 / 200) c) : B (-107630359744748125043 / 50000000000000000) (-2090281006032818060503 / 1000000000000000000) ((((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) - (s3rs 12225 46 maskSlack)) := bsub (sGlobal59_hz111 hc) sGlobal59_hz29 (by norm_num) (by norm_num)

theorem sGlobal59_hz113 {c : ℝ} (hc : B (16 / 25) (129 / 200) c) : B (-107630359744748125043 / 50000000000000000) (-2090281006032818060503 / 1000000000000000000) (s3L 12225 46 maskSlack c) := by
    convert (sGlobal59_hz112 hc) using 1 <;>
      norm_num [s3L] <;> ring

theorem sGlobal59_hz114 {c : ℝ} (hc : B (16 / 25) (129 / 200) c) : B 0 (1054075203351421899 / 1953125000000000) |(s3U 12225 46 maskSlack c)| := bweaken (babs (sGlobal59_hz107 hc)) (by norm_num) (by norm_num)

theorem sGlobal59_hz115 {c : ℝ} (hc : B (16 / 25) (129 / 200) c) : B 0 (107630359744748125043 / 50000000000000000) |(s3L 12225 46 maskSlack c)| := bweaken (babs (sGlobal59_hz113 hc)) (by norm_num) (by norm_num)

theorem sGlobal59_hz116 {c : ℝ} (hc : B (16 / 25) (129 / 200) c) : B 0 (107630359744748125043 / 50000000000000000) (max |(s3U 12225 46 maskSlack c)| |(s3L 12225 46 maskSlack c)|) := bweaken (bmax (sGlobal59_hz114 hc) (sGlobal59_hz115 hc)) (by norm_num) (by norm_num)

theorem sGlobal59_hz117 {c : ℝ} (hc : B (16 / 25) (129 / 200) c) : B 0 (107630359744748125043 / 50000000000000000) (s3nks 12225 46 maskSlack c) := by
    convert (sGlobal59_hz116 hc) using 1 <;>
      norm_num [s3nks] <;> ring

theorem sGlobal59 {c : ℝ} (hc : B (16 / 25) (129 / 200) c) :
    0 < s3am 12225 46 ∧ 0 ≤ s3dm 12225 46 c ∧
    s3dm 12225 46 c ^ 2 ≤ 2 * s3ap 12225 46 ^ 2 ∧ s3c1 12225 46 c < 1 ∧
    0 ≤ s3Cpa 12225 c - s3r1 12225 46 ∧
    s3e0 12225 46 ≤ (s3Cpa 12225 c - s3r1 12225 46) / s3ap 12225 46 ∧
    s3nks 12225 46 maskSlack c ≤ 12225 * (176083 / 1000000) := by

  refine ⟨lt_of_lt_of_le (by norm_num) sGlobal59_hz14.1,
    le_trans (by norm_num) (sGlobal59_hz64 hc).1, ?_,
    lt_of_le_of_lt (sGlobal59_hz72 hc).2 (by norm_num), ?_, ?_,
    le_trans (sGlobal59_hz117 hc).2 (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (sGlobal59_hz64 hc).1) (sGlobal59_hz64 hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) sGlobal59_hz9.1 2
    nlinarith only [h1, h2]
  · linarith only [(sGlobal59_hz84 hc).1, sGlobal59_hz33.2]
  · have hap : 0 < s3ap 12225 46 := lt_of_lt_of_le (by norm_num) sGlobal59_hz9.1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul sGlobal59_hz16.2 sGlobal59_hz9.2 (le_trans (by norm_num) sGlobal59_hz9.1) (by norm_num)
    linarith only [h, (sGlobal59_hz84 hc).1, sGlobal59_hz33.2]

end BstLean.Part255
