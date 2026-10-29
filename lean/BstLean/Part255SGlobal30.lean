import BstLean.Part255SGlobal26
import BstLean.Part255Numeric10
namespace BstLean.Part255
open Real BstLean.Part130 BstLean.Part182 BstLean.Part197 BstLean.Part246
theorem sGlobal30_hz0 : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal30_hz1 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) ((√(23 : ℝ)) / (12225 : ℝ)) := bdiv sGlobal30_hz0 (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal30_hz2 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) maskSlack := by
    convert sGlobal30_hz1 using 1 <;>
      norm_num [maskSlack] <;> ring

theorem sGlobal30_hz3 : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal30_hz4 : B (6395294793910793 / 500000000000000000) (12790589587821587 / 1000000000000000000) (√((2 / 12225) : ℝ)) := bsqrt (bpoint ((2 / 12225) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal30_hz5 : B (7230130686979 / 62500000000000000) (23136418198333 / 200000000000000000) (√((2 / 149450625) : ℝ)) := bsqrt (bpoint ((2 / 149450625) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal30_hz6 : B (2211334438749598093 / 20000000000000000) (110566721937479904651 / 1000000000000000000) (√(12225 : ℝ)) := bsqrt (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal30_hz7 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))) := bmul sGlobal30_hz3 sGlobal30_hz4 (by norm_num) (by norm_num)

theorem sGlobal30_hz8 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) ((√(12225 : ℝ)) + ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := badd sGlobal30_hz6 sGlobal30_hz7 (by norm_num) (by norm_num)

theorem sGlobal30_hz9 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) (s3ap 12225 46) := by
    convert sGlobal30_hz8 using 1 <;>
      norm_num [s3ap, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal30_hz10 : B (163599182004089 / 1000000000000000000) (16359918200409 / 100000000000000000) ((2 : ℝ) / (12225 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal30_hz11 : B (1222499983640081799591 / 100000000000000000) (12224999836400817995911 / 1000000000000000000) ((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ))) := bsub (bpoint (12225 : ℝ)) sGlobal30_hz10 (by norm_num) (by norm_num)

theorem sGlobal30_hz12 : B (110566721197658827907 / 1000000000000000000) (27641680299414706977 / 250000000000000000) (√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) := bsqrt sGlobal30_hz11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal30_hz13 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) ((√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) - ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bsub sGlobal30_hz12 sGlobal30_hz7 (by norm_num) (by norm_num)

theorem sGlobal30_hz14 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) (s3am 12225 46) := by
    convert sGlobal30_hz13 using 1 <;>
      norm_num [s3am, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal30_hz15 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√((2 / 12225) : ℝ)) * (√(92 : ℝ))) := bmul sGlobal30_hz4 sGlobal30_hz3 (by norm_num) (by norm_num)

theorem sGlobal30_hz16 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) (s3e0 12225 46) := by
    convert sGlobal30_hz15 using 1 <;>
      norm_num [s3e0, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal30_hz17 : B (250196148528560847 / 500000000000000000) (100078459411424339 / 200000000000000000) (((1 / 2) : ℝ) + maskSlack) := badd (bpoint ((1 / 2) : ℝ)) sGlobal30_hz2 (by norm_num) (by norm_num)

theorem sGlobal30_hz18 : B (59827153232297998295487 / 800000000000000) (23930861292919199366019 / 320000000000000) ((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack)) := bmul (bpoint (149450625 : ℝ)) sGlobal30_hz17 (by norm_num) (by norm_num)

theorem sGlobal30_hz19 : B (1729554180017180009583 / 200000000000000000) (8647770900085900056557 / 1000000000000000000) (√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) := bsqrt sGlobal30_hz18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal30_hz20 : B (4328681281566262743499 / 500000000000000000) (8657362563132525495641 / 1000000000000000000) ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))) := badd sGlobal30_hz19 sGlobal30_hz3 (by norm_num) (by norm_num)

theorem sGlobal30_hz21 : B (110732771457999278473 / 1000000000000000000) (55366385728999643621 / 500000000000000000) ((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ)))) := bmul sGlobal30_hz4 sGlobal30_hz20 (by norm_num) (by norm_num)

theorem sGlobal30_hz22 : B (209099159 / 15625000000000000) (13382346177 / 1000000000000000000) ((2 : ℝ) / (149450625 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (149450625 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal30_hz23 : B (2452349334953899930479 / 200000000000000000) (12261746674769501594427 / 1000000000000000000) (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2) := bsq sGlobal30_hz21 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal30_hz24 : B (82045469362091 / 500000000000000000) (32818187747289 / 200000000000000000) (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2)) := bmul sGlobal30_hz22 sGlobal30_hz23 (by norm_num) (by norm_num)

theorem sGlobal30_hz25 : B (82045469362091 / 250000000000000000) (32818187747289 / 100000000000000000) ((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) := bmul (bpoint (2 : ℝ)) sGlobal30_hz24 (by norm_num) (by norm_num)

theorem sGlobal30_hz26 : B (117258080744995992792057 / 1000000000000000000) (58629040372497996396029 / 500000000000000000) (√(13749457500 : ℝ)) := bsqrt (bpoint (13749457500 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal30_hz27 : B (117304080744995992792057 / 1000000000000000000) (58652040372497996396029 / 500000000000000000) ((√(13749457500 : ℝ)) + (46 : ℝ)) := badd sGlobal30_hz26 (bpoint (46 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal30_hz28 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal30_hz25 sGlobal30_hz27 (by norm_num) (by norm_num)

theorem sGlobal30_hz29 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (s3rs 12225 46 maskSlack) := by
    convert sGlobal30_hz28 using 1 <;>
      norm_num [s3rs, s3pp, s3K, mA, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal30_hz30 : B (490797546012267 / 1000000000000000000) (49079754601227 / 100000000000000000) ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (3 : ℝ)) sGlobal30_hz10 (by norm_num) (by norm_num)

theorem sGlobal30_hz31 : B (490797546012267 / 500000000000000000) (49079754601227 / 50000000000000000) ((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal30_hz30 (by norm_num) (by norm_num)

theorem sGlobal30_hz32 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal30_hz31 sGlobal30_hz27 (by norm_num) (by norm_num)

theorem sGlobal30_hz33 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (s3r1 12225 46) := by
    convert sGlobal30_hz32 using 1 <;>
      norm_num [s3r1, mA] <;> ring

theorem sGlobal30_hz34 : B (163599182004089 / 500000000000000000) (16359918200409 / 50000000000000000) ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (2 : ℝ)) sGlobal30_hz10 (by norm_num) (by norm_num)

theorem sGlobal30_hz35 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal30_hz34 (by norm_num) (by norm_num)

theorem sGlobal30_hz36 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal30_hz35 sGlobal30_hz27 (by norm_num) (by norm_num)

theorem sGlobal30_hz37 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (s3rpp 12225 46) := by
    convert sGlobal30_hz36 using 1 <;>
      norm_num [s3rpp, mA] <;> ring

theorem sGlobal30_hz38 {c : ℝ} (hc : B (99 / 200) (1 / 2) c) : B (99 / 200) (1 / 2) c := hc

theorem sGlobal30_hz39 : B (332415973159448007 / 500000000000000000) (83103993289871197 / 125000000000000000) (kdot ((99 / 200))) := by
    constructor
    · apply bkdot_lower (q := (290599656804885193 / 500000000000000000)) (a := (526480747581272869 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (116239862721954077 / 200000000000000000)) (a := (526480747581157319 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal30_hz40 : B (9801 / 40000) (9801 / 40000) (((99 / 200) : ℝ)^2) := bsq (bpoint ((99 / 200) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal30_hz41 : B (30199 / 40000) (30199 / 40000) ((1 : ℝ) - (((99 / 200) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal30_hz40 (by norm_num) (by norm_num)

theorem sGlobal30_hz42 : B (434446486923303363 / 500000000000000000) (868892973846606727 / 1000000000000000000) (√((1 : ℝ) - (((99 / 200) : ℝ)^2))) := bsqrt sGlobal30_hz41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal30_hz43 : B (276577223611008791 / 1000000000000000000) (34572152951376099 / 125000000000000000) ((√((1 : ℝ) - (((99 / 200) : ℝ)^2))) / Real.pi) := bdiv sGlobal30_hz42 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal30_hz44 : B (164545906713926763 / 500000000000000000) (329091813427889941 / 1000000000000000000) (((99 / 200) : ℝ) * (kdot ((99 / 200)))) := bmul (bpoint ((99 / 200) : ℝ)) sGlobal30_hz39 (by norm_num) (by norm_num)

theorem sGlobal30_hz45 : B (605669037038862317 / 1000000000000000000) (605669037038898733 / 1000000000000000000) (((√((1 : ℝ) - (((99 / 200) : ℝ)^2))) / Real.pi) + (((99 / 200) : ℝ) * (kdot ((99 / 200))))) := badd sGlobal30_hz43 sGlobal30_hz44 (by norm_num) (by norm_num)

theorem sGlobal30_hz46 : B (605669037038862317 / 1000000000000000000) (605669037038898733 / 1000000000000000000) (kappa ((99 / 200))) := by rw [kappa_eq]; exact sGlobal30_hz45

theorem sGlobal30_hz47 : B (26666666666666409 / 40000000000000000) (133333333333342669 / 200000000000000000) (kdot ((1 / 2))) := by
    constructor
    · apply bkdot_lower (q := (115470053837925153 / 200000000000000000)) (a := (523598775598308991 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (144337567297406441 / 250000000000000000)) (a := (523598775598225551 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal30_hz48 : B (1 / 4) (1 / 4) (((1 / 2) : ℝ)^2) := bsq (bpoint ((1 / 2) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal30_hz49 : B (3 / 4) (3 / 4) ((1 : ℝ) - (((1 / 2) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal30_hz48 (by norm_num) (by norm_num)

theorem sGlobal30_hz50 : B (433012701892219323 / 500000000000000000) (866025403784438647 / 1000000000000000000) (√((1 : ℝ) - (((1 / 2) : ℝ)^2))) := bsqrt sGlobal30_hz49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal30_hz51 : B (34458055963862003 / 125000000000000000) (11026577908435841 / 40000000000000000) ((√((1 : ℝ) - (((1 / 2) : ℝ)^2))) / Real.pi) := bdiv sGlobal30_hz50 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal30_hz52 : B (5208333333333283 / 15625000000000000) (333333333333356673 / 1000000000000000000) (((1 / 2) : ℝ) * (kdot ((1 / 2)))) := bmul (bpoint ((1 / 2) : ℝ)) sGlobal30_hz47 (by norm_num) (by norm_num)

theorem sGlobal30_hz53 : B (76124722630528267 / 125000000000000000) (304498890522126349 / 500000000000000000) (((√((1 : ℝ) - (((1 / 2) : ℝ)^2))) / Real.pi) + (((1 / 2) : ℝ) * (kdot ((1 / 2))))) := badd sGlobal30_hz51 sGlobal30_hz52 (by norm_num) (by norm_num)

theorem sGlobal30_hz54 : B (76124722630528267 / 125000000000000000) (304498890522126349 / 500000000000000000) (kappa ((1 / 2))) := by rw [kappa_eq]; exact sGlobal30_hz53

theorem sGlobal30_hz55 {c : ℝ} (hc : B (99 / 200) (1 / 2) c) : B (605669037038862317 / 1000000000000000000) (304498890522126349 / 500000000000000000) (kappa c) := bkappa (sGlobal30_hz38 hc) (by norm_num) (by norm_num) sGlobal30_hz46.1 sGlobal30_hz54.2

theorem sGlobal30_hz56 : B 24450 24450 ((2 : ℝ) * (12225 : ℝ)) := bmul (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal30_hz57 {c : ℝ} (hc : B (99 / 200) (1 / 2) c) : B (195501109477873651 / 500000000000000000) (394330962961137683 / 1000000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (sGlobal30_hz55 hc) (by norm_num) (by norm_num)

theorem sGlobal30_hz58 {c : ℝ} (hc : B (99 / 200) (1 / 2) c) : B (95600042534680215339 / 10000000000000000) (192827840887996326987 / 20000000000000000) (((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) := bmul sGlobal30_hz56 (sGlobal30_hz57 hc) (by norm_num) (by norm_num)

theorem sGlobal30_hz59 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (4 : ℝ)) sGlobal30_hz10 (by norm_num) (by norm_num)

theorem sGlobal30_hz60 {c : ℝ} (hc : B (99 / 200) (1 / 2) c) : B (478000179953564675877 / 50000000000000000) (4820695695001544166497 / 500000000000000000) ((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bsub (sGlobal30_hz58 hc) sGlobal30_hz59 (by norm_num) (by norm_num)

theorem sGlobal30_hz61 {c : ℝ} (hc : B (99 / 200) (1 / 2) c) : B (97775270897457980489 / 1000000000000000000) (98190587074337672141 / 1000000000000000000) (√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) := bsqrt (sGlobal30_hz60 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal30_hz62 : B (30670756373515103 / 125000000000000000) (122683025494060423 / 500000000000000000) ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal30_hz7 (by norm_num) (by norm_num)

theorem sGlobal30_hz63 {c : ℝ} (hc : B (99 / 200) (1 / 2) c) : B (97529904846469859643 / 1000000000000000000) (97945221023349551317 / 1000000000000000000) ((√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) - ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))))) := bsub (sGlobal30_hz61 hc) sGlobal30_hz62 (by norm_num) (by norm_num)

theorem sGlobal30_hz64 {c : ℝ} (hc : B (99 / 200) (1 / 2) c) : B (97529904846469859643 / 1000000000000000000) (97945221023349551317 / 1000000000000000000) (s3dm 12225 46 c) := by
    convert (sGlobal30_hz63 hc) using 1 <;>
      norm_num [s3dm, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal30_hz65 : B (6126072185528622723889 / 500000000000000000) (2450428874211449090087 / 200000000000000000) ((s3ap 12225 46)^2) := bsq sGlobal30_hz9 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal30_hz66 : B (6126072185528622723889 / 250000000000000000) (2450428874211449090087 / 100000000000000000) ((2 : ℝ) * ((s3ap 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal30_hz65 (by norm_num) (by norm_num)

theorem sGlobal30_hz67 {c : ℝ} (hc : B (99 / 200) (1 / 2) c) : B (9512082339361465016261 / 1000000000000000000) (1918653264262558985707 / 200000000000000000) ((s3dm 12225 46 c)^2) := bsq (sGlobal30_hz64 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal30_hz68 {c : ℝ} (hc : B (99 / 200) (1 / 2) c) : B (14911022420801695967021 / 1000000000000000000) (14992206402753025884609 / 1000000000000000000) (((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) := bsub sGlobal30_hz66 (sGlobal30_hz67 hc) (by norm_num) (by norm_num)

theorem sGlobal30_hz69 : B (1524735695971823534271 / 125000000000000000) (609894278388729413841 / 50000000000000000) ((s3am 12225 46)^2) := bsq sGlobal30_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal30_hz70 : B (1524735695971823534271 / 62500000000000000) (609894278388729413841 / 25000000000000000) ((2 : ℝ) * ((s3am 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal30_hz69 (by norm_num) (by norm_num)

theorem sGlobal30_hz71 {c : ℝ} (hc : B (99 / 200) (1 / 2) c) : B (152803352043600321 / 250000000000000000) (614541197302289509 / 1000000000000000000) ((((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) / ((2 : ℝ) * ((s3am 12225 46)^2))) := bdiv (sGlobal30_hz68 hc) sGlobal30_hz70 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal30_hz72 {c : ℝ} (hc : B (99 / 200) (1 / 2) c) : B (152803352043600321 / 250000000000000000) (614541197302289509 / 1000000000000000000) (s3c1 12225 46 c) := by
    convert (sGlobal30_hz71 hc) using 1 <;>
      norm_num [s3c1] <;> ring

theorem sGlobal30_hz73 {c : ℝ} (hc : B (99 / 200) (1 / 2) c) : B (332415973159448007 / 500000000000000000) (133333333333342669 / 200000000000000000) (kdot c) := bkdot (sGlobal30_hz38 hc) sGlobal30_hz39.1 sGlobal30_hz47.2

theorem sGlobal30_hz74 : B (354659144671751459 / 500000000000000000) (709318289343502939 / 1000000000000000000) (kdot ((152803352043600321 / 250000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (61402933346361049 / 125000000000000000)) (a := (456601763365682573 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (491223466770888391 / 1000000000000000000)) (a := (456601763365682541 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal30_hz75 : B (710658835720781833 / 1000000000000000000) (14213176714415637 / 20000000000000000) (kdot ((614541197302289509 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (488612325940625397 / 1000000000000000000)) (a := (56812004755044331 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (122153081485156349 / 250000000000000000)) (a := (454496038040354623 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal30_hz76 {c : ℝ} (hc : B (99 / 200) (1 / 2) c) : B (354659144671751459 / 500000000000000000) (14213176714415637 / 20000000000000000) (kdot (s3c1 12225 46 c)) := bkdot (sGlobal30_hz72 hc) sGlobal30_hz74.1 sGlobal30_hz75.2

theorem sGlobal30_hz77 {c : ℝ} (hc : B (99 / 200) (1 / 2) c) : B (9801 / 40000) (1 / 4) (c^2) := bsq (sGlobal30_hz38 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal30_hz78 {c : ℝ} (hc : B (99 / 200) (1 / 2) c) : B (3 / 4) (30199 / 40000) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (sGlobal30_hz77 hc) (by norm_num) (by norm_num)

theorem sGlobal30_hz79 {c : ℝ} (hc : B (99 / 200) (1 / 2) c) : B (433012701892219323 / 500000000000000000) (868892973846606727 / 1000000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (sGlobal30_hz78 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal30_hz80 : B (39119999999999765769 / 1600000000000000) (3912000000000000489 / 160000000000000) ((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (149450625 : ℝ)) sGlobal30_hz10 (by norm_num) (by norm_num)

theorem sGlobal30_hz81 {c : ℝ} (hc : B (99 / 200) (1 / 2) c) : B (287880677379808079 / 500000000000000000) (144815495641111261 / 250000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (sGlobal30_hz79 hc) (sGlobal30_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal30_hz82 {c : ℝ} (hc : B (99 / 200) (1 / 2) c) : B (3519341280968132693719 / 250000000000000000) (1416295547370068309617 / 100000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) := bmul sGlobal30_hz80 (sGlobal30_hz81 hc) (by norm_num) (by norm_num)

theorem sGlobal30_hz83 {c : ℝ} (hc : B (99 / 200) (1 / 2) c) : B (3519341280968132693719 / 500000000000000000) (1416295547370068309617 / 200000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) / (2 : ℝ)) := bdiv (sGlobal30_hz82 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal30_hz84 {c : ℝ} (hc : B (99 / 200) (1 / 2) c) : B (3519341280968132693719 / 500000000000000000) (1416295547370068309617 / 200000000000000000) (s3Cpa 12225 c) := by
    convert (sGlobal30_hz83 hc) using 1 <;>
      norm_num [s3Cpa, mA] <;> ring

theorem sGlobal30_hz85 {c : ℝ} (hc : B (99 / 200) (1 / 2) c) : B (34458055963862003 / 125000000000000000) (34572152951376099 / 125000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (sGlobal30_hz79 hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal30_hz86 {c : ℝ} (hc : B (99 / 200) (1 / 2) c) : B (164545906713926763 / 500000000000000000) (333333333333356673 / 1000000000000000000) (c * (kdot c)) := bmul (sGlobal30_hz38 hc) (sGlobal30_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal30_hz87 {c : ℝ} (hc : B (99 / 200) (1 / 2) c) : B (-57668885622460649 / 1000000000000000000) (-26257294908422367 / 500000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (sGlobal30_hz85 hc) (sGlobal30_hz86 hc) (by norm_num) (by norm_num)

theorem sGlobal30_hz88 {c : ℝ} (hc : B (99 / 200) (1 / 2) c) : B (-1410004253469163044301 / 1000000000000000000) (-1283981721021846058459 / 1000000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) := bmul sGlobal30_hz80 (sGlobal30_hz87 hc) (by norm_num) (by norm_num)

theorem sGlobal30_hz89 {c : ℝ} (hc : B (99 / 200) (1 / 2) c) : B (-705002126734581522151 / 1000000000000000000) (-641990860510923029229 / 1000000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) / (2 : ℝ)) := bdiv (sGlobal30_hz88 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal30_hz90 {c : ℝ} (hc : B (99 / 200) (1 / 2) c) : B (-705002126734581522151 / 1000000000000000000) (-641990860510923029229 / 1000000000000000000) (s3Cpp 12225 c) := by
    convert (sGlobal30_hz89 hc) using 1 <;>
      norm_num [s3Cpp, mA] <;> ring

theorem sGlobal30_hz91 {c : ℝ} (hc : B (99 / 200) (1 / 2) c) : B (7153827671870003095839 / 1000000000000000000) (7196622846784079960311 / 1000000000000000000) ((s3Cpa 12225 c) + (s3r1 12225 46)) := badd (sGlobal30_hz84 hc) sGlobal30_hz33 (by norm_num) (by norm_num)

theorem sGlobal30_hz92 {c : ℝ} (hc : B (99 / 200) (1 / 2) c) : B (6477332584234486711 / 100000000000000000) (16290202182678444979 / 250000000000000000) (((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) := bdiv (sGlobal30_hz91 hc) sGlobal30_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal30_hz93 {c : ℝ} (hc : B (99 / 200) (1 / 2) c) : B (32448004433919463761 / 500000000000000000) (65283491756207840339 / 1000000000000000000) ((((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) + (s3e0 12225 46)) := badd (sGlobal30_hz92 hc) sGlobal30_hz16 (by norm_num) (by norm_num)

theorem sGlobal30_hz94 {c : ℝ} (hc : B (99 / 200) (1 / 2) c) : B (32448004433919463761 / 500000000000000000) (65283491756207840339 / 1000000000000000000) (s3Lam 12225 46 c) := by
    convert (sGlobal30_hz93 hc) using 1 <;>
      norm_num [s3Lam] <;> ring

theorem sGlobal30_hz95 {c : ℝ} (hc : B (99 / 200) (1 / 2) c) : B (-628238720112089716551 / 1000000000000000000) (-565227453888430754411 / 1000000000000000000) ((s3Cpp 12225 c) + (s3rpp 12225 46)) := badd (sGlobal30_hz90 hc) sGlobal30_hz37 (by norm_num) (by norm_num)

theorem sGlobal30_hz96 {c : ℝ} (hc : B (99 / 200) (1 / 2) c) : B (-13951981168424119197 / 31250000000000000) (-56522745388843075441 / 200000000000000000) (if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) := bweaken (bfirst (sGlobal30_hz95 hc) (sGlobal30_hz76 hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem sGlobal30_hz97 {c : ℝ} (hc : B (99 / 200) (1 / 2) c) : B (2105745983487314359751 / 500000000000000000) (1065483573970714262413 / 250000000000000000) ((s3Lam 12225 46 c)^2) := bsq (sGlobal30_hz94 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal30_hz98 {c : ℝ} (hc : B (99 / 200) (1 / 2) c) : B (37358183033216727 / 100000000000000000) (377660883181731523 / 1000000000000000000) ((s3c1 12225 46 c)^2) := bsq (sGlobal30_hz72 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal30_hz99 {c : ℝ} (hc : B (99 / 200) (1 / 2) c) : B (622339116818268477 / 1000000000000000000) (62641816966783273 / 100000000000000000) ((1 : ℝ) - ((s3c1 12225 46 c)^2)) := bsub (bpoint (1 : ℝ)) (sGlobal30_hz98 hc) (by norm_num) (by norm_num)

theorem sGlobal30_hz100 {c : ℝ} (hc : B (99 / 200) (1 / 2) c) : B (394442364870416929 / 500000000000000000) (197866459017791961 / 250000000000000000) (√((1 : ℝ) - ((s3c1 12225 46 c)^2))) := bsqrt (sGlobal30_hz99 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal30_hz101 {c : ℝ} (hc : B (99 / 200) (1 / 2) c) : B (2478354471482973121 / 1000000000000000000) (2486463256168484483 / 1000000000000000000) (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))) := bmul pi_mem (sGlobal30_hz100 hc) (by norm_num) (by norm_num)

theorem sGlobal30_hz102 {c : ℝ} (hc : B (99 / 200) (1 / 2) c) : B (846884014176893006321 / 500000000000000000) (1719662923493201179141 / 1000000000000000000) (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2))))) := bdiv (sGlobal30_hz97 hc) (sGlobal30_hz101 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal30_hz103 {c : ℝ} (hc : B (99 / 200) (1 / 2) c) : B (623652315482107099169 / 500000000000000000) (89815574784311612621 / 62500000000000000) ((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) := badd (sGlobal30_hz96 hc) (sGlobal30_hz102 hc) (by norm_num) (by norm_num)

theorem sGlobal30_hz104 : B (3762781186094069 / 250000000000000000) (376278118609407 / 25000000000000000) ((s3e0 12225 46)^2) := bsq sGlobal30_hz16 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal30_hz105 {c : ℝ} (hc : B (99 / 200) (1 / 2) c) : B (623659841044479287307 / 500000000000000000) (179633030959216272277 / 125000000000000000) (((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) := badd (sGlobal30_hz103 hc) sGlobal30_hz104 (by norm_num) (by norm_num)

theorem sGlobal30_hz106 {c : ℝ} (hc : B (99 / 200) (1 / 2) c) : B (257163351108041168949 / 200000000000000000) (184445165140981806029 / 125000000000000000) ((((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) + (s3rs 12225 46 maskSlack)) := badd (sGlobal30_hz105 hc) sGlobal30_hz29 (by norm_num) (by norm_num)

theorem sGlobal30_hz107 {c : ℝ} (hc : B (99 / 200) (1 / 2) c) : B (257163351108041168949 / 200000000000000000) (184445165140981806029 / 125000000000000000) (s3U 12225 46 maskSlack c) := by
    convert (sGlobal30_hz106 hc) using 1 <;>
      norm_num [s3U] <;> ring

theorem sGlobal30_hz108 {c : ℝ} (hc : B (99 / 200) (1 / 2) c) : B (-781765533357073796969 / 1000000000000000000) (-718754267133414834829 / 1000000000000000000) ((s3Cpp 12225 c) - (s3rpp 12225 46)) := bsub (sGlobal30_hz90 hc) sGlobal30_hz37 (by norm_num) (by norm_num)

theorem sGlobal30_hz109 {c : ℝ} (hc : B (99 / 200) (1 / 2) c) : B (-781765533357073796969 / 1000000000000000000) (-718754267133414834829 / 1000000000000000000) (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ)) := bweaken (bmin (sGlobal30_hz108 hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem sGlobal30_hz110 {c : ℝ} (hc : B (99 / 200) (1 / 2) c) : B (-555568583742174110963 / 1000000000000000000) (-509825547221416933453 / 1000000000000000000) ((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) := bmul (sGlobal30_hz76 hc) (sGlobal30_hz109 hc) (by norm_num) (by norm_num)

theorem sGlobal30_hz111 {c : ℝ} (hc : B (99 / 200) (1 / 2) c) : B (-555583634866918487243 / 1000000000000000000) (-509840598346161309729 / 1000000000000000000) (((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) := bsub (sGlobal30_hz110 hc) sGlobal30_hz104 (by norm_num) (by norm_num)

theorem sGlobal30_hz112 {c : ℝ} (hc : B (99 / 200) (1 / 2) c) : B (-594080708321042757259 / 1000000000000000000) (-27416883589870428993 / 50000000000000000) ((((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) - (s3rs 12225 46 maskSlack)) := bsub (sGlobal30_hz111 hc) sGlobal30_hz29 (by norm_num) (by norm_num)

theorem sGlobal30_hz113 {c : ℝ} (hc : B (99 / 200) (1 / 2) c) : B (-594080708321042757259 / 1000000000000000000) (-27416883589870428993 / 50000000000000000) (s3L 12225 46 maskSlack c) := by
    convert (sGlobal30_hz112 hc) using 1 <;>
      norm_num [s3L] <;> ring

theorem sGlobal30_hz114 {c : ℝ} (hc : B (99 / 200) (1 / 2) c) : B 0 (184445165140981806029 / 125000000000000000) |(s3U 12225 46 maskSlack c)| := bweaken (babs (sGlobal30_hz107 hc)) (by norm_num) (by norm_num)

theorem sGlobal30_hz115 {c : ℝ} (hc : B (99 / 200) (1 / 2) c) : B 0 (594080708321042757259 / 1000000000000000000) |(s3L 12225 46 maskSlack c)| := bweaken (babs (sGlobal30_hz113 hc)) (by norm_num) (by norm_num)

theorem sGlobal30_hz116 {c : ℝ} (hc : B (99 / 200) (1 / 2) c) : B 0 (184445165140981806029 / 125000000000000000) (max |(s3U 12225 46 maskSlack c)| |(s3L 12225 46 maskSlack c)|) := bweaken (bmax (sGlobal30_hz114 hc) (sGlobal30_hz115 hc)) (by norm_num) (by norm_num)

theorem sGlobal30_hz117 {c : ℝ} (hc : B (99 / 200) (1 / 2) c) : B 0 (184445165140981806029 / 125000000000000000) (s3nks 12225 46 maskSlack c) := by
    convert (sGlobal30_hz116 hc) using 1 <;>
      norm_num [s3nks] <;> ring

theorem sGlobal30 {c : ℝ} (hc : B (99 / 200) (1 / 2) c) :
    0 < s3am 12225 46 ∧ 0 ≤ s3dm 12225 46 c ∧
    s3dm 12225 46 c ^ 2 ≤ 2 * s3ap 12225 46 ^ 2 ∧ s3c1 12225 46 c < 1 ∧
    0 ≤ s3Cpa 12225 c - s3r1 12225 46 ∧
    s3e0 12225 46 ≤ (s3Cpa 12225 c - s3r1 12225 46) / s3ap 12225 46 ∧
    s3nks 12225 46 maskSlack c ≤ 12225 * (120701 / 1000000) := by

  refine ⟨lt_of_lt_of_le (by norm_num) sGlobal30_hz14.1,
    le_trans (by norm_num) (sGlobal30_hz64 hc).1, ?_,
    lt_of_le_of_lt (sGlobal30_hz72 hc).2 (by norm_num), ?_, ?_,
    le_trans (sGlobal30_hz117 hc).2 (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (sGlobal30_hz64 hc).1) (sGlobal30_hz64 hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) sGlobal30_hz9.1 2
    nlinarith only [h1, h2]
  · linarith only [(sGlobal30_hz84 hc).1, sGlobal30_hz33.2]
  · have hap : 0 < s3ap 12225 46 := lt_of_lt_of_le (by norm_num) sGlobal30_hz9.1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul sGlobal30_hz16.2 sGlobal30_hz9.2 (le_trans (by norm_num) sGlobal30_hz9.1) (by norm_num)
    linarith only [h, (sGlobal30_hz84 hc).1, sGlobal30_hz33.2]

end BstLean.Part255
