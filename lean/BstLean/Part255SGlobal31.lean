import BstLean.Part255SGlobal27
import BstLean.Part255Numeric10
namespace BstLean.Part255
open Real BstLean.Part130 BstLean.Part182 BstLean.Part197 BstLean.Part246
theorem sGlobal31_hz0 : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal31_hz1 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) ((√(23 : ℝ)) / (12225 : ℝ)) := bdiv sGlobal31_hz0 (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal31_hz2 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) maskSlack := by
    convert sGlobal31_hz1 using 1 <;>
      norm_num [maskSlack] <;> ring

theorem sGlobal31_hz3 : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal31_hz4 : B (6395294793910793 / 500000000000000000) (12790589587821587 / 1000000000000000000) (√((2 / 12225) : ℝ)) := bsqrt (bpoint ((2 / 12225) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal31_hz5 : B (7230130686979 / 62500000000000000) (23136418198333 / 200000000000000000) (√((2 / 149450625) : ℝ)) := bsqrt (bpoint ((2 / 149450625) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal31_hz6 : B (2211334438749598093 / 20000000000000000) (110566721937479904651 / 1000000000000000000) (√(12225 : ℝ)) := bsqrt (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal31_hz7 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))) := bmul sGlobal31_hz3 sGlobal31_hz4 (by norm_num) (by norm_num)

theorem sGlobal31_hz8 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) ((√(12225 : ℝ)) + ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := badd sGlobal31_hz6 sGlobal31_hz7 (by norm_num) (by norm_num)

theorem sGlobal31_hz9 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) (s3ap 12225 46) := by
    convert sGlobal31_hz8 using 1 <;>
      norm_num [s3ap, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal31_hz10 : B (163599182004089 / 1000000000000000000) (16359918200409 / 100000000000000000) ((2 : ℝ) / (12225 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal31_hz11 : B (1222499983640081799591 / 100000000000000000) (12224999836400817995911 / 1000000000000000000) ((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ))) := bsub (bpoint (12225 : ℝ)) sGlobal31_hz10 (by norm_num) (by norm_num)

theorem sGlobal31_hz12 : B (110566721197658827907 / 1000000000000000000) (27641680299414706977 / 250000000000000000) (√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) := bsqrt sGlobal31_hz11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal31_hz13 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) ((√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) - ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bsub sGlobal31_hz12 sGlobal31_hz7 (by norm_num) (by norm_num)

theorem sGlobal31_hz14 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) (s3am 12225 46) := by
    convert sGlobal31_hz13 using 1 <;>
      norm_num [s3am, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal31_hz15 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√((2 / 12225) : ℝ)) * (√(92 : ℝ))) := bmul sGlobal31_hz4 sGlobal31_hz3 (by norm_num) (by norm_num)

theorem sGlobal31_hz16 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) (s3e0 12225 46) := by
    convert sGlobal31_hz15 using 1 <;>
      norm_num [s3e0, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal31_hz17 : B (250196148528560847 / 500000000000000000) (100078459411424339 / 200000000000000000) (((1 / 2) : ℝ) + maskSlack) := badd (bpoint ((1 / 2) : ℝ)) sGlobal31_hz2 (by norm_num) (by norm_num)

theorem sGlobal31_hz18 : B (59827153232297998295487 / 800000000000000) (23930861292919199366019 / 320000000000000) ((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack)) := bmul (bpoint (149450625 : ℝ)) sGlobal31_hz17 (by norm_num) (by norm_num)

theorem sGlobal31_hz19 : B (1729554180017180009583 / 200000000000000000) (8647770900085900056557 / 1000000000000000000) (√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) := bsqrt sGlobal31_hz18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal31_hz20 : B (4328681281566262743499 / 500000000000000000) (8657362563132525495641 / 1000000000000000000) ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))) := badd sGlobal31_hz19 sGlobal31_hz3 (by norm_num) (by norm_num)

theorem sGlobal31_hz21 : B (110732771457999278473 / 1000000000000000000) (55366385728999643621 / 500000000000000000) ((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ)))) := bmul sGlobal31_hz4 sGlobal31_hz20 (by norm_num) (by norm_num)

theorem sGlobal31_hz22 : B (209099159 / 15625000000000000) (13382346177 / 1000000000000000000) ((2 : ℝ) / (149450625 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (149450625 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal31_hz23 : B (2452349334953899930479 / 200000000000000000) (12261746674769501594427 / 1000000000000000000) (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2) := bsq sGlobal31_hz21 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal31_hz24 : B (82045469362091 / 500000000000000000) (32818187747289 / 200000000000000000) (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2)) := bmul sGlobal31_hz22 sGlobal31_hz23 (by norm_num) (by norm_num)

theorem sGlobal31_hz25 : B (82045469362091 / 250000000000000000) (32818187747289 / 100000000000000000) ((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) := bmul (bpoint (2 : ℝ)) sGlobal31_hz24 (by norm_num) (by norm_num)

theorem sGlobal31_hz26 : B (117258080744995992792057 / 1000000000000000000) (58629040372497996396029 / 500000000000000000) (√(13749457500 : ℝ)) := bsqrt (bpoint (13749457500 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal31_hz27 : B (117304080744995992792057 / 1000000000000000000) (58652040372497996396029 / 500000000000000000) ((√(13749457500 : ℝ)) + (46 : ℝ)) := badd sGlobal31_hz26 (bpoint (46 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal31_hz28 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal31_hz25 sGlobal31_hz27 (by norm_num) (by norm_num)

theorem sGlobal31_hz29 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (s3rs 12225 46 maskSlack) := by
    convert sGlobal31_hz28 using 1 <;>
      norm_num [s3rs, s3pp, s3K, mA, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal31_hz30 : B (490797546012267 / 1000000000000000000) (49079754601227 / 100000000000000000) ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (3 : ℝ)) sGlobal31_hz10 (by norm_num) (by norm_num)

theorem sGlobal31_hz31 : B (490797546012267 / 500000000000000000) (49079754601227 / 50000000000000000) ((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal31_hz30 (by norm_num) (by norm_num)

theorem sGlobal31_hz32 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal31_hz31 sGlobal31_hz27 (by norm_num) (by norm_num)

theorem sGlobal31_hz33 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (s3r1 12225 46) := by
    convert sGlobal31_hz32 using 1 <;>
      norm_num [s3r1, mA] <;> ring

theorem sGlobal31_hz34 : B (163599182004089 / 500000000000000000) (16359918200409 / 50000000000000000) ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (2 : ℝ)) sGlobal31_hz10 (by norm_num) (by norm_num)

theorem sGlobal31_hz35 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal31_hz34 (by norm_num) (by norm_num)

theorem sGlobal31_hz36 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal31_hz35 sGlobal31_hz27 (by norm_num) (by norm_num)

theorem sGlobal31_hz37 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (s3rpp 12225 46) := by
    convert sGlobal31_hz36 using 1 <;>
      norm_num [s3rpp, mA] <;> ring

theorem sGlobal31_hz38 {c : ℝ} (hc : B (1 / 2) (101 / 200) c) : B (1 / 2) (101 / 200) c := hc

theorem sGlobal31_hz39 : B (26666666666666409 / 40000000000000000) (133333333333342669 / 200000000000000000) (kdot ((1 / 2))) := by
    constructor
    · apply bkdot_lower (q := (115470053837925153 / 200000000000000000)) (a := (523598775598308991 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (144337567297406441 / 250000000000000000)) (a := (523598775598225551 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal31_hz40 : B (1 / 4) (1 / 4) (((1 / 2) : ℝ)^2) := bsq (bpoint ((1 / 2) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal31_hz41 : B (3 / 4) (3 / 4) ((1 : ℝ) - (((1 / 2) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal31_hz40 (by norm_num) (by norm_num)

theorem sGlobal31_hz42 : B (433012701892219323 / 500000000000000000) (866025403784438647 / 1000000000000000000) (√((1 : ℝ) - (((1 / 2) : ℝ)^2))) := bsqrt sGlobal31_hz41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal31_hz43 : B (34458055963862003 / 125000000000000000) (11026577908435841 / 40000000000000000) ((√((1 : ℝ) - (((1 / 2) : ℝ)^2))) / Real.pi) := bdiv sGlobal31_hz42 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal31_hz44 : B (5208333333333283 / 15625000000000000) (333333333333356673 / 1000000000000000000) (((1 / 2) : ℝ) * (kdot ((1 / 2)))) := bmul (bpoint ((1 / 2) : ℝ)) sGlobal31_hz39 (by norm_num) (by norm_num)

theorem sGlobal31_hz45 : B (76124722630528267 / 125000000000000000) (304498890522126349 / 500000000000000000) (((√((1 : ℝ) - (((1 / 2) : ℝ)^2))) / Real.pi) + (((1 / 2) : ℝ) * (kdot ((1 / 2))))) := badd sGlobal31_hz43 sGlobal31_hz44 (by norm_num) (by norm_num)

theorem sGlobal31_hz46 : B (76124722630528267 / 125000000000000000) (304498890522126349 / 500000000000000000) (kappa ((1 / 2))) := by rw [kappa_eq]; exact sGlobal31_hz45

theorem sGlobal31_hz47 : B (83563439141160113 / 125000000000000000) (33425375656465959 / 50000000000000000) (kdot ((101 / 200))) := by
    constructor
    · apply bkdot_lower (q := (573501224484350891 / 1000000000000000000)) (a := (520707180736631049 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (57350122448435089 / 100000000000000000)) (a := (520707180736570927 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal31_hz48 : B (10201 / 40000) (10201 / 40000) (((101 / 200) : ℝ)^2) := bsq (bpoint ((101 / 200) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal31_hz49 : B (29799 / 40000) (29799 / 40000) ((1 : ℝ) - (((101 / 200) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal31_hz48 (by norm_num) (by norm_num)

theorem sGlobal31_hz50 : B (86311934284894809 / 100000000000000000) (863119342848948091 / 1000000000000000000) (√((1 : ℝ) - (((101 / 200) : ℝ)^2))) := bsqrt sGlobal31_hz49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal31_hz51 : B (54947883957055373 / 200000000000000000) (137369709892638433 / 500000000000000000) ((√((1 : ℝ) - (((101 / 200) : ℝ)^2))) / Real.pi) := bdiv sGlobal31_hz50 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal31_hz52 : B (42199536766285857 / 125000000000000000) (168798147065153093 / 500000000000000000) (((101 / 200) : ℝ) * (kdot ((101 / 200)))) := bmul (bpoint ((101 / 200) : ℝ)) sGlobal31_hz47 (by norm_num) (by norm_num)

theorem sGlobal31_hz53 : B (612335713915563721 / 1000000000000000000) (153083928478895763 / 250000000000000000) (((√((1 : ℝ) - (((101 / 200) : ℝ)^2))) / Real.pi) + (((101 / 200) : ℝ) * (kdot ((101 / 200))))) := badd sGlobal31_hz51 sGlobal31_hz52 (by norm_num) (by norm_num)

theorem sGlobal31_hz54 : B (612335713915563721 / 1000000000000000000) (153083928478895763 / 250000000000000000) (kappa ((101 / 200))) := by rw [kappa_eq]; exact sGlobal31_hz53

theorem sGlobal31_hz55 {c : ℝ} (hc : B (1 / 2) (101 / 200) c) : B (76124722630528267 / 125000000000000000) (153083928478895763 / 250000000000000000) (kappa c) := bkappa (sGlobal31_hz38 hc) (by norm_num) (by norm_num) sGlobal31_hz46.1 sGlobal31_hz54.2

theorem sGlobal31_hz56 : B 24450 24450 ((2 : ℝ) * (12225 : ℝ)) := bmul (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal31_hz57 {c : ℝ} (hc : B (1 / 2) (101 / 200) c) : B (96916071521104237 / 250000000000000000) (48875277369471733 / 125000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (sGlobal31_hz55 hc) (by norm_num) (by norm_num)

theorem sGlobal31_hz58 {c : ℝ} (hc : B (1 / 2) (101 / 200) c) : B (47391958973819971893 / 5000000000000000) (23900010633671677437 / 2500000000000000) (((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) := bmul sGlobal31_hz56 (sGlobal31_hz57 hc) (by norm_num) (by norm_num)

theorem sGlobal31_hz59 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (4 : ℝ)) sGlobal31_hz10 (by norm_num) (by norm_num)

theorem sGlobal31_hz60 {c : ℝ} (hc : B (1 / 2) (101 / 200) c) : B (14809986156823853691 / 1562500000000000) (2390000899767985739611 / 250000000000000000) ((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bsub (sGlobal31_hz58 hc) sGlobal31_hz59 (by norm_num) (by norm_num)

theorem sGlobal31_hz61 {c : ℝ} (hc : B (1 / 2) (101 / 200) c) : B (97357029229364154639 / 1000000000000000000) (4888763544873065079 / 50000000000000000) (√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) := bsqrt (sGlobal31_hz60 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal31_hz62 : B (30670756373515103 / 125000000000000000) (122683025494060423 / 500000000000000000) ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal31_hz7 (by norm_num) (by norm_num)

theorem sGlobal31_hz63 {c : ℝ} (hc : B (1 / 2) (101 / 200) c) : B (97111663178376033793 / 1000000000000000000) (24382476211618295189 / 250000000000000000) ((√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) - ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))))) := bsub (sGlobal31_hz61 hc) sGlobal31_hz62 (by norm_num) (by norm_num)

theorem sGlobal31_hz64 {c : ℝ} (hc : B (1 / 2) (101 / 200) c) : B (97111663178376033793 / 1000000000000000000) (24382476211618295189 / 250000000000000000) (s3dm 12225 46 c) := by
    convert (sGlobal31_hz63 hc) using 1 <;>
      norm_num [s3dm, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal31_hz65 : B (6126072185528622723889 / 500000000000000000) (2450428874211449090087 / 200000000000000000) ((s3ap 12225 46)^2) := bsq sGlobal31_hz9 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal31_hz66 : B (6126072185528622723889 / 250000000000000000) (2450428874211449090087 / 100000000000000000) ((2 : ℝ) * ((s3ap 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal31_hz65 (by norm_num) (by norm_num)

theorem sGlobal31_hz67 {c : ℝ} (hc : B (1 / 2) (101 / 200) c) : B (4715337562635177796891 / 500000000000000000) (2378020584840528207983 / 250000000000000000) ((s3dm 12225 46 c)^2) := bsq (sGlobal31_hz64 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal31_hz68 {c : ℝ} (hc : B (1 / 2) (101 / 200) c) : B (1874025800344047257953 / 125000000000000000) (942100851052758456693 / 62500000000000000) (((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) := bsub sGlobal31_hz66 (sGlobal31_hz67 hc) (by norm_num) (by norm_num)

theorem sGlobal31_hz69 : B (1524735695971823534271 / 125000000000000000) (609894278388729413841 / 50000000000000000) ((s3am 12225 46)^2) := bsq sGlobal31_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal31_hz70 : B (1524735695971823534271 / 62500000000000000) (609894278388729413841 / 25000000000000000) ((2 : ℝ) * ((s3am 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal31_hz69 (by norm_num) (by norm_num)

theorem sGlobal31_hz71 {c : ℝ} (hc : B (1 / 2) (101 / 200) c) : B (307270598651131477 / 500000000000000000) (123575627374853311 / 200000000000000000) ((((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) / ((2 : ℝ) * ((s3am 12225 46)^2))) := bdiv (sGlobal31_hz68 hc) sGlobal31_hz70 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal31_hz72 {c : ℝ} (hc : B (1 / 2) (101 / 200) c) : B (307270598651131477 / 500000000000000000) (123575627374853311 / 200000000000000000) (s3c1 12225 46 c) := by
    convert (sGlobal31_hz71 hc) using 1 <;>
      norm_num [s3c1] <;> ring

theorem sGlobal31_hz73 {c : ℝ} (hc : B (1 / 2) (101 / 200) c) : B (26666666666666409 / 40000000000000000) (33425375656465959 / 50000000000000000) (kdot c) := bkdot (sGlobal31_hz38 hc) sGlobal31_hz39.1 sGlobal31_hz47.2

theorem sGlobal31_hz74 : B (355329417860385559 / 500000000000000000) (142131767144154227 / 200000000000000000) (kdot ((307270598651131477 / 500000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (244306162970323123 / 500000000000000000)) (a := (454496038040371479 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (97722465188129249 / 200000000000000000)) (a := (454496038040371453 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal31_hz75 : B (712007498976065531 / 1000000000000000000) (89000937372008193 / 125000000000000000) (kdot ((123575627374853311 / 200000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (485990791278543561 / 1000000000000000000)) (a := (452377562752871767 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (12149769781963589 / 25000000000000000)) (a := (113094390688217937 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal31_hz76 {c : ℝ} (hc : B (1 / 2) (101 / 200) c) : B (355329417860385559 / 500000000000000000) (89000937372008193 / 125000000000000000) (kdot (s3c1 12225 46 c)) := bkdot (sGlobal31_hz72 hc) sGlobal31_hz74.1 sGlobal31_hz75.2

theorem sGlobal31_hz77 {c : ℝ} (hc : B (1 / 2) (101 / 200) c) : B (1 / 4) (10201 / 40000) (c^2) := bsq (sGlobal31_hz38 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal31_hz78 {c : ℝ} (hc : B (1 / 2) (101 / 200) c) : B (29799 / 40000) (3 / 4) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (sGlobal31_hz77 hc) (by norm_num) (by norm_num)

theorem sGlobal31_hz79 {c : ℝ} (hc : B (1 / 2) (101 / 200) c) : B (86311934284894809 / 100000000000000000) (866025403784438647 / 1000000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (sGlobal31_hz78 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal31_hz80 : B (39119999999999765769 / 1600000000000000) (3912000000000000489 / 160000000000000) ((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (149450625 : ℝ)) sGlobal31_hz10 (by norm_num) (by norm_num)

theorem sGlobal31_hz81 {c : ℝ} (hc : B (1 / 2) (101 / 200) c) : B (1150825790465253 / 2000000000000000) (144736122247687391 / 250000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (sGlobal31_hz79 hc) (sGlobal31_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal31_hz82 {c : ℝ} (hc : B (1 / 2) (101 / 200) c) : B (3517211322109408421947 / 250000000000000000) (35387981889559571523 / 2500000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) := bmul sGlobal31_hz80 (sGlobal31_hz81 hc) (by norm_num) (by norm_num)

theorem sGlobal31_hz83 {c : ℝ} (hc : B (1 / 2) (101 / 200) c) : B (3517211322109408421947 / 500000000000000000) (35387981889559571523 / 5000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) / (2 : ℝ)) := bdiv (sGlobal31_hz82 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal31_hz84 {c : ℝ} (hc : B (1 / 2) (101 / 200) c) : B (3517211322109408421947 / 500000000000000000) (35387981889559571523 / 5000000000000000) (s3Cpa 12225 c) := by
    convert (sGlobal31_hz83 hc) using 1 <;>
      norm_num [s3Cpa, mA] <;> ring

theorem sGlobal31_hz85 {c : ℝ} (hc : B (1 / 2) (101 / 200) c) : B (54947883957055373 / 200000000000000000) (11026577908435841 / 40000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (sGlobal31_hz79 hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal31_hz86 {c : ℝ} (hc : B (1 / 2) (101 / 200) c) : B (5208333333333283 / 15625000000000000) (168798147065153093 / 500000000000000000) (c * (kdot c)) := bmul (sGlobal31_hz38 hc) (sGlobal31_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal31_hz87 {c : ℝ} (hc : B (1 / 2) (101 / 200) c) : B (-62856874345029321 / 1000000000000000000) (-57668885622434087 / 1000000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (sGlobal31_hz85 hc) (sGlobal31_hz86 hc) (by norm_num) (by norm_num)

theorem sGlobal31_hz88 {c : ℝ} (hc : B (1 / 2) (101 / 200) c) : B (-1536850577735967090557 / 1000000000000000000) (-1410004253468504984749 / 1000000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) := bmul sGlobal31_hz80 (sGlobal31_hz87 hc) (by norm_num) (by norm_num)

theorem sGlobal31_hz89 {c : ℝ} (hc : B (1 / 2) (101 / 200) c) : B (-768425288867983545279 / 1000000000000000000) (-352501063367126246187 / 500000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) / (2 : ℝ)) := bdiv (sGlobal31_hz88 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal31_hz90 {c : ℝ} (hc : B (1 / 2) (101 / 200) c) : B (-768425288867983545279 / 1000000000000000000) (-352501063367126246187 / 500000000000000000) (s3Cpp 12225 c) := by
    convert (sGlobal31_hz89 hc) using 1 <;>
      norm_num [s3Cpp, mA] <;> ring

theorem sGlobal31_hz91 {c : ℝ} (hc : B (1 / 2) (101 / 200) c) : B (1429913550830510910459 / 200000000000000000) (3596370743922826358413 / 500000000000000000) ((s3Cpa 12225 c) + (s3r1 12225 46)) := badd (sGlobal31_hz84 hc) sGlobal31_hz33 (by norm_num) (by norm_num)

theorem sGlobal31_hz92 {c : ℝ} (hc : B (1 / 2) (101 / 200) c) : B (12946951003380572713 / 200000000000000000) (65125665512458967289 / 1000000000000000000) (((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) := bdiv (sGlobal31_hz91 hc) sGlobal31_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal31_hz93 {c : ℝ} (hc : B (1 / 2) (101 / 200) c) : B (64857438042396923977 / 1000000000000000000) (509752722952758029 / 7812500000000000) ((((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) + (s3e0 12225 46)) := badd (sGlobal31_hz92 hc) sGlobal31_hz16 (by norm_num) (by norm_num)

theorem sGlobal31_hz94 {c : ℝ} (hc : B (1 / 2) (101 / 200) c) : B (64857438042396923977 / 1000000000000000000) (509752722952758029 / 7812500000000000) (s3Lam 12225 46 c) := by
    convert (sGlobal31_hz93 hc) using 1 <;>
      norm_num [s3Lam] <;> ring

theorem sGlobal31_hz95 {c : ℝ} (hc : B (1 / 2) (101 / 200) c) : B (-691661882245491739679 / 1000000000000000000) (-157059680027940054389 / 250000000000000000) ((s3Cpp 12225 c) + (s3rpp 12225 46)) := badd (sGlobal31_hz90 hc) sGlobal31_hz37 (by norm_num) (by norm_num)

theorem sGlobal31_hz96 {c : ℝ} (hc : B (1 / 2) (101 / 200) c) : B (-492468446914690526707 / 1000000000000000000) (-157059680027940054389 / 500000000000000000) (if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) := bweaken (bfirst (sGlobal31_hz95 hc) (sGlobal31_hz76 hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem sGlobal31_hz97 {c : ℝ} (hc : B (1 / 2) (101 / 200) c) : B (841297453884671147651 / 200000000000000000) (2128673493465098504503 / 500000000000000000) ((s3Lam 12225 46 c)^2) := bsq (sGlobal31_hz94 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal31_hz98 {c : ℝ} (hc : B (1 / 2) (101 / 200) c) : B (94415220795424721 / 250000000000000000) (95443348006803719 / 250000000000000000) ((s3c1 12225 46 c)^2) := bsq (sGlobal31_hz72 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal31_hz99 {c : ℝ} (hc : B (1 / 2) (101 / 200) c) : B (154556651993196281 / 250000000000000000) (155584779204575279 / 250000000000000000) ((1 : ℝ) - ((s3c1 12225 46 c)^2)) := bsub (bpoint (1 : ℝ)) (sGlobal31_hz98 hc) (by norm_num) (by norm_num)

theorem sGlobal31_hz100 {c : ℝ} (hc : B (1 / 2) (101 / 200) c) : B (786273875931780607 / 1000000000000000000) (394442364870427273 / 500000000000000000) (√((1 : ℝ) - ((s3c1 12225 46 c)^2))) := bsqrt (sGlobal31_hz99 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal31_hz101 {c : ℝ} (hc : B (1 / 2) (101 / 200) c) : B (2470152232336854499 / 1000000000000000000) (619588617870759529 / 250000000000000000) (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))) := bmul pi_mem (sGlobal31_hz100 hc) (by norm_num) (by norm_num)

theorem sGlobal31_hz102 {c : ℝ} (hc : B (1 / 2) (101 / 200) c) : B (1697290406931260874419 / 1000000000000000000) (1723516037269731672859 / 1000000000000000000) (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2))))) := bdiv (sGlobal31_hz97 hc) (sGlobal31_hz101 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal31_hz103 {c : ℝ} (hc : B (1 / 2) (101 / 200) c) : B (18825343125258911683 / 15625000000000000) (1409396677213851564081 / 1000000000000000000) ((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) := badd (sGlobal31_hz96 hc) (sGlobal31_hz102 hc) (by norm_num) (by norm_num)

theorem sGlobal31_hz104 : B (3762781186094069 / 250000000000000000) (376278118609407 / 25000000000000000) ((s3e0 12225 46)^2) := bsq sGlobal31_hz16 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal31_hz105 {c : ℝ} (hc : B (1 / 2) (101 / 200) c) : B (301209252785328680997 / 250000000000000000) (1409411728338595940361 / 1000000000000000000) (((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) := badd (sGlobal31_hz103 hc) sGlobal31_hz104 (by norm_num) (by norm_num)

theorem sGlobal31_hz106 {c : ℝ} (hc : B (1 / 2) (101 / 200) c) : B (1243334084592561994119 / 1000000000000000000) (1447908801792720210377 / 1000000000000000000) ((((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) + (s3rs 12225 46 maskSlack)) := badd (sGlobal31_hz105 hc) sGlobal31_hz29 (by norm_num) (by norm_num)

theorem sGlobal31_hz107 {c : ℝ} (hc : B (1 / 2) (101 / 200) c) : B (1243334084592561994119 / 1000000000000000000) (1447908801792720210377 / 1000000000000000000) (s3U 12225 46 maskSlack c) := by
    convert (sGlobal31_hz106 hc) using 1 <;>
      norm_num [s3U] <;> ring

theorem sGlobal31_hz108 {c : ℝ} (hc : B (1 / 2) (101 / 200) c) : B (-845188695490475820097 / 1000000000000000000) (-390882766678372148987 / 500000000000000000) ((s3Cpp 12225 c) - (s3rpp 12225 46)) := bsub (sGlobal31_hz90 hc) sGlobal31_hz37 (by norm_num) (by norm_num)

theorem sGlobal31_hz109 {c : ℝ} (hc : B (1 / 2) (101 / 200) c) : B (-845188695490475820097 / 1000000000000000000) (-390882766678372148987 / 500000000000000000) (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ)) := bweaken (bmin (sGlobal31_hz108 hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem sGlobal31_hz110 {c : ℝ} (hc : B (1 / 2) (101 / 200) c) : B (-37611293077438570959 / 62500000000000000) (-277784291870965779841 / 500000000000000000) ((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) := bmul (sGlobal31_hz76 hc) (sGlobal31_hz109 hc) (by norm_num) (by norm_num)

theorem sGlobal31_hz111 {c : ℝ} (hc : B (1 / 2) (101 / 200) c) : B (-75224467545470188953 / 125000000000000000) (-277791817433337967979 / 500000000000000000) (((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) := bsub (sGlobal31_hz110 hc) sGlobal31_hz104 (by norm_num) (by norm_num)

theorem sGlobal31_hz112 {c : ℝ} (hc : B (1 / 2) (101 / 200) c) : B (-16007320345447144541 / 25000000000000000) (-594080708317923206089 / 1000000000000000000) ((((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) - (s3rs 12225 46 maskSlack)) := bsub (sGlobal31_hz111 hc) sGlobal31_hz29 (by norm_num) (by norm_num)

theorem sGlobal31_hz113 {c : ℝ} (hc : B (1 / 2) (101 / 200) c) : B (-16007320345447144541 / 25000000000000000) (-594080708317923206089 / 1000000000000000000) (s3L 12225 46 maskSlack c) := by
    convert (sGlobal31_hz112 hc) using 1 <;>
      norm_num [s3L] <;> ring

theorem sGlobal31_hz114 {c : ℝ} (hc : B (1 / 2) (101 / 200) c) : B 0 (1447908801792720210377 / 1000000000000000000) |(s3U 12225 46 maskSlack c)| := bweaken (babs (sGlobal31_hz107 hc)) (by norm_num) (by norm_num)

theorem sGlobal31_hz115 {c : ℝ} (hc : B (1 / 2) (101 / 200) c) : B 0 (16007320345447144541 / 25000000000000000) |(s3L 12225 46 maskSlack c)| := bweaken (babs (sGlobal31_hz113 hc)) (by norm_num) (by norm_num)

theorem sGlobal31_hz116 {c : ℝ} (hc : B (1 / 2) (101 / 200) c) : B 0 (1447908801792720210377 / 1000000000000000000) (max |(s3U 12225 46 maskSlack c)| |(s3L 12225 46 maskSlack c)|) := bweaken (bmax (sGlobal31_hz114 hc) (sGlobal31_hz115 hc)) (by norm_num) (by norm_num)

theorem sGlobal31_hz117 {c : ℝ} (hc : B (1 / 2) (101 / 200) c) : B 0 (1447908801792720210377 / 1000000000000000000) (s3nks 12225 46 maskSlack c) := by
    convert (sGlobal31_hz116 hc) using 1 <;>
      norm_num [s3nks] <;> ring

theorem sGlobal31 {c : ℝ} (hc : B (1 / 2) (101 / 200) c) :
    0 < s3am 12225 46 ∧ 0 ≤ s3dm 12225 46 c ∧
    s3dm 12225 46 c ^ 2 ≤ 2 * s3ap 12225 46 ^ 2 ∧ s3c1 12225 46 c < 1 ∧
    0 ≤ s3Cpa 12225 c - s3r1 12225 46 ∧
    s3e0 12225 46 ≤ (s3Cpa 12225 c - s3r1 12225 46) / s3ap 12225 46 ∧
    s3nks 12225 46 maskSlack c ≤ 12225 * (118439 / 1000000) := by

  refine ⟨lt_of_lt_of_le (by norm_num) sGlobal31_hz14.1,
    le_trans (by norm_num) (sGlobal31_hz64 hc).1, ?_,
    lt_of_le_of_lt (sGlobal31_hz72 hc).2 (by norm_num), ?_, ?_,
    le_trans (sGlobal31_hz117 hc).2 (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (sGlobal31_hz64 hc).1) (sGlobal31_hz64 hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) sGlobal31_hz9.1 2
    nlinarith only [h1, h2]
  · linarith only [(sGlobal31_hz84 hc).1, sGlobal31_hz33.2]
  · have hap : 0 < s3ap 12225 46 := lt_of_lt_of_le (by norm_num) sGlobal31_hz9.1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul sGlobal31_hz16.2 sGlobal31_hz9.2 (le_trans (by norm_num) sGlobal31_hz9.1) (by norm_num)
    linarith only [h, (sGlobal31_hz84 hc).1, sGlobal31_hz33.2]

end BstLean.Part255
