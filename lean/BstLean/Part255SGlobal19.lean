import BstLean.Part255SGlobal15
import BstLean.Part255Numeric10
namespace BstLean.Part255
open Real BstLean.Part130 BstLean.Part182 BstLean.Part197 BstLean.Part246
theorem sGlobal19_hz0 : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal19_hz1 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) ((√(23 : ℝ)) / (12225 : ℝ)) := bdiv sGlobal19_hz0 (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal19_hz2 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) maskSlack := by
    convert sGlobal19_hz1 using 1 <;>
      norm_num [maskSlack] <;> ring

theorem sGlobal19_hz3 : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal19_hz4 : B (6395294793910793 / 500000000000000000) (12790589587821587 / 1000000000000000000) (√((2 / 12225) : ℝ)) := bsqrt (bpoint ((2 / 12225) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal19_hz5 : B (7230130686979 / 62500000000000000) (23136418198333 / 200000000000000000) (√((2 / 149450625) : ℝ)) := bsqrt (bpoint ((2 / 149450625) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal19_hz6 : B (2211334438749598093 / 20000000000000000) (110566721937479904651 / 1000000000000000000) (√(12225 : ℝ)) := bsqrt (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal19_hz7 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))) := bmul sGlobal19_hz3 sGlobal19_hz4 (by norm_num) (by norm_num)

theorem sGlobal19_hz8 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) ((√(12225 : ℝ)) + ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := badd sGlobal19_hz6 sGlobal19_hz7 (by norm_num) (by norm_num)

theorem sGlobal19_hz9 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) (s3ap 12225 46) := by
    convert sGlobal19_hz8 using 1 <;>
      norm_num [s3ap, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal19_hz10 : B (163599182004089 / 1000000000000000000) (16359918200409 / 100000000000000000) ((2 : ℝ) / (12225 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal19_hz11 : B (1222499983640081799591 / 100000000000000000) (12224999836400817995911 / 1000000000000000000) ((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ))) := bsub (bpoint (12225 : ℝ)) sGlobal19_hz10 (by norm_num) (by norm_num)

theorem sGlobal19_hz12 : B (110566721197658827907 / 1000000000000000000) (27641680299414706977 / 250000000000000000) (√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) := bsqrt sGlobal19_hz11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal19_hz13 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) ((√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) - ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bsub sGlobal19_hz12 sGlobal19_hz7 (by norm_num) (by norm_num)

theorem sGlobal19_hz14 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) (s3am 12225 46) := by
    convert sGlobal19_hz13 using 1 <;>
      norm_num [s3am, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal19_hz15 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√((2 / 12225) : ℝ)) * (√(92 : ℝ))) := bmul sGlobal19_hz4 sGlobal19_hz3 (by norm_num) (by norm_num)

theorem sGlobal19_hz16 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) (s3e0 12225 46) := by
    convert sGlobal19_hz15 using 1 <;>
      norm_num [s3e0, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal19_hz17 : B (250196148528560847 / 500000000000000000) (100078459411424339 / 200000000000000000) (((1 / 2) : ℝ) + maskSlack) := badd (bpoint ((1 / 2) : ℝ)) sGlobal19_hz2 (by norm_num) (by norm_num)

theorem sGlobal19_hz18 : B (59827153232297998295487 / 800000000000000) (23930861292919199366019 / 320000000000000) ((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack)) := bmul (bpoint (149450625 : ℝ)) sGlobal19_hz17 (by norm_num) (by norm_num)

theorem sGlobal19_hz19 : B (1729554180017180009583 / 200000000000000000) (8647770900085900056557 / 1000000000000000000) (√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) := bsqrt sGlobal19_hz18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal19_hz20 : B (4328681281566262743499 / 500000000000000000) (8657362563132525495641 / 1000000000000000000) ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))) := badd sGlobal19_hz19 sGlobal19_hz3 (by norm_num) (by norm_num)

theorem sGlobal19_hz21 : B (110732771457999278473 / 1000000000000000000) (55366385728999643621 / 500000000000000000) ((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ)))) := bmul sGlobal19_hz4 sGlobal19_hz20 (by norm_num) (by norm_num)

theorem sGlobal19_hz22 : B (209099159 / 15625000000000000) (13382346177 / 1000000000000000000) ((2 : ℝ) / (149450625 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (149450625 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal19_hz23 : B (2452349334953899930479 / 200000000000000000) (12261746674769501594427 / 1000000000000000000) (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2) := bsq sGlobal19_hz21 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal19_hz24 : B (82045469362091 / 500000000000000000) (32818187747289 / 200000000000000000) (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2)) := bmul sGlobal19_hz22 sGlobal19_hz23 (by norm_num) (by norm_num)

theorem sGlobal19_hz25 : B (82045469362091 / 250000000000000000) (32818187747289 / 100000000000000000) ((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) := bmul (bpoint (2 : ℝ)) sGlobal19_hz24 (by norm_num) (by norm_num)

theorem sGlobal19_hz26 : B (117258080744995992792057 / 1000000000000000000) (58629040372497996396029 / 500000000000000000) (√(13749457500 : ℝ)) := bsqrt (bpoint (13749457500 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal19_hz27 : B (117304080744995992792057 / 1000000000000000000) (58652040372497996396029 / 500000000000000000) ((√(13749457500 : ℝ)) + (46 : ℝ)) := badd sGlobal19_hz26 (bpoint (46 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal19_hz28 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal19_hz25 sGlobal19_hz27 (by norm_num) (by norm_num)

theorem sGlobal19_hz29 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (s3rs 12225 46 maskSlack) := by
    convert sGlobal19_hz28 using 1 <;>
      norm_num [s3rs, s3pp, s3K, mA, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal19_hz30 : B (490797546012267 / 1000000000000000000) (49079754601227 / 100000000000000000) ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (3 : ℝ)) sGlobal19_hz10 (by norm_num) (by norm_num)

theorem sGlobal19_hz31 : B (490797546012267 / 500000000000000000) (49079754601227 / 50000000000000000) ((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal19_hz30 (by norm_num) (by norm_num)

theorem sGlobal19_hz32 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal19_hz31 sGlobal19_hz27 (by norm_num) (by norm_num)

theorem sGlobal19_hz33 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (s3r1 12225 46) := by
    convert sGlobal19_hz32 using 1 <;>
      norm_num [s3r1, mA] <;> ring

theorem sGlobal19_hz34 : B (163599182004089 / 500000000000000000) (16359918200409 / 50000000000000000) ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (2 : ℝ)) sGlobal19_hz10 (by norm_num) (by norm_num)

theorem sGlobal19_hz35 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal19_hz34 (by norm_num) (by norm_num)

theorem sGlobal19_hz36 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal19_hz35 sGlobal19_hz27 (by norm_num) (by norm_num)

theorem sGlobal19_hz37 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (s3rpp 12225 46) := by
    convert sGlobal19_hz36 using 1 <;>
      norm_num [s3rpp, mA] <;> ring

theorem sGlobal19_hz38 {c : ℝ} (hc : B (11 / 25) (89 / 200) c) : B (11 / 25) (89 / 200) c := hc

theorem sGlobal19_hz39 : B (322510780936897579 / 500000000000000000) (645021561876114903 / 1000000000000000000) (kdot ((11 / 25))) := by
    constructor
    · apply bkdot_lower (q := (124721912892464713 / 200000000000000000)) (a := (557598826700032049 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (155902391115580891 / 250000000000000000)) (a := (111519765339277641 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal19_hz40 : B (121 / 625) (121 / 625) (((11 / 25) : ℝ)^2) := bsq (bpoint ((11 / 25) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal19_hz41 : B (504 / 625) (504 / 625) ((1 : ℝ) - (((11 / 25) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal19_hz40 (by norm_num) (by norm_num)

theorem sGlobal19_hz42 : B (224499443206436483 / 250000000000000000) (897997772825745933 / 1000000000000000000) (√((1 : ℝ) - (((11 / 25) : ℝ)^2))) := bsqrt sGlobal19_hz41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal19_hz43 : B (285841568861460699 / 1000000000000000000) (2858415688614607 / 10000000000000000) ((√((1 : ℝ) - (((11 / 25) : ℝ)^2))) / Real.pi) := bdiv sGlobal19_hz42 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal19_hz44 : B (283809487224469869 / 1000000000000000000) (141904743612745279 / 500000000000000000) (((11 / 25) : ℝ) * (kdot ((11 / 25)))) := bmul (bpoint ((11 / 25) : ℝ)) sGlobal19_hz39 (by norm_num) (by norm_num)

theorem sGlobal19_hz45 : B (71206382010741321 / 125000000000000000) (284825528043475629 / 500000000000000000) (((√((1 : ℝ) - (((11 / 25) : ℝ)^2))) / Real.pi) + (((11 / 25) : ℝ) * (kdot ((11 / 25))))) := badd sGlobal19_hz43 sGlobal19_hz44 (by norm_num) (by norm_num)

theorem sGlobal19_hz46 : B (71206382010741321 / 125000000000000000) (284825528043475629 / 500000000000000000) (kappa ((11 / 25))) := by rw [kappa_eq]; exact sGlobal19_hz45

theorem sGlobal19_hz47 : B (646796326476973757 / 1000000000000000000) (323398163239342143 / 500000000000000000) (kdot ((89 / 200))) := by
    constructor
    · apply bkdot_lower (q := (309872169201551143 / 500000000000000000)) (a := (17337844780638547 / 31250000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (123948867680620457 / 200000000000000000)) (a := (554811032977746613 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal19_hz48 : B (7921 / 40000) (7921 / 40000) (((89 / 200) : ℝ)^2) := bsq (bpoint ((89 / 200) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal19_hz49 : B (32079 / 40000) (32079 / 40000) ((1 : ℝ) - (((89 / 200) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal19_hz48 (by norm_num) (by norm_num)

theorem sGlobal19_hz50 : B (447765284496241401 / 500000000000000000) (895530568992482803 / 1000000000000000000) (√((1 : ℝ) - (((89 / 200) : ℝ)^2))) := bsqrt sGlobal19_hz49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal19_hz51 : B (114022493396041 / 400000000000000) (285056233490102501 / 1000000000000000000) ((√((1 : ℝ) - (((89 / 200) : ℝ)^2))) / Real.pi) := bdiv sGlobal19_hz50 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal19_hz52 : B (287824365282253321 / 1000000000000000000) (71956091320753627 / 250000000000000000) (((89 / 200) : ℝ) * (kdot ((89 / 200)))) := bmul (bpoint ((89 / 200) : ℝ)) sGlobal19_hz47 (by norm_num) (by norm_num)

theorem sGlobal19_hz53 : B (572880598772355821 / 1000000000000000000) (572880598773117009 / 1000000000000000000) (((√((1 : ℝ) - (((89 / 200) : ℝ)^2))) / Real.pi) + (((89 / 200) : ℝ) * (kdot ((89 / 200))))) := badd sGlobal19_hz51 sGlobal19_hz52 (by norm_num) (by norm_num)

theorem sGlobal19_hz54 : B (572880598772355821 / 1000000000000000000) (572880598773117009 / 1000000000000000000) (kappa ((89 / 200))) := by rw [kappa_eq]; exact sGlobal19_hz53

theorem sGlobal19_hz55 {c : ℝ} (hc : B (11 / 25) (89 / 200) c) : B (71206382010741321 / 125000000000000000) (572880598773117009 / 1000000000000000000) (kappa c) := bkappa (sGlobal19_hz38 hc) (by norm_num) (by norm_num) sGlobal19_hz46.1 sGlobal19_hz54.2

theorem sGlobal19_hz56 : B 24450 24450 ((2 : ℝ) * (12225 : ℝ)) := bmul (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal19_hz57 {c : ℝ} (hc : B (11 / 25) (89 / 200) c) : B (427119401226882991 / 1000000000000000000) (53793617989258679 / 125000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (sGlobal19_hz55 hc) (by norm_num) (by norm_num)

theorem sGlobal19_hz58 {c : ℝ} (hc : B (11 / 25) (89 / 200) c) : B (208861387199945782599 / 20000000000000000) (26305079196747494031 / 2500000000000000) (((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) := bmul sGlobal19_hz56 (sGlobal19_hz57 hc) (by norm_num) (by norm_num)

theorem sGlobal19_hz59 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (4 : ℝ)) sGlobal19_hz10 (by norm_num) (by norm_num)

theorem sGlobal19_hz60 {c : ℝ} (hc : B (11 / 25) (89 / 200) c) : B (1044306870560056111359 / 100000000000000000) (2630507756075567399011 / 250000000000000000) ((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bsub (sGlobal19_hz58 hc) sGlobal19_hz59 (by norm_num) (by norm_num)

theorem sGlobal19_hz61 {c : ℝ} (hc : B (11 / 25) (89 / 200) c) : B (51095666904348555321 / 500000000000000000) (1602764870635286381 / 15625000000000000) (√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) := bsqrt (sGlobal19_hz60 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal19_hz62 : B (30670756373515103 / 125000000000000000) (122683025494060423 / 500000000000000000) ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal19_hz7 (by norm_num) (by norm_num)

theorem sGlobal19_hz63 {c : ℝ} (hc : B (11 / 25) (89 / 200) c) : B (25486491939427247449 / 250000000000000000) (2558289641741755189 / 25000000000000000) ((√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) - ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))))) := bsub (sGlobal19_hz61 hc) sGlobal19_hz62 (by norm_num) (by norm_num)

theorem sGlobal19_hz64 {c : ℝ} (hc : B (11 / 25) (89 / 200) c) : B (25486491939427247449 / 250000000000000000) (2558289641741755189 / 25000000000000000) (s3dm 12225 46 c) := by
    convert (sGlobal19_hz63 hc) using 1 <;>
      norm_num [s3dm, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal19_hz65 : B (6126072185528622723889 / 500000000000000000) (2450428874211449090087 / 200000000000000000) ((s3ap 12225 46)^2) := bsq sGlobal19_hz9 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal19_hz66 : B (6126072185528622723889 / 250000000000000000) (2450428874211449090087 / 100000000000000000) ((2 : ℝ) * ((s3ap 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal19_hz65 (by norm_num) (by norm_num)

theorem sGlobal19_hz67 {c : ℝ} (hc : B (11 / 25) (89 / 200) c) : B (2078596068411168182563 / 200000000000000000) (5235876712834526491123 / 500000000000000000) ((s3dm 12225 46 c)^2) := bsq (sGlobal19_hz64 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal19_hz68 {c : ℝ} (hc : B (11 / 25) (89 / 200) c) : B (1403253531644543791331 / 100000000000000000) (2822261680011729997611 / 200000000000000000) (((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) := bsub sGlobal19_hz66 (sGlobal19_hz67 hc) (by norm_num) (by norm_num)

theorem sGlobal19_hz69 : B (1524735695971823534271 / 125000000000000000) (609894278388729413841 / 50000000000000000) ((s3am 12225 46)^2) := bsq sGlobal19_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal19_hz70 : B (1524735695971823534271 / 62500000000000000) (609894278388729413841 / 25000000000000000) ((2 : ℝ) * ((s3am 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal19_hz69 (by norm_num) (by norm_num)

theorem sGlobal19_hz71 {c : ℝ} (hc : B (11 / 25) (89 / 200) c) : B (287601798657584217 / 500000000000000000) (578432562006447451 / 1000000000000000000) ((((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) / ((2 : ℝ) * ((s3am 12225 46)^2))) := bdiv (sGlobal19_hz68 hc) sGlobal19_hz70 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal19_hz72 {c : ℝ} (hc : B (11 / 25) (89 / 200) c) : B (287601798657584217 / 500000000000000000) (578432562006447451 / 1000000000000000000) (s3c1 12225 46 c) := by
    convert (sGlobal19_hz71 hc) using 1 <;>
      norm_num [s3c1] <;> ring

theorem sGlobal19_hz73 {c : ℝ} (hc : B (11 / 25) (89 / 200) c) : B (322510780936897579 / 500000000000000000) (323398163239342143 / 500000000000000000) (kdot c) := bkdot (sGlobal19_hz38 hc) sGlobal19_hz39.1 sGlobal19_hz47.2

theorem sGlobal19_hz74 : B (695077174922536973 / 1000000000000000000) (695077174922537271 / 1000000000000000000) (kdot ((287601798657584217 / 500000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (259652239082943731 / 500000000000000000)) (a := (47897165358760171 / 100000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (519304478165887461 / 1000000000000000000)) (a := (119742913396900311 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal19_hz75 : B (696335404184404909 / 1000000000000000000) (87041925523050643 / 125000000000000000) (kdot ((578432562006447451 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (258398815065579129 / 500000000000000000)) (a := (476995231684793703 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (516797630131158257 / 1000000000000000000)) (a := (95399046336958667 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal19_hz76 {c : ℝ} (hc : B (11 / 25) (89 / 200) c) : B (695077174922536973 / 1000000000000000000) (87041925523050643 / 125000000000000000) (kdot (s3c1 12225 46 c)) := bkdot (sGlobal19_hz72 hc) sGlobal19_hz74.1 sGlobal19_hz75.2

theorem sGlobal19_hz77 {c : ℝ} (hc : B (11 / 25) (89 / 200) c) : B (121 / 625) (7921 / 40000) (c^2) := bsq (sGlobal19_hz38 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal19_hz78 {c : ℝ} (hc : B (11 / 25) (89 / 200) c) : B (32079 / 40000) (504 / 625) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (sGlobal19_hz77 hc) (by norm_num) (by norm_num)

theorem sGlobal19_hz79 {c : ℝ} (hc : B (11 / 25) (89 / 200) c) : B (447765284496241401 / 500000000000000000) (897997772825745933 / 1000000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (sGlobal19_hz78 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal19_hz80 : B (39119999999999765769 / 1600000000000000) (3912000000000000489 / 160000000000000) ((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (149450625 : ℝ)) sGlobal19_hz10 (by norm_num) (by norm_num)

theorem sGlobal19_hz81 {c : ℝ} (hc : B (11 / 25) (89 / 200) c) : B (577636526317259729 / 1000000000000000000) (580821660649732531 / 1000000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (sGlobal19_hz79 hc) (sGlobal19_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal19_hz82 {c : ℝ} (hc : B (11 / 25) (89 / 200) c) : B (14123213068456915811311 / 1000000000000000000) (14201089602885962158087 / 1000000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) := bmul sGlobal19_hz80 (sGlobal19_hz81 hc) (by norm_num) (by norm_num)

theorem sGlobal19_hz83 {c : ℝ} (hc : B (11 / 25) (89 / 200) c) : B (1412321306845691581131 / 200000000000000000) (1775136200360745269761 / 250000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) / (2 : ℝ)) := bdiv (sGlobal19_hz82 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal19_hz84 {c : ℝ} (hc : B (11 / 25) (89 / 200) c) : B (1412321306845691581131 / 200000000000000000) (1775136200360745269761 / 250000000000000000) (s3Cpa 12225 c) := by
    convert (sGlobal19_hz83 hc) using 1 <;>
      norm_num [s3Cpa, mA] <;> ring

theorem sGlobal19_hz85 {c : ℝ} (hc : B (11 / 25) (89 / 200) c) : B (114022493396041 / 400000000000000) (2858415688614607 / 10000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (sGlobal19_hz79 hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal19_hz86 {c : ℝ} (hc : B (11 / 25) (89 / 200) c) : B (283809487224469869 / 1000000000000000000) (71956091320753627 / 250000000000000000) (c * (kdot c)) := bmul (sGlobal19_hz38 hc) (sGlobal19_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal19_hz87 {c : ℝ} (hc : B (11 / 25) (89 / 200) c) : B (-346016474114001 / 125000000000000000) (2032081636990831 / 1000000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (sGlobal19_hz85 hc) (sGlobal19_hz86 hc) (by norm_num) (by norm_num)

theorem sGlobal19_hz88 {c : ℝ} (hc : B (11 / 25) (89 / 200) c) : B (-67680822336698604061 / 1000000000000000000) (49684396024425824161 / 1000000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) := bmul sGlobal19_hz80 (sGlobal19_hz87 hc) (by norm_num) (by norm_num)

theorem sGlobal19_hz89 {c : ℝ} (hc : B (11 / 25) (89 / 200) c) : B (-33840411168349302031 / 1000000000000000000) (24842198012212912081 / 1000000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) / (2 : ℝ)) := bdiv (sGlobal19_hz88 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal19_hz90 {c : ℝ} (hc : B (11 / 25) (89 / 200) c) : B (-33840411168349302031 / 1000000000000000000) (24842198012212912081 / 1000000000000000000) (s3Cpp 12225 c) := by
    convert (sGlobal19_hz89 hc) using 1 <;>
      norm_num [s3Cpp, mA] <;> ring

theorem sGlobal19_hz91 {c : ℝ} (hc : B (11 / 25) (89 / 200) c) : B (897093955520274451757 / 125000000000000000) (721568991137671949127 / 100000000000000000) ((s3Cpa 12225 c) + (s3r1 12225 46)) := badd (sGlobal19_hz84 hc) sGlobal19_hz33 (by norm_num) (by norm_num)

theorem sGlobal19_hz92 {c : ℝ} (hc : B (11 / 25) (89 / 200) c) : B (12996177544639894799 / 200000000000000000) (65333448783614752229 / 1000000000000000000) (((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) := bdiv (sGlobal19_hz91 hc) sGlobal19_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal19_hz93 {c : ℝ} (hc : B (11 / 25) (89 / 200) c) : B (65103570748693534407 / 1000000000000000000) (16364032952277203163 / 250000000000000000) ((((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) + (s3e0 12225 46)) := badd (sGlobal19_hz92 hc) sGlobal19_hz16 (by norm_num) (by norm_num)

theorem sGlobal19_hz94 {c : ℝ} (hc : B (11 / 25) (89 / 200) c) : B (65103570748693534407 / 1000000000000000000) (16364032952277203163 / 250000000000000000) (s3Lam 12225 46 c) := by
    convert (sGlobal19_hz93 hc) using 1 <;>
      norm_num [s3Lam] <;> ring

theorem sGlobal19_hz95 {c : ℝ} (hc : B (11 / 25) (89 / 200) c) : B (42922995454142503569 / 1000000000000000000) (101605604634705186899 / 1000000000000000000) ((s3Cpp 12225 c) + (s3rpp 12225 46)) := badd (sGlobal19_hz90 hc) sGlobal19_hz37 (by norm_num) (by norm_num)

theorem sGlobal19_hz96 {c : ℝ} (hc : B (11 / 25) (89 / 200) c) : B (2682687215883906473 / 125000000000000000) (14150315954141660979 / 200000000000000000) (if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) := bweaken (bfirst (sGlobal19_hz95 hc) (sGlobal19_hz76 hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem sGlobal19_hz97 {c : ℝ} (hc : B (11 / 25) (89 / 200) c) : B (4238474924230144412169 / 1000000000000000000) (856901038282285304613 / 200000000000000000) ((s3Lam 12225 46 c)^2) := bsq (sGlobal19_hz94 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal19_hz98 {c : ℝ} (hc : B (11 / 25) (89 / 200) c) : B (165429589182155221 / 500000000000000000) (83646057197335669 / 250000000000000000) ((s3c1 12225 46 c)^2) := bsq (sGlobal19_hz72 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal19_hz99 {c : ℝ} (hc : B (11 / 25) (89 / 200) c) : B (166353942802664331 / 250000000000000000) (334570410817844779 / 500000000000000000) ((1 : ℝ) - ((s3c1 12225 46 c)^2)) := bsub (bpoint (1 : ℝ)) (sGlobal19_hz98 hc) (by norm_num) (by norm_num)

theorem sGlobal19_hz100 {c : ℝ} (hc : B (11 / 25) (89 / 200) c) : B (16314604147335691 / 20000000000000000) (12781410657949723 / 15625000000000000) (√((1 : ℝ) - ((s3c1 12225 46 c)^2))) := bsqrt (sGlobal19_hz99 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal19_hz101 {c : ℝ} (hc : B (11 / 25) (89 / 200) c) : B (2562692026774768979 / 1000000000000000000) (1284927546416932333 / 500000000000000000) (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))) := bmul pi_mem (sGlobal19_hz100 hc) (by norm_num) (by norm_num)

theorem sGlobal19_hz102 {c : ℝ} (hc : B (11 / 25) (89 / 200) c) : B (1649305027372666826767 / 1000000000000000000) (1671876740024674462457 / 1000000000000000000) (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2))))) := bdiv (sGlobal19_hz97 hc) (sGlobal19_hz101 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal19_hz103 {c : ℝ} (hc : B (11 / 25) (89 / 200) c) : B (1670766525099738078551 / 1000000000000000000) (217828539974422845919 / 125000000000000000) ((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) := badd (sGlobal19_hz96 hc) (sGlobal19_hz102 hc) (by norm_num) (by norm_num)

theorem sGlobal19_hz104 : B (3762781186094069 / 250000000000000000) (376278118609407 / 25000000000000000) ((s3e0 12225 46)^2) := bsq sGlobal19_hz16 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal19_hz105 {c : ℝ} (hc : B (11 / 25) (89 / 200) c) : B (1670781576224482454827 / 1000000000000000000) (108915210682507946477 / 62500000000000000) (((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) := badd (sGlobal19_hz103 hc) sGlobal19_hz104 (by norm_num) (by norm_num)

theorem sGlobal19_hz106 {c : ℝ} (hc : B (11 / 25) (89 / 200) c) : B (854639324837864862479 / 500000000000000000) (111321277773390713353 / 62500000000000000) ((((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) + (s3rs 12225 46 maskSlack)) := badd (sGlobal19_hz105 hc) sGlobal19_hz29 (by norm_num) (by norm_num)

theorem sGlobal19_hz107 {c : ℝ} (hc : B (11 / 25) (89 / 200) c) : B (854639324837864862479 / 500000000000000000) (111321277773390713353 / 62500000000000000) (s3U 12225 46 maskSlack c) := by
    convert (sGlobal19_hz106 hc) using 1 <;>
      norm_num [s3U] <;> ring

theorem sGlobal19_hz108 {c : ℝ} (hc : B (11 / 25) (89 / 200) c) : B (-110603817790841576849 / 1000000000000000000) (-51921208610278893519 / 1000000000000000000) ((s3Cpp 12225 c) - (s3rpp 12225 46)) := bsub (sGlobal19_hz90 hc) sGlobal19_hz37 (by norm_num) (by norm_num)

theorem sGlobal19_hz109 {c : ℝ} (hc : B (11 / 25) (89 / 200) c) : B (-110603817790841576849 / 1000000000000000000) (-51921208610278893519 / 1000000000000000000) (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ)) := bweaken (bmin (sGlobal19_hz108 hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem sGlobal19_hz110 {c : ℝ} (hc : B (11 / 25) (89 / 200) c) : B (-38508677082861984931 / 500000000000000000) (-9022311749849088821 / 250000000000000000) ((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) := bmul (sGlobal19_hz76 hc) (sGlobal19_hz109 hc) (by norm_num) (by norm_num)

theorem sGlobal19_hz111 {c : ℝ} (hc : B (11 / 25) (89 / 200) c) : B (-38516202645234173071 / 500000000000000000) (-902607453103518289 / 25000000000000000) (((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) := bsub (sGlobal19_hz110 hc) sGlobal19_hz104 (by norm_num) (by norm_num)

theorem sGlobal19_hz112 {c : ℝ} (hc : B (11 / 25) (89 / 200) c) : B (-57764739372296308079 / 500000000000000000) (-74601371575388001691 / 1000000000000000000) ((((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) - (s3rs 12225 46 maskSlack)) := bsub (sGlobal19_hz111 hc) sGlobal19_hz29 (by norm_num) (by norm_num)

theorem sGlobal19_hz113 {c : ℝ} (hc : B (11 / 25) (89 / 200) c) : B (-57764739372296308079 / 500000000000000000) (-74601371575388001691 / 1000000000000000000) (s3L 12225 46 maskSlack c) := by
    convert (sGlobal19_hz112 hc) using 1 <;>
      norm_num [s3L] <;> ring

theorem sGlobal19_hz114 {c : ℝ} (hc : B (11 / 25) (89 / 200) c) : B 0 (111321277773390713353 / 62500000000000000) |(s3U 12225 46 maskSlack c)| := bweaken (babs (sGlobal19_hz107 hc)) (by norm_num) (by norm_num)

theorem sGlobal19_hz115 {c : ℝ} (hc : B (11 / 25) (89 / 200) c) : B 0 (57764739372296308079 / 500000000000000000) |(s3L 12225 46 maskSlack c)| := bweaken (babs (sGlobal19_hz113 hc)) (by norm_num) (by norm_num)

theorem sGlobal19_hz116 {c : ℝ} (hc : B (11 / 25) (89 / 200) c) : B 0 (111321277773390713353 / 62500000000000000) (max |(s3U 12225 46 maskSlack c)| |(s3L 12225 46 maskSlack c)|) := bweaken (bmax (sGlobal19_hz114 hc) (sGlobal19_hz115 hc)) (by norm_num) (by norm_num)

theorem sGlobal19_hz117 {c : ℝ} (hc : B (11 / 25) (89 / 200) c) : B 0 (111321277773390713353 / 62500000000000000) (s3nks 12225 46 maskSlack c) := by
    convert (sGlobal19_hz116 hc) using 1 <;>
      norm_num [s3nks] <;> ring

theorem sGlobal19 {c : ℝ} (hc : B (11 / 25) (89 / 200) c) :
    0 < s3am 12225 46 ∧ 0 ≤ s3dm 12225 46 c ∧
    s3dm 12225 46 c ^ 2 ≤ 2 * s3ap 12225 46 ^ 2 ∧ s3c1 12225 46 c < 1 ∧
    0 ≤ s3Cpa 12225 c - s3r1 12225 46 ∧
    s3e0 12225 46 ≤ (s3Cpa 12225 c - s3r1 12225 46) / s3ap 12225 46 ∧
    s3nks 12225 46 maskSlack c ≤ 12225 * (145697 / 1000000) := by

  refine ⟨lt_of_lt_of_le (by norm_num) sGlobal19_hz14.1,
    le_trans (by norm_num) (sGlobal19_hz64 hc).1, ?_,
    lt_of_le_of_lt (sGlobal19_hz72 hc).2 (by norm_num), ?_, ?_,
    le_trans (sGlobal19_hz117 hc).2 (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (sGlobal19_hz64 hc).1) (sGlobal19_hz64 hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) sGlobal19_hz9.1 2
    nlinarith only [h1, h2]
  · linarith only [(sGlobal19_hz84 hc).1, sGlobal19_hz33.2]
  · have hap : 0 < s3ap 12225 46 := lt_of_lt_of_le (by norm_num) sGlobal19_hz9.1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul sGlobal19_hz16.2 sGlobal19_hz9.2 (le_trans (by norm_num) sGlobal19_hz9.1) (by norm_num)
    linarith only [h, (sGlobal19_hz84 hc).1, sGlobal19_hz33.2]

end BstLean.Part255
