import BstLean.Part255SGlobal16
import BstLean.Part255Numeric10
namespace BstLean.Part255
open Real BstLean.Part130 BstLean.Part182 BstLean.Part197 BstLean.Part246
theorem sGlobal20_hz0 : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal20_hz1 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) ((√(23 : ℝ)) / (12225 : ℝ)) := bdiv sGlobal20_hz0 (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal20_hz2 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) maskSlack := by
    convert sGlobal20_hz1 using 1 <;>
      norm_num [maskSlack] <;> ring

theorem sGlobal20_hz3 : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal20_hz4 : B (6395294793910793 / 500000000000000000) (12790589587821587 / 1000000000000000000) (√((2 / 12225) : ℝ)) := bsqrt (bpoint ((2 / 12225) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal20_hz5 : B (7230130686979 / 62500000000000000) (23136418198333 / 200000000000000000) (√((2 / 149450625) : ℝ)) := bsqrt (bpoint ((2 / 149450625) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal20_hz6 : B (2211334438749598093 / 20000000000000000) (110566721937479904651 / 1000000000000000000) (√(12225 : ℝ)) := bsqrt (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal20_hz7 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))) := bmul sGlobal20_hz3 sGlobal20_hz4 (by norm_num) (by norm_num)

theorem sGlobal20_hz8 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) ((√(12225 : ℝ)) + ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := badd sGlobal20_hz6 sGlobal20_hz7 (by norm_num) (by norm_num)

theorem sGlobal20_hz9 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) (s3ap 12225 46) := by
    convert sGlobal20_hz8 using 1 <;>
      norm_num [s3ap, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal20_hz10 : B (163599182004089 / 1000000000000000000) (16359918200409 / 100000000000000000) ((2 : ℝ) / (12225 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal20_hz11 : B (1222499983640081799591 / 100000000000000000) (12224999836400817995911 / 1000000000000000000) ((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ))) := bsub (bpoint (12225 : ℝ)) sGlobal20_hz10 (by norm_num) (by norm_num)

theorem sGlobal20_hz12 : B (110566721197658827907 / 1000000000000000000) (27641680299414706977 / 250000000000000000) (√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) := bsqrt sGlobal20_hz11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal20_hz13 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) ((√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) - ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bsub sGlobal20_hz12 sGlobal20_hz7 (by norm_num) (by norm_num)

theorem sGlobal20_hz14 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) (s3am 12225 46) := by
    convert sGlobal20_hz13 using 1 <;>
      norm_num [s3am, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal20_hz15 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√((2 / 12225) : ℝ)) * (√(92 : ℝ))) := bmul sGlobal20_hz4 sGlobal20_hz3 (by norm_num) (by norm_num)

theorem sGlobal20_hz16 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) (s3e0 12225 46) := by
    convert sGlobal20_hz15 using 1 <;>
      norm_num [s3e0, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal20_hz17 : B (250196148528560847 / 500000000000000000) (100078459411424339 / 200000000000000000) (((1 / 2) : ℝ) + maskSlack) := badd (bpoint ((1 / 2) : ℝ)) sGlobal20_hz2 (by norm_num) (by norm_num)

theorem sGlobal20_hz18 : B (59827153232297998295487 / 800000000000000) (23930861292919199366019 / 320000000000000) ((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack)) := bmul (bpoint (149450625 : ℝ)) sGlobal20_hz17 (by norm_num) (by norm_num)

theorem sGlobal20_hz19 : B (1729554180017180009583 / 200000000000000000) (8647770900085900056557 / 1000000000000000000) (√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) := bsqrt sGlobal20_hz18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal20_hz20 : B (4328681281566262743499 / 500000000000000000) (8657362563132525495641 / 1000000000000000000) ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))) := badd sGlobal20_hz19 sGlobal20_hz3 (by norm_num) (by norm_num)

theorem sGlobal20_hz21 : B (110732771457999278473 / 1000000000000000000) (55366385728999643621 / 500000000000000000) ((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ)))) := bmul sGlobal20_hz4 sGlobal20_hz20 (by norm_num) (by norm_num)

theorem sGlobal20_hz22 : B (209099159 / 15625000000000000) (13382346177 / 1000000000000000000) ((2 : ℝ) / (149450625 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (149450625 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal20_hz23 : B (2452349334953899930479 / 200000000000000000) (12261746674769501594427 / 1000000000000000000) (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2) := bsq sGlobal20_hz21 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal20_hz24 : B (82045469362091 / 500000000000000000) (32818187747289 / 200000000000000000) (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2)) := bmul sGlobal20_hz22 sGlobal20_hz23 (by norm_num) (by norm_num)

theorem sGlobal20_hz25 : B (82045469362091 / 250000000000000000) (32818187747289 / 100000000000000000) ((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) := bmul (bpoint (2 : ℝ)) sGlobal20_hz24 (by norm_num) (by norm_num)

theorem sGlobal20_hz26 : B (117258080744995992792057 / 1000000000000000000) (58629040372497996396029 / 500000000000000000) (√(13749457500 : ℝ)) := bsqrt (bpoint (13749457500 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal20_hz27 : B (117304080744995992792057 / 1000000000000000000) (58652040372497996396029 / 500000000000000000) ((√(13749457500 : ℝ)) + (46 : ℝ)) := badd sGlobal20_hz26 (bpoint (46 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal20_hz28 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal20_hz25 sGlobal20_hz27 (by norm_num) (by norm_num)

theorem sGlobal20_hz29 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (s3rs 12225 46 maskSlack) := by
    convert sGlobal20_hz28 using 1 <;>
      norm_num [s3rs, s3pp, s3K, mA, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal20_hz30 : B (490797546012267 / 1000000000000000000) (49079754601227 / 100000000000000000) ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (3 : ℝ)) sGlobal20_hz10 (by norm_num) (by norm_num)

theorem sGlobal20_hz31 : B (490797546012267 / 500000000000000000) (49079754601227 / 50000000000000000) ((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal20_hz30 (by norm_num) (by norm_num)

theorem sGlobal20_hz32 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal20_hz31 sGlobal20_hz27 (by norm_num) (by norm_num)

theorem sGlobal20_hz33 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (s3r1 12225 46) := by
    convert sGlobal20_hz32 using 1 <;>
      norm_num [s3r1, mA] <;> ring

theorem sGlobal20_hz34 : B (163599182004089 / 500000000000000000) (16359918200409 / 50000000000000000) ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (2 : ℝ)) sGlobal20_hz10 (by norm_num) (by norm_num)

theorem sGlobal20_hz35 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal20_hz34 (by norm_num) (by norm_num)

theorem sGlobal20_hz36 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal20_hz35 sGlobal20_hz27 (by norm_num) (by norm_num)

theorem sGlobal20_hz37 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (s3rpp 12225 46) := by
    convert sGlobal20_hz36 using 1 <;>
      norm_num [s3rpp, mA] <;> ring

theorem sGlobal20_hz38 {c : ℝ} (hc : B (89 / 200) (9 / 20) c) : B (89 / 200) (9 / 20) c := hc

theorem sGlobal20_hz39 : B (646796326476973757 / 1000000000000000000) (323398163239342143 / 500000000000000000) (kdot ((89 / 200))) := by
    constructor
    · apply bkdot_lower (q := (309872169201551143 / 500000000000000000)) (a := (17337844780638547 / 31250000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (123948867680620457 / 200000000000000000)) (a := (554811032977746613 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal20_hz40 : B (7921 / 40000) (7921 / 40000) (((89 / 200) : ℝ)^2) := bsq (bpoint ((89 / 200) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal20_hz41 : B (32079 / 40000) (32079 / 40000) ((1 : ℝ) - (((89 / 200) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal20_hz40 (by norm_num) (by norm_num)

theorem sGlobal20_hz42 : B (447765284496241401 / 500000000000000000) (895530568992482803 / 1000000000000000000) (√((1 : ℝ) - (((89 / 200) : ℝ)^2))) := bsqrt sGlobal20_hz41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal20_hz43 : B (114022493396041 / 400000000000000) (285056233490102501 / 1000000000000000000) ((√((1 : ℝ) - (((89 / 200) : ℝ)^2))) / Real.pi) := bdiv sGlobal20_hz42 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal20_hz44 : B (287824365282253321 / 1000000000000000000) (71956091320753627 / 250000000000000000) (((89 / 200) : ℝ) * (kdot ((89 / 200)))) := bmul (bpoint ((89 / 200) : ℝ)) sGlobal20_hz39 (by norm_num) (by norm_num)

theorem sGlobal20_hz45 : B (572880598772355821 / 1000000000000000000) (572880598773117009 / 1000000000000000000) (((√((1 : ℝ) - (((89 / 200) : ℝ)^2))) / Real.pi) + (((89 / 200) : ℝ) * (kdot ((89 / 200))))) := badd sGlobal20_hz43 sGlobal20_hz44 (by norm_num) (by norm_num)

theorem sGlobal20_hz46 : B (572880598772355821 / 1000000000000000000) (572880598773117009 / 1000000000000000000) (kappa ((89 / 200))) := by rw [kappa_eq]; exact sGlobal20_hz45

theorem sGlobal20_hz47 : B (32428801097325763 / 50000000000000000) (64857602194777443 / 100000000000000000) (kdot ((9 / 20))) := by
    constructor
    · apply bkdot_lower (q := (307940881025719857 / 500000000000000000)) (a := (552015493874064193 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (615881762051439713 / 1000000000000000000)) (a := (276007746936043147 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal20_hz48 : B (81 / 400) (81 / 400) (((9 / 20) : ℝ)^2) := bsq (bpoint ((9 / 20) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal20_hz49 : B (319 / 400) (319 / 400) ((1 : ℝ) - (((9 / 20) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal20_hz48 (by norm_num) (by norm_num)

theorem sGlobal20_hz50 : B (13953571171477931 / 15625000000000000) (178605710994917517 / 200000000000000000) (√((1 : ℝ) - (((9 / 20) : ℝ)^2))) := bsqrt sGlobal20_hz49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal20_hz51 : B (35532477211604503 / 125000000000000000) (11370392707713441 / 40000000000000000) ((√((1 : ℝ) - (((9 / 20) : ℝ)^2))) / Real.pi) := bdiv sGlobal20_hz50 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal20_hz52 : B (291859209875931867 / 1000000000000000000) (145929604938249247 / 500000000000000000) (((9 / 20) : ℝ) * (kdot ((9 / 20)))) := bmul (bpoint ((9 / 20) : ℝ)) sGlobal20_hz47 (by norm_num) (by norm_num)

theorem sGlobal20_hz53 : B (576119027568767891 / 1000000000000000000) (576119027569334519 / 1000000000000000000) (((√((1 : ℝ) - (((9 / 20) : ℝ)^2))) / Real.pi) + (((9 / 20) : ℝ) * (kdot ((9 / 20))))) := badd sGlobal20_hz51 sGlobal20_hz52 (by norm_num) (by norm_num)

theorem sGlobal20_hz54 : B (576119027568767891 / 1000000000000000000) (576119027569334519 / 1000000000000000000) (kappa ((9 / 20))) := by rw [kappa_eq]; exact sGlobal20_hz53

theorem sGlobal20_hz55 {c : ℝ} (hc : B (89 / 200) (9 / 20) c) : B (572880598772355821 / 1000000000000000000) (576119027569334519 / 1000000000000000000) (kappa c) := bkappa (sGlobal20_hz38 hc) (by norm_num) (by norm_num) sGlobal20_hz46.1 sGlobal20_hz54.2

theorem sGlobal20_hz56 : B 24450 24450 ((2 : ℝ) * (12225 : ℝ)) := bmul (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal20_hz57 {c : ℝ} (hc : B (89 / 200) (9 / 20) c) : B (423880972430665481 / 1000000000000000000) (427119401227644179 / 1000000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (sGlobal20_hz55 hc) (by norm_num) (by norm_num)

theorem sGlobal20_hz58 {c : ℝ} (hc : B (89 / 200) (9 / 20) c) : B (207277795518595420209 / 20000000000000000) (208861387200318003531 / 20000000000000000) (((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) := bmul sGlobal20_hz56 (sGlobal20_hz57 hc) (by norm_num) (by norm_num)

theorem sGlobal20_hz59 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (4 : ℝ)) sGlobal20_hz10 (by norm_num) (by norm_num)

theorem sGlobal20_hz60 {c : ℝ} (hc : B (89 / 200) (9 / 20) c) : B (1036388912153304299409 / 100000000000000000) (5221534352809586080097 / 500000000000000000) ((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bsub (sGlobal20_hz58 hc) sGlobal20_hz59 (by norm_num) (by norm_num)

theorem sGlobal20_hz61 {c : ℝ} (hc : B (89 / 200) (9 / 20) c) : B (795337407576460293 / 7812500000000000) (25547833452197042613 / 250000000000000000) (√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) := bsqrt (sGlobal20_hz60 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal20_hz62 : B (30670756373515103 / 125000000000000000) (122683025494060423 / 500000000000000000) ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal20_hz7 (by norm_num) (by norm_num)

theorem sGlobal20_hz63 {c : ℝ} (hc : B (89 / 200) (9 / 20) c) : B (50778911059399398329 / 500000000000000000) (25486491939450012407 / 250000000000000000) ((√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) - ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))))) := bsub (sGlobal20_hz61 hc) sGlobal20_hz62 (by norm_num) (by norm_num)

theorem sGlobal20_hz64 {c : ℝ} (hc : B (89 / 200) (9 / 20) c) : B (50778911059399398329 / 500000000000000000) (25486491939450012407 / 250000000000000000) (s3dm 12225 46 c) := by
    convert (sGlobal20_hz63 hc) using 1 <;>
      norm_num [s3dm, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal20_hz65 : B (6126072185528622723889 / 500000000000000000) (2450428874211449090087 / 200000000000000000) ((s3ap 12225 46)^2) := bsq sGlobal20_hz9 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal20_hz66 : B (6126072185528622723889 / 250000000000000000) (2450428874211449090087 / 100000000000000000) ((2 : ℝ) * ((s3ap 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal20_hz65 (by norm_num) (by norm_num)

theorem sGlobal20_hz67 {c : ℝ} (hc : B (89 / 200) (9 / 20) c) : B (10313991233513578103727 / 1000000000000000000) (1039298034207440727821 / 100000000000000000) ((s3dm 12225 46 c)^2) := bsq (sGlobal20_hz64 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal20_hz68 {c : ℝ} (hc : B (89 / 200) (9 / 20) c) : B (7055654200020041808673 / 500000000000000000) (14190297508600912797143 / 1000000000000000000) (((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) := bsub sGlobal20_hz66 (sGlobal20_hz67 hc) (by norm_num) (by norm_num)

theorem sGlobal20_hz69 : B (1524735695971823534271 / 125000000000000000) (609894278388729413841 / 50000000000000000) ((s3am 12225 46)^2) := bsq sGlobal20_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal20_hz70 : B (1524735695971823534271 / 62500000000000000) (609894278388729413841 / 25000000000000000) ((2 : ℝ) * ((s3am 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal20_hz69 (by norm_num) (by norm_num)

theorem sGlobal20_hz71 {c : ℝ} (hc : B (89 / 200) (9 / 20) c) : B (578432562005686401 / 1000000000000000000) (581670381713124441 / 1000000000000000000) ((((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) / ((2 : ℝ) * ((s3am 12225 46)^2))) := bdiv (sGlobal20_hz68 hc) sGlobal20_hz70 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal20_hz72 {c : ℝ} (hc : B (89 / 200) (9 / 20) c) : B (578432562005686401 / 1000000000000000000) (581670381713124441 / 1000000000000000000) (s3c1 12225 46 c) := by
    convert (sGlobal20_hz71 hc) using 1 <;>
      norm_num [s3c1] <;> ring

theorem sGlobal20_hz73 {c : ℝ} (hc : B (89 / 200) (9 / 20) c) : B (646796326476973757 / 1000000000000000000) (64857602194777443 / 100000000000000000) (kdot c) := bkdot (sGlobal20_hz38 hc) sGlobal20_hz39.1 sGlobal20_hz47.2

theorem sGlobal20_hz74 : B (21760481380753373 / 31250000000000000) (696335404184108171 / 1000000000000000000) (kdot ((578432562005686401 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (51679763013174933 / 100000000000000000)) (a := (238497615842630093 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (516797630131749329 / 1000000000000000000)) (a := (476995231685259819 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal20_hz75 : B (697600635291614611 / 1000000000000000000) (697600635291614797 / 1000000000000000000) (kdot ((581670381713124441 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (514281990424473507 / 1000000000000000000)) (a := (237503905654521031 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (257140995212236753 / 500000000000000000)) (a := (118751952827260443 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal20_hz76 {c : ℝ} (hc : B (89 / 200) (9 / 20) c) : B (21760481380753373 / 31250000000000000) (697600635291614797 / 1000000000000000000) (kdot (s3c1 12225 46 c)) := bkdot (sGlobal20_hz72 hc) sGlobal20_hz74.1 sGlobal20_hz75.2

theorem sGlobal20_hz77 {c : ℝ} (hc : B (89 / 200) (9 / 20) c) : B (7921 / 40000) (81 / 400) (c^2) := bsq (sGlobal20_hz38 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal20_hz78 {c : ℝ} (hc : B (89 / 200) (9 / 20) c) : B (319 / 400) (32079 / 40000) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (sGlobal20_hz77 hc) (by norm_num) (by norm_num)

theorem sGlobal20_hz79 {c : ℝ} (hc : B (89 / 200) (9 / 20) c) : B (13953571171477931 / 15625000000000000) (895530568992482803 / 1000000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (sGlobal20_hz78 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal20_hz80 : B (39119999999999765769 / 1600000000000000) (3912000000000000489 / 160000000000000) ((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (149450625 : ℝ)) sGlobal20_hz10 (by norm_num) (by norm_num)

theorem sGlobal20_hz81 {c : ℝ} (hc : B (89 / 200) (9 / 20) c) : B (577607588796603457 / 1000000000000000000) (11616393079395429 / 20000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (sGlobal20_hz79 hc) (sGlobal20_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal20_hz82 {c : ℝ} (hc : B (89 / 200) (9 / 20) c) : B (3530626386519217491287 / 250000000000000000) (14201040539560913727631 / 1000000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) := bmul sGlobal20_hz80 (sGlobal20_hz81 hc) (by norm_num) (by norm_num)

theorem sGlobal20_hz83 {c : ℝ} (hc : B (89 / 200) (9 / 20) c) : B (3530626386519217491287 / 500000000000000000) (887565033722557107977 / 125000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) / (2 : ℝ)) := bdiv (sGlobal20_hz82 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal20_hz84 {c : ℝ} (hc : B (89 / 200) (9 / 20) c) : B (3530626386519217491287 / 500000000000000000) (887565033722557107977 / 125000000000000000) (s3Cpa 12225 c) := by
    convert (sGlobal20_hz83 hc) using 1 <;>
      norm_num [s3Cpa, mA] <;> ring

theorem sGlobal20_hz85 {c : ℝ} (hc : B (89 / 200) (9 / 20) c) : B (35532477211604503 / 125000000000000000) (285056233490102501 / 1000000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (sGlobal20_hz79 hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal20_hz86 {c : ℝ} (hc : B (89 / 200) (9 / 20) c) : B (287824365282253321 / 1000000000000000000) (145929604938249247 / 500000000000000000) (c * (kdot c)) := bmul (sGlobal20_hz38 hc) (sGlobal20_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal20_hz87 {c : ℝ} (hc : B (89 / 200) (9 / 20) c) : B (-759939218366247 / 100000000000000000) (-138406589607541 / 50000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (sGlobal20_hz85 hc) (sGlobal20_hz86 hc) (by norm_num) (by norm_num)

theorem sGlobal20_hz88 {c : ℝ} (hc : B (89 / 200) (9 / 20) c) : B (-92902569445273707363 / 500000000000000000) (-67680822318087143761 / 1000000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) := bmul sGlobal20_hz80 (sGlobal20_hz87 hc) (by norm_num) (by norm_num)

theorem sGlobal20_hz89 {c : ℝ} (hc : B (89 / 200) (9 / 20) c) : B (-92902569445273707363 / 1000000000000000000) (-846010278976089297 / 25000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) / (2 : ℝ)) := bdiv (sGlobal20_hz88 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal20_hz90 {c : ℝ} (hc : B (89 / 200) (9 / 20) c) : B (-92902569445273707363 / 1000000000000000000) (-846010278976089297 / 25000000000000000) (s3Cpp 12225 c) := by
    convert (sGlobal20_hz89 hc) using 1 <;>
      norm_num [s3Cpp, mA] <;> ring

theorem sGlobal20_hz91 {c : ℝ} (hc : B (89 / 200) (9 / 20) c) : B (287055915318886907639 / 40000000000000000) (3607832689857097638021 / 500000000000000000) ((s3Cpa 12225 c) + (s3r1 12225 46)) := badd (sGlobal20_hz84 hc) sGlobal20_hz33 (by norm_num) (by norm_num)

theorem sGlobal20_hz92 {c : ℝ} (hc : B (89 / 200) (9 / 20) c) : B (12995536928458383099 / 200000000000000000) (16333306666282238563 / 250000000000000000) (((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) := bdiv (sGlobal20_hz91 hc) sGlobal20_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal20_hz93 {c : ℝ} (hc : B (89 / 200) (9 / 20) c) : B (65100367667785975907 / 1000000000000000000) (2618236387624920587 / 40000000000000000) ((((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) + (s3e0 12225 46)) := badd (sGlobal20_hz92 hc) sGlobal20_hz16 (by norm_num) (by norm_num)

theorem sGlobal20_hz94 {c : ℝ} (hc : B (89 / 200) (9 / 20) c) : B (65100367667785975907 / 1000000000000000000) (2618236387624920587 / 40000000000000000) (s3Lam 12225 46 c) := by
    convert (sGlobal20_hz93 hc) using 1 <;>
      norm_num [s3Lam] <;> ring

theorem sGlobal20_hz95 {c : ℝ} (hc : B (89 / 200) (9 / 20) c) : B (-16139162822781901763 / 1000000000000000000) (21461497731724351469 / 500000000000000000) ((s3Cpp 12225 c) + (s3rpp 12225 46)) := badd (sGlobal20_hz90 hc) sGlobal20_hz37 (by norm_num) (by norm_num)

theorem sGlobal20_hz96 {c : ℝ} (hc : B (89 / 200) (9 / 20) c) : B (-11258690238247465827 / 1000000000000000000) (29943108903920915069 / 1000000000000000000) (if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) := bweaken (bfirst (sGlobal20_hz95 hc) (sGlobal20_hz76 hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem sGlobal20_hz97 {c : ℝ} (hc : B (89 / 200) (9 / 20) c) : B (847611574096182732787 / 200000000000000000) (2142238056713497940353 / 500000000000000000) ((s3Lam 12225 46 c)^2) := bsq (sGlobal20_hz94 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal20_hz98 {c : ℝ} (hc : B (89 / 200) (9 / 20) c) : B (167292114394231121 / 500000000000000000) (338340432962291893 / 1000000000000000000) ((s3c1 12225 46 c)^2) := bsq (sGlobal20_hz72 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal20_hz99 {c : ℝ} (hc : B (89 / 200) (9 / 20) c) : B (661659567037708107 / 1000000000000000000) (332707885605768879 / 500000000000000000) ((1 : ℝ) - ((s3c1 12225 46 c)^2)) := bsub (bpoint (1 : ℝ)) (sGlobal20_hz98 hc) (by norm_num) (by norm_num)

theorem sGlobal20_hz100 {c : ℝ} (hc : B (89 / 200) (9 / 20) c) : B (813424592102862419 / 1000000000000000000) (815730207367324211 / 1000000000000000000) (√((1 : ℝ) - ((s3c1 12225 46 c)^2))) := bsqrt (sGlobal20_hz99 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal20_hz101 {c : ℝ} (hc : B (89 / 200) (9 / 20) c) : B (15971554517497667 / 6250000000000000) (4100307242842343 / 1600000000000000) (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))) := bmul pi_mem (sGlobal20_hz100 hc) (by norm_num) (by norm_num)

theorem sGlobal20_hz102 {c : ℝ} (hc : B (89 / 200) (9 / 20) c) : B (330750462888187400689 / 200000000000000000) (104787763769261086627 / 62500000000000000) (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2))))) := bdiv (sGlobal20_hz97 hc) (sGlobal20_hz101 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal20_hz103 {c : ℝ} (hc : B (89 / 200) (9 / 20) c) : B (821246812101344768809 / 500000000000000000) (1706547329212098301101 / 1000000000000000000) ((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) := badd (sGlobal20_hz96 hc) (sGlobal20_hz102 hc) (by norm_num) (by norm_num)

theorem sGlobal20_hz104 : B (3762781186094069 / 250000000000000000) (376278118609407 / 25000000000000000) ((s3e0 12225 46)^2) := bsq sGlobal20_hz16 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal20_hz105 {c : ℝ} (hc : B (89 / 200) (9 / 20) c) : B (821254337663716956947 / 500000000000000000) (1706562380336842677381 / 1000000000000000000) (((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) := badd (sGlobal20_hz103 hc) sGlobal20_hz104 (by norm_num) (by norm_num)

theorem sGlobal20_hz106 {c : ℝ} (hc : B (89 / 200) (9 / 20) c) : B (67240229951147247361 / 40000000000000000) (1745059453790966947397 / 1000000000000000000) ((((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) + (s3rs 12225 46 maskSlack)) := badd (sGlobal20_hz105 hc) sGlobal20_hz29 (by norm_num) (by norm_num)

theorem sGlobal20_hz107 {c : ℝ} (hc : B (89 / 200) (9 / 20) c) : B (67240229951147247361 / 40000000000000000) (1745059453790966947397 / 1000000000000000000) (s3U 12225 46 maskSlack c) := by
    convert (sGlobal20_hz106 hc) using 1 <;>
      norm_num [s3U] <;> ring

theorem sGlobal20_hz108 {c : ℝ} (hc : B (89 / 200) (9 / 20) c) : B (-169665976067765982181 / 1000000000000000000) (-2765095444538384437 / 25000000000000000) ((s3Cpp 12225 c) - (s3rpp 12225 46)) := bsub (sGlobal20_hz90 hc) sGlobal20_hz37 (by norm_num) (by norm_num)

theorem sGlobal20_hz109 {c : ℝ} (hc : B (89 / 200) (9 / 20) c) : B (-169665976067765982181 / 1000000000000000000) (-2765095444538384437 / 25000000000000000) (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ)) := bweaken (bmin (sGlobal20_hz108 hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem sGlobal20_hz110 {c : ℝ} (hc : B (89 / 200) (9 / 20) c) : B (-11835909269224546137 / 100000000000000000) (-77017354159210861423 / 1000000000000000000) ((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) := bmul (sGlobal20_hz76 hc) (sGlobal20_hz109 hc) (by norm_num) (by norm_num)

theorem sGlobal20_hz111 {c : ℝ} (hc : B (89 / 200) (9 / 20) c) : B (-2367482876339796753 / 20000000000000000) (-77032405283955237699 / 1000000000000000000) (((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) := bsub (sGlobal20_hz110 hc) sGlobal20_hz104 (by norm_num) (by norm_num)

theorem sGlobal20_hz112 {c : ℝ} (hc : B (89 / 200) (9 / 20) c) : B (-78435608635557053833 / 500000000000000000) (-11552947873520250783 / 100000000000000000) ((((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) - (s3rs 12225 46 maskSlack)) := bsub (sGlobal20_hz111 hc) sGlobal20_hz29 (by norm_num) (by norm_num)

theorem sGlobal20_hz113 {c : ℝ} (hc : B (89 / 200) (9 / 20) c) : B (-78435608635557053833 / 500000000000000000) (-11552947873520250783 / 100000000000000000) (s3L 12225 46 maskSlack c) := by
    convert (sGlobal20_hz112 hc) using 1 <;>
      norm_num [s3L] <;> ring

theorem sGlobal20_hz114 {c : ℝ} (hc : B (89 / 200) (9 / 20) c) : B 0 (1745059453790966947397 / 1000000000000000000) |(s3U 12225 46 maskSlack c)| := bweaken (babs (sGlobal20_hz107 hc)) (by norm_num) (by norm_num)

theorem sGlobal20_hz115 {c : ℝ} (hc : B (89 / 200) (9 / 20) c) : B 0 (78435608635557053833 / 500000000000000000) |(s3L 12225 46 maskSlack c)| := bweaken (babs (sGlobal20_hz113 hc)) (by norm_num) (by norm_num)

theorem sGlobal20_hz116 {c : ℝ} (hc : B (89 / 200) (9 / 20) c) : B 0 (1745059453790966947397 / 1000000000000000000) (max |(s3U 12225 46 maskSlack c)| |(s3L 12225 46 maskSlack c)|) := bweaken (bmax (sGlobal20_hz114 hc) (sGlobal20_hz115 hc)) (by norm_num) (by norm_num)

theorem sGlobal20_hz117 {c : ℝ} (hc : B (89 / 200) (9 / 20) c) : B 0 (1745059453790966947397 / 1000000000000000000) (s3nks 12225 46 maskSlack c) := by
    convert (sGlobal20_hz116 hc) using 1 <;>
      norm_num [s3nks] <;> ring

theorem sGlobal20 {c : ℝ} (hc : B (89 / 200) (9 / 20) c) :
    0 < s3am 12225 46 ∧ 0 ≤ s3dm 12225 46 c ∧
    s3dm 12225 46 c ^ 2 ≤ 2 * s3ap 12225 46 ^ 2 ∧ s3c1 12225 46 c < 1 ∧
    0 ≤ s3Cpa 12225 c - s3r1 12225 46 ∧
    s3e0 12225 46 ≤ (s3Cpa 12225 c - s3r1 12225 46) / s3ap 12225 46 ∧
    s3nks 12225 46 maskSlack c ≤ 12225 * (71373 / 500000) := by

  refine ⟨lt_of_lt_of_le (by norm_num) sGlobal20_hz14.1,
    le_trans (by norm_num) (sGlobal20_hz64 hc).1, ?_,
    lt_of_le_of_lt (sGlobal20_hz72 hc).2 (by norm_num), ?_, ?_,
    le_trans (sGlobal20_hz117 hc).2 (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (sGlobal20_hz64 hc).1) (sGlobal20_hz64 hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) sGlobal20_hz9.1 2
    nlinarith only [h1, h2]
  · linarith only [(sGlobal20_hz84 hc).1, sGlobal20_hz33.2]
  · have hap : 0 < s3ap 12225 46 := lt_of_lt_of_le (by norm_num) sGlobal20_hz9.1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul sGlobal20_hz16.2 sGlobal20_hz9.2 (le_trans (by norm_num) sGlobal20_hz9.1) (by norm_num)
    linarith only [h, (sGlobal20_hz84 hc).1, sGlobal20_hz33.2]

end BstLean.Part255
