import BstLean.Part255SGlobal14
import BstLean.Part255Numeric10
namespace BstLean.Part255
open Real BstLean.Part130 BstLean.Part182 BstLean.Part197 BstLean.Part246
theorem sGlobal18_hz0 : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal18_hz1 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) ((√(23 : ℝ)) / (12225 : ℝ)) := bdiv sGlobal18_hz0 (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal18_hz2 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) maskSlack := by
    convert sGlobal18_hz1 using 1 <;>
      norm_num [maskSlack] <;> ring

theorem sGlobal18_hz3 : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal18_hz4 : B (6395294793910793 / 500000000000000000) (12790589587821587 / 1000000000000000000) (√((2 / 12225) : ℝ)) := bsqrt (bpoint ((2 / 12225) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal18_hz5 : B (7230130686979 / 62500000000000000) (23136418198333 / 200000000000000000) (√((2 / 149450625) : ℝ)) := bsqrt (bpoint ((2 / 149450625) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal18_hz6 : B (2211334438749598093 / 20000000000000000) (110566721937479904651 / 1000000000000000000) (√(12225 : ℝ)) := bsqrt (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal18_hz7 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))) := bmul sGlobal18_hz3 sGlobal18_hz4 (by norm_num) (by norm_num)

theorem sGlobal18_hz8 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) ((√(12225 : ℝ)) + ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := badd sGlobal18_hz6 sGlobal18_hz7 (by norm_num) (by norm_num)

theorem sGlobal18_hz9 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) (s3ap 12225 46) := by
    convert sGlobal18_hz8 using 1 <;>
      norm_num [s3ap, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal18_hz10 : B (163599182004089 / 1000000000000000000) (16359918200409 / 100000000000000000) ((2 : ℝ) / (12225 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal18_hz11 : B (1222499983640081799591 / 100000000000000000) (12224999836400817995911 / 1000000000000000000) ((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ))) := bsub (bpoint (12225 : ℝ)) sGlobal18_hz10 (by norm_num) (by norm_num)

theorem sGlobal18_hz12 : B (110566721197658827907 / 1000000000000000000) (27641680299414706977 / 250000000000000000) (√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) := bsqrt sGlobal18_hz11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal18_hz13 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) ((√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) - ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bsub sGlobal18_hz12 sGlobal18_hz7 (by norm_num) (by norm_num)

theorem sGlobal18_hz14 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) (s3am 12225 46) := by
    convert sGlobal18_hz13 using 1 <;>
      norm_num [s3am, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal18_hz15 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√((2 / 12225) : ℝ)) * (√(92 : ℝ))) := bmul sGlobal18_hz4 sGlobal18_hz3 (by norm_num) (by norm_num)

theorem sGlobal18_hz16 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) (s3e0 12225 46) := by
    convert sGlobal18_hz15 using 1 <;>
      norm_num [s3e0, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal18_hz17 : B (250196148528560847 / 500000000000000000) (100078459411424339 / 200000000000000000) (((1 / 2) : ℝ) + maskSlack) := badd (bpoint ((1 / 2) : ℝ)) sGlobal18_hz2 (by norm_num) (by norm_num)

theorem sGlobal18_hz18 : B (59827153232297998295487 / 800000000000000) (23930861292919199366019 / 320000000000000) ((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack)) := bmul (bpoint (149450625 : ℝ)) sGlobal18_hz17 (by norm_num) (by norm_num)

theorem sGlobal18_hz19 : B (1729554180017180009583 / 200000000000000000) (8647770900085900056557 / 1000000000000000000) (√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) := bsqrt sGlobal18_hz18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal18_hz20 : B (4328681281566262743499 / 500000000000000000) (8657362563132525495641 / 1000000000000000000) ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))) := badd sGlobal18_hz19 sGlobal18_hz3 (by norm_num) (by norm_num)

theorem sGlobal18_hz21 : B (110732771457999278473 / 1000000000000000000) (55366385728999643621 / 500000000000000000) ((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ)))) := bmul sGlobal18_hz4 sGlobal18_hz20 (by norm_num) (by norm_num)

theorem sGlobal18_hz22 : B (209099159 / 15625000000000000) (13382346177 / 1000000000000000000) ((2 : ℝ) / (149450625 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (149450625 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal18_hz23 : B (2452349334953899930479 / 200000000000000000) (12261746674769501594427 / 1000000000000000000) (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2) := bsq sGlobal18_hz21 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal18_hz24 : B (82045469362091 / 500000000000000000) (32818187747289 / 200000000000000000) (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2)) := bmul sGlobal18_hz22 sGlobal18_hz23 (by norm_num) (by norm_num)

theorem sGlobal18_hz25 : B (82045469362091 / 250000000000000000) (32818187747289 / 100000000000000000) ((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) := bmul (bpoint (2 : ℝ)) sGlobal18_hz24 (by norm_num) (by norm_num)

theorem sGlobal18_hz26 : B (117258080744995992792057 / 1000000000000000000) (58629040372497996396029 / 500000000000000000) (√(13749457500 : ℝ)) := bsqrt (bpoint (13749457500 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal18_hz27 : B (117304080744995992792057 / 1000000000000000000) (58652040372497996396029 / 500000000000000000) ((√(13749457500 : ℝ)) + (46 : ℝ)) := badd sGlobal18_hz26 (bpoint (46 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal18_hz28 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal18_hz25 sGlobal18_hz27 (by norm_num) (by norm_num)

theorem sGlobal18_hz29 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (s3rs 12225 46 maskSlack) := by
    convert sGlobal18_hz28 using 1 <;>
      norm_num [s3rs, s3pp, s3K, mA, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal18_hz30 : B (490797546012267 / 1000000000000000000) (49079754601227 / 100000000000000000) ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (3 : ℝ)) sGlobal18_hz10 (by norm_num) (by norm_num)

theorem sGlobal18_hz31 : B (490797546012267 / 500000000000000000) (49079754601227 / 50000000000000000) ((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal18_hz30 (by norm_num) (by norm_num)

theorem sGlobal18_hz32 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal18_hz31 sGlobal18_hz27 (by norm_num) (by norm_num)

theorem sGlobal18_hz33 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (s3r1 12225 46) := by
    convert sGlobal18_hz32 using 1 <;>
      norm_num [s3r1, mA] <;> ring

theorem sGlobal18_hz34 : B (163599182004089 / 500000000000000000) (16359918200409 / 50000000000000000) ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (2 : ℝ)) sGlobal18_hz10 (by norm_num) (by norm_num)

theorem sGlobal18_hz35 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal18_hz34 (by norm_num) (by norm_num)

theorem sGlobal18_hz36 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal18_hz35 sGlobal18_hz27 (by norm_num) (by norm_num)

theorem sGlobal18_hz37 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (s3rpp 12225 46) := by
    convert sGlobal18_hz36 using 1 <;>
      norm_num [s3rpp, mA] <;> ring

theorem sGlobal18_hz38 {c : ℝ} (hc : B (87 / 200) (11 / 25) c) : B (87 / 200) (11 / 25) c := hc

theorem sGlobal18_hz39 : B (643251632656853101 / 1000000000000000000) (25730065306399753 / 40000000000000000) (kdot ((87 / 200))) := by
    constructor
    · apply bkdot_lower (q := (78434708416112299 / 125000000000000000)) (a := (560379025012691601 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (627477667328898391 / 1000000000000000000)) (a := (112075805001551633 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal18_hz40 : B (7569 / 40000) (7569 / 40000) (((87 / 200) : ℝ)^2) := bsq (bpoint ((87 / 200) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal18_hz41 : B (32431 / 40000) (32431 / 40000) ((1 : ℝ) - (((87 / 200) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal18_hz40 (by norm_num) (by norm_num)

theorem sGlobal18_hz42 : B (900430452616969191 / 1000000000000000000) (112553806577121149 / 125000000000000000) (√((1 : ℝ) - (((87 / 200) : ℝ)^2))) := bsqrt sGlobal18_hz41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal18_hz43 : B (143307957444463291 / 500000000000000000) (286615914888926583 / 1000000000000000000) ((√((1 : ℝ) - (((87 / 200) : ℝ)^2))) / Real.pi) := bdiv sGlobal18_hz42 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal18_hz44 : B (139907230102865549 / 500000000000000000) (139907230103548657 / 500000000000000000) (((87 / 200) : ℝ) * (kdot ((87 / 200)))) := bmul (bpoint ((87 / 200) : ℝ)) sGlobal18_hz39 (by norm_num) (by norm_num)

theorem sGlobal18_hz45 : B (7080379688683221 / 12500000000000000) (566430375096023897 / 1000000000000000000) (((√((1 : ℝ) - (((87 / 200) : ℝ)^2))) / Real.pi) + (((87 / 200) : ℝ) * (kdot ((87 / 200))))) := badd sGlobal18_hz43 sGlobal18_hz44 (by norm_num) (by norm_num)

theorem sGlobal18_hz46 : B (7080379688683221 / 12500000000000000) (566430375096023897 / 1000000000000000000) (kappa ((87 / 200))) := by rw [kappa_eq]; exact sGlobal18_hz45

theorem sGlobal18_hz47 : B (322510780936897579 / 500000000000000000) (645021561876114903 / 1000000000000000000) (kdot ((11 / 25))) := by
    constructor
    · apply bkdot_lower (q := (124721912892464713 / 200000000000000000)) (a := (557598826700032049 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (155902391115580891 / 250000000000000000)) (a := (111519765339277641 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal18_hz48 : B (121 / 625) (121 / 625) (((11 / 25) : ℝ)^2) := bsq (bpoint ((11 / 25) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal18_hz49 : B (504 / 625) (504 / 625) ((1 : ℝ) - (((11 / 25) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal18_hz48 (by norm_num) (by norm_num)

theorem sGlobal18_hz50 : B (224499443206436483 / 250000000000000000) (897997772825745933 / 1000000000000000000) (√((1 : ℝ) - (((11 / 25) : ℝ)^2))) := bsqrt sGlobal18_hz49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal18_hz51 : B (285841568861460699 / 1000000000000000000) (2858415688614607 / 10000000000000000) ((√((1 : ℝ) - (((11 / 25) : ℝ)^2))) / Real.pi) := bdiv sGlobal18_hz50 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal18_hz52 : B (283809487224469869 / 1000000000000000000) (141904743612745279 / 500000000000000000) (((11 / 25) : ℝ) * (kdot ((11 / 25)))) := bmul (bpoint ((11 / 25) : ℝ)) sGlobal18_hz47 (by norm_num) (by norm_num)

theorem sGlobal18_hz53 : B (71206382010741321 / 125000000000000000) (284825528043475629 / 500000000000000000) (((√((1 : ℝ) - (((11 / 25) : ℝ)^2))) / Real.pi) + (((11 / 25) : ℝ) * (kdot ((11 / 25))))) := badd sGlobal18_hz51 sGlobal18_hz52 (by norm_num) (by norm_num)

theorem sGlobal18_hz54 : B (71206382010741321 / 125000000000000000) (284825528043475629 / 500000000000000000) (kappa ((11 / 25))) := by rw [kappa_eq]; exact sGlobal18_hz53

theorem sGlobal18_hz55 {c : ℝ} (hc : B (87 / 200) (11 / 25) c) : B (7080379688683221 / 12500000000000000) (284825528043475629 / 500000000000000000) (kappa c) := bkappa (sGlobal18_hz38 hc) (by norm_num) (by norm_num) sGlobal18_hz46.1 sGlobal18_hz54.2

theorem sGlobal18_hz56 : B 24450 24450 ((2 : ℝ) * (12225 : ℝ)) := bmul (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal18_hz57 {c : ℝ} (hc : B (87 / 200) (11 / 25) c) : B (215174471956524371 / 500000000000000000) (5419620311316779 / 12500000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (sGlobal18_hz55 hc) (by norm_num) (by norm_num)

theorem sGlobal18_hz58 {c : ℝ} (hc : B (87 / 200) (11 / 25) c) : B (105220316786740417419 / 10000000000000000) (2650194332233904931 / 250000000000000) (((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) := bmul sGlobal18_hz56 (sGlobal18_hz57 hc) (by norm_num) (by norm_num)

theorem sGlobal18_hz59 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (4 : ℝ)) sGlobal18_hz10 (by norm_num) (by norm_num)

theorem sGlobal18_hz60 {c : ℝ} (hc : B (87 / 200) (11 / 25) c) : B (526101551213865686277 / 50000000000000000) (2650194168634722926911 / 250000000000000000) ((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bsub (sGlobal18_hz58 hc) sGlobal18_hz59 (by norm_num) (by norm_num)

theorem sGlobal18_hz61 {c : ℝ} (hc : B (87 / 200) (11 / 25) c) : B (51288475860268341877 / 500000000000000000) (25740018301444168393 / 250000000000000000) (√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) := bsqrt (sGlobal18_hz60 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal18_hz62 : B (30670756373515103 / 125000000000000000) (122683025494060423 / 500000000000000000) ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal18_hz7 (by norm_num) (by norm_num)

theorem sGlobal18_hz63 {c : ℝ} (hc : B (87 / 200) (11 / 25) c) : B (25582896417387140727 / 250000000000000000) (25678676788697138187 / 250000000000000000) ((√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) - ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))))) := bsub (sGlobal18_hz61 hc) sGlobal18_hz62 (by norm_num) (by norm_num)

theorem sGlobal18_hz64 {c : ℝ} (hc : B (87 / 200) (11 / 25) c) : B (25582896417387140727 / 250000000000000000) (25678676788697138187 / 250000000000000000) (s3dm 12225 46 c) := by
    convert (sGlobal18_hz63 hc) using 1 <;>
      norm_num [s3dm, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal18_hz65 : B (6126072185528622723889 / 500000000000000000) (2450428874211449090087 / 200000000000000000) ((s3ap 12225 46)^2) := bsq sGlobal18_hz9 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal18_hz66 : B (6126072185528622723889 / 250000000000000000) (2450428874211449090087 / 100000000000000000) ((2 : ℝ) * ((s3ap 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal18_hz65 (by norm_num) (by norm_num)

theorem sGlobal18_hz67 {c : ℝ} (hc : B (87 / 200) (11 / 25) c) : B (1047175342564415680199 / 100000000000000000) (1055031106589397070889 / 100000000000000000) ((s3dm 12225 46 c)^2) := bsq (sGlobal18_hz64 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal18_hz68 {c : ℝ} (hc : B (87 / 200) (11 / 25) c) : B (6976988838110260093333 / 500000000000000000) (43851672863969794059 / 3125000000000000) (((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) := bsub sGlobal18_hz66 (sGlobal18_hz67 hc) (by norm_num) (by norm_num)

theorem sGlobal18_hz69 : B (1524735695971823534271 / 125000000000000000) (609894278388729413841 / 50000000000000000) ((s3am 12225 46)^2) := bsq sGlobal18_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal18_hz70 : B (1524735695971823534271 / 62500000000000000) (609894278388729413841 / 25000000000000000) ((2 : ℝ) * ((s3am 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal18_hz69 (by norm_num) (by norm_num)

theorem sGlobal18_hz71 {c : ℝ} (hc : B (87 / 200) (11 / 25) c) : B (571983463801518413 / 1000000000000000000) (575203597316188947 / 1000000000000000000) ((((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) / ((2 : ℝ) * ((s3am 12225 46)^2))) := bdiv (sGlobal18_hz68 hc) sGlobal18_hz70 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal18_hz72 {c : ℝ} (hc : B (87 / 200) (11 / 25) c) : B (571983463801518413 / 1000000000000000000) (575203597316188947 / 1000000000000000000) (s3c1 12225 46 c) := by
    convert (sGlobal18_hz71 hc) using 1 <;>
      norm_num [s3c1] <;> ring

theorem sGlobal18_hz73 {c : ℝ} (hc : B (87 / 200) (11 / 25) c) : B (643251632656853101 / 1000000000000000000) (645021561876114903 / 1000000000000000000) (kdot c) := bkdot (sGlobal18_hz38 hc) sGlobal18_hz39.1 sGlobal18_hz47.2

theorem sGlobal18_hz74 : B (693825860287873633 / 1000000000000000000) (86728232535984251 / 125000000000000000) (kdot ((571983463801518413 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (65225332310762503 / 125000000000000000)) (a := (480937214019395583 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (521802658486100023 / 1000000000000000000)) (a := (96187442803878999 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal18_hz75 : B (347538587461467041 / 500000000000000000) (34753858746146719 / 50000000000000000) (kdot ((575203597316188947 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (259652239082547733 / 500000000000000000)) (a := (478971653586977933 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (103860895633019093 / 200000000000000000)) (a := (478971653586977467 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal18_hz76 {c : ℝ} (hc : B (87 / 200) (11 / 25) c) : B (693825860287873633 / 1000000000000000000) (34753858746146719 / 50000000000000000) (kdot (s3c1 12225 46 c)) := bkdot (sGlobal18_hz72 hc) sGlobal18_hz74.1 sGlobal18_hz75.2

theorem sGlobal18_hz77 {c : ℝ} (hc : B (87 / 200) (11 / 25) c) : B (7569 / 40000) (121 / 625) (c^2) := bsq (sGlobal18_hz38 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal18_hz78 {c : ℝ} (hc : B (87 / 200) (11 / 25) c) : B (504 / 625) (32431 / 40000) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (sGlobal18_hz77 hc) (by norm_num) (by norm_num)

theorem sGlobal18_hz79 {c : ℝ} (hc : B (87 / 200) (11 / 25) c) : B (224499443206436483 / 250000000000000000) (112553806577121149 / 125000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (sGlobal18_hz78 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal18_hz80 : B (39119999999999765769 / 1600000000000000) (3912000000000000489 / 160000000000000) ((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (149450625 : ℝ)) sGlobal18_hz10 (by norm_num) (by norm_num)

theorem sGlobal18_hz81 {c : ℝ} (hc : B (87 / 200) (11 / 25) c) : B (9025602085818421 / 15625000000000000) (290398528453907271 / 500000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (sGlobal18_hz79 hc) (sGlobal18_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal18_hz82 {c : ℝ} (hc : B (87 / 200) (11 / 25) c) : B (14123262143888580617767 / 1000000000000000000) (7100244020698033663481 / 500000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) := bmul sGlobal18_hz80 (sGlobal18_hz81 hc) (by norm_num) (by norm_num)

theorem sGlobal18_hz83 {c : ℝ} (hc : B (87 / 200) (11 / 25) c) : B (7061631071944290308883 / 1000000000000000000) (7100244020698033663481 / 1000000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) / (2 : ℝ)) := bdiv (sGlobal18_hz82 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal18_hz84 {c : ℝ} (hc : B (87 / 200) (11 / 25) c) : B (7061631071944290308883 / 1000000000000000000) (7100244020698033663481 / 1000000000000000000) (s3Cpa 12225 c) := by
    convert (sGlobal18_hz83 hc) using 1 <;>
      norm_num [s3Cpa, mA] <;> ring

theorem sGlobal18_hz85 {c : ℝ} (hc : B (87 / 200) (11 / 25) c) : B (285841568861460699 / 1000000000000000000) (286615914888926583 / 1000000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (sGlobal18_hz79 hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal18_hz86 {c : ℝ} (hc : B (87 / 200) (11 / 25) c) : B (139907230102865549 / 500000000000000000) (141904743612745279 / 500000000000000000) (c * (kdot c)) := bmul (sGlobal18_hz38 hc) (sGlobal18_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal18_hz87 {c : ℝ} (hc : B (87 / 200) (11 / 25) c) : B (2032081635970141 / 1000000000000000000) (1360290936639097 / 200000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (sGlobal18_hz85 hc) (sGlobal18_hz86 hc) (by norm_num) (by norm_num)

theorem sGlobal18_hz88 {c : ℝ} (hc : B (87 / 200) (11 / 25) c) : B (12421098999867412491 / 250000000000000000) (166295567004129629037 / 1000000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) := bmul sGlobal18_hz80 (sGlobal18_hz87 hc) (by norm_num) (by norm_num)

theorem sGlobal18_hz89 {c : ℝ} (hc : B (87 / 200) (11 / 25) c) : B (12421098999867412491 / 500000000000000000) (83147783502064814519 / 1000000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) / (2 : ℝ)) := bdiv (sGlobal18_hz88 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal18_hz90 {c : ℝ} (hc : B (87 / 200) (11 / 25) c) : B (12421098999867412491 / 500000000000000000) (83147783502064814519 / 1000000000000000000) (s3Cpp 12225 c) := by
    convert (sGlobal18_hz89 hc) using 1 <;>
      norm_num [s3Cpp, mA] <;> ring

theorem sGlobal18_hz91 {c : ℝ} (hc : B (87 / 200) (11 / 25) c) : B (1794194045469507004321 / 250000000000000000) (7215389130631772075707 / 1000000000000000000) ((s3Cpa 12225 c) + (s3r1 12225 46)) := badd (sGlobal18_hz84 hc) sGlobal18_hz33 (by norm_num) (by norm_num)

theorem sGlobal18_hz92 {c : ℝ} (hc : B (87 / 200) (11 / 25) c) : B (8122638737061762379 / 125000000000000000) (32665362703345394373 / 500000000000000000) (((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) := bdiv (sGlobal18_hz91 hc) sGlobal18_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal18_hz93 {c : ℝ} (hc : B (87 / 200) (11 / 25) c) : B (16275948230497039861 / 250000000000000000) (65453408432184849169 / 1000000000000000000) ((((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) + (s3e0 12225 46)) := badd (sGlobal18_hz92 hc) sGlobal18_hz16 (by norm_num) (by norm_num)

theorem sGlobal18_hz94 {c : ℝ} (hc : B (87 / 200) (11 / 25) c) : B (16275948230497039861 / 250000000000000000) (65453408432184849169 / 1000000000000000000) (s3Lam 12225 46 c) := by
    convert (sGlobal18_hz93 hc) using 1 <;>
      norm_num [s3Lam] <;> ring

theorem sGlobal18_hz95 {c : ℝ} (hc : B (87 / 200) (11 / 25) c) : B (50802802311113315291 / 500000000000000000) (159911190124557089337 / 1000000000000000000) ((s3Cpp 12225 c) + (s3rpp 12225 46)) := badd (sGlobal18_hz90 hc) sGlobal18_hz37 (by norm_num) (by norm_num)

theorem sGlobal18_hz96 {c : ℝ} (hc : B (87 / 200) (11 / 25) c) : B (50802802311113315291 / 1000000000000000000) (111150618270341384771 / 1000000000000000000) (if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) := bweaken (bfirst (sGlobal18_hz95 hc) (sGlobal18_hz76 hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem sGlobal18_hz97 {c : ℝ} (hc : B (87 / 200) (11 / 25) c) : B (16556655675113732687 / 3906250000000000) (2142074337695203357469 / 500000000000000000) ((s3Lam 12225 46 c)^2) := bsq (sGlobal18_hz94 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal18_hz98 {c : ℝ} (hc : B (87 / 200) (11 / 25) c) : B (81791270715595731 / 250000000000000000) (330859178365484449 / 1000000000000000000) ((s3c1 12225 46 c)^2) := bsq (sGlobal18_hz72 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal18_hz99 {c : ℝ} (hc : B (87 / 200) (11 / 25) c) : B (669140821634515551 / 1000000000000000000) (168208729284404269 / 250000000000000000) ((1 : ℝ) - ((s3c1 12225 46 c)^2)) := bsub (bpoint (1 : ℝ)) (sGlobal18_hz98 hc) (by norm_num) (by norm_num)

theorem sGlobal18_hz100 {c : ℝ} (hc : B (87 / 200) (11 / 25) c) : B (25562821315877021 / 31250000000000000) (205066287626955073 / 250000000000000000) (√((1 : ℝ) - ((s3c1 12225 46 c)^2))) := bsqrt (sGlobal18_hz99 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal18_hz101 {c : ℝ} (hc : B (87 / 200) (11 / 25) c) : B (1284927546415805129 / 500000000000000000) (161058685676943393 / 62500000000000000) (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))) := bmul pi_mem (sGlobal18_hz100 hc) (by norm_num) (by norm_num)

theorem sGlobal18_hz102 {c : ℝ} (hc : B (87 / 200) (11 / 25) c) : B (822391197619660025201 / 500000000000000000) (41676947927342975047 / 25000000000000000) (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2))))) := bdiv (sGlobal18_hz97 hc) (sGlobal18_hz101 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal18_hz103 {c : ℝ} (hc : B (87 / 200) (11 / 25) c) : B (1695585197550433365693 / 1000000000000000000) (1778228535364060386651 / 1000000000000000000) ((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) := badd (sGlobal18_hz96 hc) (sGlobal18_hz102 hc) (by norm_num) (by norm_num)

theorem sGlobal18_hz104 : B (3762781186094069 / 250000000000000000) (376278118609407 / 25000000000000000) ((s3e0 12225 46)^2) := bsq sGlobal18_hz16 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal18_hz105 {c : ℝ} (hc : B (87 / 200) (11 / 25) c) : B (1695600248675177741969 / 1000000000000000000) (1778243586488804762931 / 1000000000000000000) (((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) := badd (sGlobal18_hz103 hc) sGlobal18_hz104 (by norm_num) (by norm_num)

theorem sGlobal18_hz106 {c : ℝ} (hc : B (87 / 200) (11 / 25) c) : B (17340973221264250121 / 10000000000000000) (1816740659942929032947 / 1000000000000000000) ((((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) + (s3rs 12225 46 maskSlack)) := badd (sGlobal18_hz105 hc) sGlobal18_hz29 (by norm_num) (by norm_num)

theorem sGlobal18_hz107 {c : ℝ} (hc : B (87 / 200) (11 / 25) c) : B (17340973221264250121 / 10000000000000000) (1816740659942929032947 / 1000000000000000000) (s3U 12225 46 maskSlack c) := by
    convert (sGlobal18_hz106 hc) using 1 <;>
      norm_num [s3U] <;> ring

theorem sGlobal18_hz108 {c : ℝ} (hc : B (87 / 200) (11 / 25) c) : B (-12980302155689362459 / 250000000000000000) (6384376879573008919 / 1000000000000000000) ((s3Cpp 12225 c) - (s3rpp 12225 46)) := bsub (sGlobal18_hz90 hc) sGlobal18_hz37 (by norm_num) (by norm_num)

theorem sGlobal18_hz109 {c : ℝ} (hc : B (87 / 200) (11 / 25) c) : B (-12980302155689362459 / 250000000000000000) 0 (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ)) := bweaken (bmin (sGlobal18_hz108 hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem sGlobal18_hz110 {c : ℝ} (hc : B (87 / 200) (11 / 25) c) : B (-36089247008090548809 / 1000000000000000000) 0 ((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) := bmul (sGlobal18_hz76 hc) (sGlobal18_hz109 hc) (by norm_num) (by norm_num)

theorem sGlobal18_hz111 {c : ℝ} (hc : B (87 / 200) (11 / 25) c) : B (-36104298132834925089 / 1000000000000000000) (-3762781186094069 / 250000000000000000) (((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) := bsub (sGlobal18_hz110 hc) sGlobal18_hz104 (by norm_num) (by norm_num)

theorem sGlobal18_hz112 {c : ℝ} (hc : B (87 / 200) (11 / 25) c) : B (-14920274317391839021 / 200000000000000000) (-38512124575991646407 / 1000000000000000000) ((((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) - (s3rs 12225 46 maskSlack)) := bsub (sGlobal18_hz111 hc) sGlobal18_hz29 (by norm_num) (by norm_num)

theorem sGlobal18_hz113 {c : ℝ} (hc : B (87 / 200) (11 / 25) c) : B (-14920274317391839021 / 200000000000000000) (-38512124575991646407 / 1000000000000000000) (s3L 12225 46 maskSlack c) := by
    convert (sGlobal18_hz112 hc) using 1 <;>
      norm_num [s3L] <;> ring

theorem sGlobal18_hz114 {c : ℝ} (hc : B (87 / 200) (11 / 25) c) : B 0 (1816740659942929032947 / 1000000000000000000) |(s3U 12225 46 maskSlack c)| := bweaken (babs (sGlobal18_hz107 hc)) (by norm_num) (by norm_num)

theorem sGlobal18_hz115 {c : ℝ} (hc : B (87 / 200) (11 / 25) c) : B 0 (14920274317391839021 / 200000000000000000) |(s3L 12225 46 maskSlack c)| := bweaken (babs (sGlobal18_hz113 hc)) (by norm_num) (by norm_num)

theorem sGlobal18_hz116 {c : ℝ} (hc : B (87 / 200) (11 / 25) c) : B 0 (1816740659942929032947 / 1000000000000000000) (max |(s3U 12225 46 maskSlack c)| |(s3L 12225 46 maskSlack c)|) := bweaken (bmax (sGlobal18_hz114 hc) (sGlobal18_hz115 hc)) (by norm_num) (by norm_num)

theorem sGlobal18_hz117 {c : ℝ} (hc : B (87 / 200) (11 / 25) c) : B 0 (1816740659942929032947 / 1000000000000000000) (s3nks 12225 46 maskSlack c) := by
    convert (sGlobal18_hz116 hc) using 1 <;>
      norm_num [s3nks] <;> ring

theorem sGlobal18 {c : ℝ} (hc : B (87 / 200) (11 / 25) c) :
    0 < s3am 12225 46 ∧ 0 ≤ s3dm 12225 46 c ∧
    s3dm 12225 46 c ^ 2 ≤ 2 * s3ap 12225 46 ^ 2 ∧ s3c1 12225 46 c < 1 ∧
    0 ≤ s3Cpa 12225 c - s3r1 12225 46 ∧
    s3e0 12225 46 ≤ (s3Cpa 12225 c - s3r1 12225 46) / s3ap 12225 46 ∧
    s3nks 12225 46 maskSlack c ≤ 12225 * (148609 / 1000000) := by

  refine ⟨lt_of_lt_of_le (by norm_num) sGlobal18_hz14.1,
    le_trans (by norm_num) (sGlobal18_hz64 hc).1, ?_,
    lt_of_le_of_lt (sGlobal18_hz72 hc).2 (by norm_num), ?_, ?_,
    le_trans (sGlobal18_hz117 hc).2 (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (sGlobal18_hz64 hc).1) (sGlobal18_hz64 hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) sGlobal18_hz9.1 2
    nlinarith only [h1, h2]
  · linarith only [(sGlobal18_hz84 hc).1, sGlobal18_hz33.2]
  · have hap : 0 < s3ap 12225 46 := lt_of_lt_of_le (by norm_num) sGlobal18_hz9.1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul sGlobal18_hz16.2 sGlobal18_hz9.2 (le_trans (by norm_num) sGlobal18_hz9.1) (by norm_num)
    linarith only [h, (sGlobal18_hz84 hc).1, sGlobal18_hz33.2]

end BstLean.Part255
