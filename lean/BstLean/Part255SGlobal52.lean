import BstLean.Part255SGlobal48
import BstLean.Part255Numeric10
namespace BstLean.Part255
open Real BstLean.Part130 BstLean.Part182 BstLean.Part197 BstLean.Part246
theorem sGlobal52_hz0 : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal52_hz1 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) ((√(23 : ℝ)) / (12225 : ℝ)) := bdiv sGlobal52_hz0 (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal52_hz2 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) maskSlack := by
    convert sGlobal52_hz1 using 1 <;>
      norm_num [maskSlack] <;> ring

theorem sGlobal52_hz3 : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal52_hz4 : B (6395294793910793 / 500000000000000000) (12790589587821587 / 1000000000000000000) (√((2 / 12225) : ℝ)) := bsqrt (bpoint ((2 / 12225) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal52_hz5 : B (7230130686979 / 62500000000000000) (23136418198333 / 200000000000000000) (√((2 / 149450625) : ℝ)) := bsqrt (bpoint ((2 / 149450625) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal52_hz6 : B (2211334438749598093 / 20000000000000000) (110566721937479904651 / 1000000000000000000) (√(12225 : ℝ)) := bsqrt (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal52_hz7 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))) := bmul sGlobal52_hz3 sGlobal52_hz4 (by norm_num) (by norm_num)

theorem sGlobal52_hz8 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) ((√(12225 : ℝ)) + ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := badd sGlobal52_hz6 sGlobal52_hz7 (by norm_num) (by norm_num)

theorem sGlobal52_hz9 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) (s3ap 12225 46) := by
    convert sGlobal52_hz8 using 1 <;>
      norm_num [s3ap, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal52_hz10 : B (163599182004089 / 1000000000000000000) (16359918200409 / 100000000000000000) ((2 : ℝ) / (12225 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal52_hz11 : B (1222499983640081799591 / 100000000000000000) (12224999836400817995911 / 1000000000000000000) ((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ))) := bsub (bpoint (12225 : ℝ)) sGlobal52_hz10 (by norm_num) (by norm_num)

theorem sGlobal52_hz12 : B (110566721197658827907 / 1000000000000000000) (27641680299414706977 / 250000000000000000) (√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) := bsqrt sGlobal52_hz11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal52_hz13 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) ((√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) - ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bsub sGlobal52_hz12 sGlobal52_hz7 (by norm_num) (by norm_num)

theorem sGlobal52_hz14 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) (s3am 12225 46) := by
    convert sGlobal52_hz13 using 1 <;>
      norm_num [s3am, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal52_hz15 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√((2 / 12225) : ℝ)) * (√(92 : ℝ))) := bmul sGlobal52_hz4 sGlobal52_hz3 (by norm_num) (by norm_num)

theorem sGlobal52_hz16 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) (s3e0 12225 46) := by
    convert sGlobal52_hz15 using 1 <;>
      norm_num [s3e0, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal52_hz17 : B (250196148528560847 / 500000000000000000) (100078459411424339 / 200000000000000000) (((1 / 2) : ℝ) + maskSlack) := badd (bpoint ((1 / 2) : ℝ)) sGlobal52_hz2 (by norm_num) (by norm_num)

theorem sGlobal52_hz18 : B (59827153232297998295487 / 800000000000000) (23930861292919199366019 / 320000000000000) ((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack)) := bmul (bpoint (149450625 : ℝ)) sGlobal52_hz17 (by norm_num) (by norm_num)

theorem sGlobal52_hz19 : B (1729554180017180009583 / 200000000000000000) (8647770900085900056557 / 1000000000000000000) (√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) := bsqrt sGlobal52_hz18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal52_hz20 : B (4328681281566262743499 / 500000000000000000) (8657362563132525495641 / 1000000000000000000) ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))) := badd sGlobal52_hz19 sGlobal52_hz3 (by norm_num) (by norm_num)

theorem sGlobal52_hz21 : B (110732771457999278473 / 1000000000000000000) (55366385728999643621 / 500000000000000000) ((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ)))) := bmul sGlobal52_hz4 sGlobal52_hz20 (by norm_num) (by norm_num)

theorem sGlobal52_hz22 : B (209099159 / 15625000000000000) (13382346177 / 1000000000000000000) ((2 : ℝ) / (149450625 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (149450625 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal52_hz23 : B (2452349334953899930479 / 200000000000000000) (12261746674769501594427 / 1000000000000000000) (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2) := bsq sGlobal52_hz21 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal52_hz24 : B (82045469362091 / 500000000000000000) (32818187747289 / 200000000000000000) (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2)) := bmul sGlobal52_hz22 sGlobal52_hz23 (by norm_num) (by norm_num)

theorem sGlobal52_hz25 : B (82045469362091 / 250000000000000000) (32818187747289 / 100000000000000000) ((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) := bmul (bpoint (2 : ℝ)) sGlobal52_hz24 (by norm_num) (by norm_num)

theorem sGlobal52_hz26 : B (117258080744995992792057 / 1000000000000000000) (58629040372497996396029 / 500000000000000000) (√(13749457500 : ℝ)) := bsqrt (bpoint (13749457500 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal52_hz27 : B (117304080744995992792057 / 1000000000000000000) (58652040372497996396029 / 500000000000000000) ((√(13749457500 : ℝ)) + (46 : ℝ)) := badd sGlobal52_hz26 (bpoint (46 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal52_hz28 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal52_hz25 sGlobal52_hz27 (by norm_num) (by norm_num)

theorem sGlobal52_hz29 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (s3rs 12225 46 maskSlack) := by
    convert sGlobal52_hz28 using 1 <;>
      norm_num [s3rs, s3pp, s3K, mA, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal52_hz30 : B (490797546012267 / 1000000000000000000) (49079754601227 / 100000000000000000) ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (3 : ℝ)) sGlobal52_hz10 (by norm_num) (by norm_num)

theorem sGlobal52_hz31 : B (490797546012267 / 500000000000000000) (49079754601227 / 50000000000000000) ((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal52_hz30 (by norm_num) (by norm_num)

theorem sGlobal52_hz32 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal52_hz31 sGlobal52_hz27 (by norm_num) (by norm_num)

theorem sGlobal52_hz33 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (s3r1 12225 46) := by
    convert sGlobal52_hz32 using 1 <;>
      norm_num [s3r1, mA] <;> ring

theorem sGlobal52_hz34 : B (163599182004089 / 500000000000000000) (16359918200409 / 50000000000000000) ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (2 : ℝ)) sGlobal52_hz10 (by norm_num) (by norm_num)

theorem sGlobal52_hz35 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal52_hz34 (by norm_num) (by norm_num)

theorem sGlobal52_hz36 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal52_hz35 sGlobal52_hz27 (by norm_num) (by norm_num)

theorem sGlobal52_hz37 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (s3rpp 12225 46) := by
    convert sGlobal52_hz36 using 1 <;>
      norm_num [s3rpp, mA] <;> ring

theorem sGlobal52_hz38 {c : ℝ} (hc : B (121 / 200) (61 / 100) c) : B (121 / 200) (61 / 100) c := hc

theorem sGlobal52_hz39 : B (14136537986119283 / 20000000000000000) (88353362413245523 / 125000000000000000) (kdot ((121 / 200))) := by
    constructor
    · apply bkdot_lower (q := (19843625435010217 / 40000000000000000)) (a := (460515229685261869 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (3875708092775433 / 7812500000000000)) (a := (230257614842630909 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal52_hz40 : B (14641 / 40000) (14641 / 40000) (((121 / 200) : ℝ)^2) := bsq (bpoint ((121 / 200) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal52_hz41 : B (25359 / 40000) (25359 / 40000) ((1 : ℝ) - (((121 / 200) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal52_hz40 (by norm_num) (by norm_num)

theorem sGlobal52_hz42 : B (199056367644946239 / 250000000000000000) (796225470579784957 / 1000000000000000000) (√((1 : ℝ) - (((121 / 200) : ℝ)^2))) := bsqrt sGlobal52_hz41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal52_hz43 : B (253446438916886517 / 1000000000000000000) (126723219458443259 / 500000000000000000) ((√((1 : ℝ) - (((121 / 200) : ℝ)^2))) / Real.pi) := bdiv sGlobal52_hz42 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal52_hz44 : B (42763027408010831 / 100000000000000000) (106907568520027083 / 250000000000000000) (((121 / 200) : ℝ) * (kdot ((121 / 200)))) := bmul (bpoint ((121 / 200) : ℝ)) sGlobal52_hz39 (by norm_num) (by norm_num)

theorem sGlobal52_hz45 : B (681076712996994827 / 1000000000000000000) (13621534259939897 / 20000000000000000) (((√((1 : ℝ) - (((121 / 200) : ℝ)^2))) / Real.pi) + (((121 / 200) : ℝ) * (kdot ((121 / 200))))) := badd sGlobal52_hz43 sGlobal52_hz44 (by norm_num) (by norm_num)

theorem sGlobal52_hz46 : B (681076712996994827 / 1000000000000000000) (13621534259939897 / 20000000000000000) (kappa ((121 / 200))) := by rw [kappa_eq]; exact sGlobal52_hz45

theorem sGlobal52_hz47 : B (28353222881079303 / 40000000000000000) (708830572026982599 / 1000000000000000000) (kdot ((61 / 100))) := by
    constructor
    · apply bkdot_lower (q := (492174790948013201 / 1000000000000000000)) (a := (457367867934986991 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (1230436977370033 / 2500000000000000)) (a := (114341966983746739 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal52_hz48 : B (3721 / 10000) (3721 / 10000) (((61 / 100) : ℝ)^2) := bsq (bpoint ((61 / 100) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal52_hz49 : B (6279 / 10000) (6279 / 10000) ((1 : ℝ) - (((61 / 100) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal52_hz48 (by norm_num) (by norm_num)

theorem sGlobal52_hz50 : B (792401413426301253 / 1000000000000000000) (396200706713150627 / 500000000000000000) (√((1 : ℝ) - (((61 / 100) : ℝ)^2))) := bsqrt sGlobal52_hz49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal52_hz51 : B (252229203719600809 / 1000000000000000000) (25222920371960081 / 100000000000000000) ((√((1 : ℝ) - (((61 / 100) : ℝ)^2))) / Real.pi) := bdiv sGlobal52_hz50 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal52_hz52 : B (43238664893645937 / 100000000000000000) (216193324468229693 / 500000000000000000) (((61 / 100) : ℝ) * (kdot ((61 / 100)))) := bmul (bpoint ((61 / 100) : ℝ)) sGlobal52_hz47 (by norm_num) (by norm_num)

theorem sGlobal52_hz53 : B (684615852656060179 / 1000000000000000000) (171153963164015049 / 250000000000000000) (((√((1 : ℝ) - (((61 / 100) : ℝ)^2))) / Real.pi) + (((61 / 100) : ℝ) * (kdot ((61 / 100))))) := badd sGlobal52_hz51 sGlobal52_hz52 (by norm_num) (by norm_num)

theorem sGlobal52_hz54 : B (684615852656060179 / 1000000000000000000) (171153963164015049 / 250000000000000000) (kappa ((61 / 100))) := by rw [kappa_eq]; exact sGlobal52_hz53

theorem sGlobal52_hz55 {c : ℝ} (hc : B (121 / 200) (61 / 100) c) : B (681076712996994827 / 1000000000000000000) (171153963164015049 / 250000000000000000) (kappa c) := bkappa (sGlobal52_hz38 hc) (by norm_num) (by norm_num) sGlobal52_hz46.1 sGlobal52_hz54.2

theorem sGlobal52_hz56 : B 24450 24450 ((2 : ℝ) * (12225 : ℝ)) := bmul (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal52_hz57 {c : ℝ} (hc : B (121 / 200) (61 / 100) c) : B (78846036835984951 / 250000000000000000) (318923287003005173 / 1000000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (sGlobal52_hz55 hc) (by norm_num) (by norm_num)

theorem sGlobal52_hz58 {c : ℝ} (hc : B (121 / 200) (61 / 100) c) : B (38555712012796641039 / 5000000000000000) (155953487344469529597 / 20000000000000000) (((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) := bmul sGlobal52_hz56 (sGlobal52_hz57 hc) (by norm_num) (by norm_num)

theorem sGlobal52_hz59 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (4 : ℝ)) sGlobal52_hz10 (by norm_num) (by norm_num)

theorem sGlobal52_hz60 {c : ℝ} (hc : B (121 / 200) (61 / 100) c) : B (96389271852032502393 / 12500000000000000) (3898836856413374231747 / 500000000000000000) ((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bsub (sGlobal52_hz58 hc) sGlobal52_hz59 (by norm_num) (by norm_num)

theorem sGlobal52_hz61 {c : ℝ} (hc : B (121 / 200) (61 / 100) c) : B (87813106926942291121 / 1000000000000000000) (88304437673464341379 / 1000000000000000000) (√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) := bsqrt (sGlobal52_hz60 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal52_hz62 : B (30670756373515103 / 125000000000000000) (122683025494060423 / 500000000000000000) ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal52_hz7 (by norm_num) (by norm_num)

theorem sGlobal52_hz63 {c : ℝ} (hc : B (121 / 200) (61 / 100) c) : B (3502709635038166811 / 40000000000000000) (17611814324495244111 / 200000000000000000) ((√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) - ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))))) := bsub (sGlobal52_hz61 hc) sGlobal52_hz62 (by norm_num) (by norm_num)

theorem sGlobal52_hz64 {c : ℝ} (hc : B (121 / 200) (61 / 100) c) : B (3502709635038166811 / 40000000000000000) (17611814324495244111 / 200000000000000000) (s3dm 12225 46 c) := by
    convert (sGlobal52_hz63 hc) using 1 <;>
      norm_num [s3dm, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal52_hz65 : B (6126072185528622723889 / 500000000000000000) (2450428874211449090087 / 200000000000000000) ((s3ap 12225 46)^2) := bsq sGlobal52_hz9 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal52_hz66 : B (6126072185528622723889 / 250000000000000000) (2450428874211449090087 / 100000000000000000) ((2 : ℝ) * ((s3ap 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal52_hz65 (by norm_num) (by norm_num)

theorem sGlobal52_hz67 {c : ℝ} (hc : B (121 / 200) (61 / 100) c) : B (7668109242118254836409 / 1000000000000000000) (3877200047506198395403 / 500000000000000000) ((s3dm 12225 46 c)^2) := bsq (sGlobal52_hz64 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal52_hz68 {c : ℝ} (hc : B (121 / 200) (61 / 100) c) : B (66999554588408376419 / 4000000000000000) (16836179499996236064461 / 1000000000000000000) (((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) := bsub sGlobal52_hz66 (sGlobal52_hz67 hc) (by norm_num) (by norm_num)

theorem sGlobal52_hz69 : B (1524735695971823534271 / 125000000000000000) (609894278388729413841 / 50000000000000000) ((s3am 12225 46)^2) := bsq sGlobal52_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal52_hz70 : B (1524735695971823534271 / 62500000000000000) (609894278388729413841 / 25000000000000000) ((2 : ℝ) * ((s3am 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal52_hz69 (by norm_num) (by norm_num)

theorem sGlobal52_hz71 {c : ℝ} (hc : B (121 / 200) (61 / 100) c) : B (10727966279762309 / 15625000000000000) (21566467665709989 / 31250000000000000) ((((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) / ((2 : ℝ) * ((s3am 12225 46)^2))) := bdiv (sGlobal52_hz68 hc) sGlobal52_hz70 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal52_hz72 {c : ℝ} (hc : B (121 / 200) (61 / 100) c) : B (10727966279762309 / 15625000000000000) (21566467665709989 / 31250000000000000) (s3c1 12225 46 c) := by
    convert (sGlobal52_hz71 hc) using 1 <;>
      norm_num [s3c1] <;> ring

theorem sGlobal52_hz73 {c : ℝ} (hc : B (121 / 200) (61 / 100) c) : B (14136537986119283 / 20000000000000000) (708830572026982599 / 1000000000000000000) (kdot c) := bkdot (sGlobal52_hz38 hc) sGlobal52_hz39.1 sGlobal52_hz47.2

theorem sGlobal52_hz74 : B (92611644326401311 / 125000000000000000) (740893154611210491 / 1000000000000000000) (kdot ((10727966279762309 / 15625000000000000))) := by
    constructor
    · apply bkdot_lower (q := (26942122809821587 / 62500000000000000)) (a := (407004080984123761 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (431073964957145391 / 1000000000000000000)) (a := (407004080984123759 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal52_hz75 : B (742445333953168289 / 1000000000000000000) (742445333953168291 / 1000000000000000000) (kdot ((21566467665709989 / 31250000000000000))) := by
    constructor
    · apply bkdot_lower (q := (428185767136503167 / 1000000000000000000)) (a := (50570740421906191 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (214092883568251583 / 500000000000000000)) (a := (202282961687624763 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal52_hz76 {c : ℝ} (hc : B (121 / 200) (61 / 100) c) : B (92611644326401311 / 125000000000000000) (742445333953168291 / 1000000000000000000) (kdot (s3c1 12225 46 c)) := bkdot (sGlobal52_hz72 hc) sGlobal52_hz74.1 sGlobal52_hz75.2

theorem sGlobal52_hz77 {c : ℝ} (hc : B (121 / 200) (61 / 100) c) : B (14641 / 40000) (3721 / 10000) (c^2) := bsq (sGlobal52_hz38 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal52_hz78 {c : ℝ} (hc : B (121 / 200) (61 / 100) c) : B (6279 / 10000) (25359 / 40000) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (sGlobal52_hz77 hc) (by norm_num) (by norm_num)

theorem sGlobal52_hz79 {c : ℝ} (hc : B (121 / 200) (61 / 100) c) : B (792401413426301253 / 1000000000000000000) (796225470579784957 / 1000000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (sGlobal52_hz78 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal52_hz80 : B (39119999999999765769 / 1600000000000000) (3912000000000000489 / 160000000000000) ((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (149450625 : ℝ)) sGlobal52_hz10 (by norm_num) (by norm_num)

theorem sGlobal52_hz81 {c : ℝ} (hc : B (121 / 200) (61 / 100) c) : B (17502832314305497 / 31250000000000000) (70548619471690297 / 125000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (sGlobal52_hz79 hc) (sGlobal52_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal52_hz82 {c : ℝ} (hc : B (121 / 200) (61 / 100) c) : B (13694216002712538858681 / 1000000000000000000) (6899654984331311909057 / 500000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) := bmul sGlobal52_hz80 (sGlobal52_hz81 hc) (by norm_num) (by norm_num)

theorem sGlobal52_hz83 {c : ℝ} (hc : B (121 / 200) (61 / 100) c) : B (342355400067813471467 / 50000000000000000) (6899654984331311909057 / 1000000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) / (2 : ℝ)) := bdiv (sGlobal52_hz82 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal52_hz84 {c : ℝ} (hc : B (121 / 200) (61 / 100) c) : B (342355400067813471467 / 50000000000000000) (6899654984331311909057 / 1000000000000000000) (s3Cpa 12225 c) := by
    convert (sGlobal52_hz83 hc) using 1 <;>
      norm_num [s3Cpa, mA] <;> ring

theorem sGlobal52_hz85 {c : ℝ} (hc : B (121 / 200) (61 / 100) c) : B (252229203719600809 / 1000000000000000000) (126723219458443259 / 500000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (sGlobal52_hz79 hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal52_hz86 {c : ℝ} (hc : B (121 / 200) (61 / 100) c) : B (42763027408010831 / 100000000000000000) (216193324468229693 / 500000000000000000) (c * (kdot c)) := bmul (sGlobal52_hz38 hc) (sGlobal52_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal52_hz87 {c : ℝ} (hc : B (121 / 200) (61 / 100) c) : B (-180157445216858577 / 1000000000000000000) (-5443244848850681 / 31250000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (sGlobal52_hz85 hc) (sGlobal52_hz86 hc) (by norm_num) (by norm_num)

theorem sGlobal52_hz88 {c : ℝ} (hc : B (121 / 200) (61 / 100) c) : B (-4404849535552192758257 / 1000000000000000000) (-2129397384870373657433 / 500000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) := bmul sGlobal52_hz80 (sGlobal52_hz87 hc) (by norm_num) (by norm_num)

theorem sGlobal52_hz89 {c : ℝ} (hc : B (121 / 200) (61 / 100) c) : B (-2202424767776096379129 / 1000000000000000000) (-2129397384870373657433 / 1000000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) / (2 : ℝ)) := bdiv (sGlobal52_hz88 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal52_hz90 {c : ℝ} (hc : B (121 / 200) (61 / 100) c) : B (-2202424767776096379129 / 1000000000000000000) (-2129397384870373657433 / 1000000000000000000) (s3Cpp 12225 c) := by
    convert (sGlobal52_hz89 hc) using 1 <;>
      norm_num [s3Cpp, mA] <;> ring

theorem sGlobal52_hz91 {c : ℝ} (hc : B (121 / 200) (61 / 100) c) : B (6962253111290007137741 / 1000000000000000000) (7014800094265050321283 / 1000000000000000000) ((s3Cpa 12225 c) + (s3r1 12225 46)) := badd (sGlobal52_hz84 hc) sGlobal52_hz33 (by norm_num) (by norm_num)

theorem sGlobal52_hz92 {c : ℝ} (hc : B (121 / 200) (61 / 100) c) : B (63038740945318904037 / 1000000000000000000) (6351452020732968599 / 100000000000000000) (((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) := bdiv (sGlobal52_hz91 hc) sGlobal52_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal52_hz93 {c : ℝ} (hc : B (121 / 200) (61 / 100) c) : B (63161423970812964449 / 1000000000000000000) (63637203232823746413 / 1000000000000000000) ((((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) + (s3e0 12225 46)) := badd (sGlobal52_hz92 hc) sGlobal52_hz16 (by norm_num) (by norm_num)

theorem sGlobal52_hz94 {c : ℝ} (hc : B (121 / 200) (61 / 100) c) : B (63161423970812964449 / 1000000000000000000) (63637203232823746413 / 1000000000000000000) (s3Lam 12225 46 c) := by
    convert (sGlobal52_hz93 hc) using 1 <;>
      norm_num [s3Lam] <;> ring

theorem sGlobal52_hz95 {c : ℝ} (hc : B (121 / 200) (61 / 100) c) : B (-2125661361153604573529 / 1000000000000000000) (-410526795649576276523 / 200000000000000000) ((s3Cpp 12225 c) + (s3rpp 12225 46)) := badd (sGlobal52_hz90 hc) sGlobal52_hz37 (by norm_num) (by norm_num)

theorem sGlobal52_hz96 {c : ℝ} (hc : B (121 / 200) (61 / 100) c) : B (-7890936795765171093 / 5000000000000000) (-1026316989123940691307 / 1000000000000000000) (if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) := bweaken (bfirst (sGlobal52_hz95 hc) (sGlobal52_hz76 hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem sGlobal52_hz97 {c : ℝ} (hc : B (121 / 200) (61 / 100) c) : B (997341369505196636343 / 250000000000000000) (4049693635295713081617 / 1000000000000000000) ((s3Lam 12225 46 c)^2) := bsq (sGlobal52_hz94 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal52_hz98 {c : ℝ} (hc : B (121 / 200) (61 / 100) c) : B (3682856335990949 / 7812500000000000) (476275228237941209 / 1000000000000000000) ((s3c1 12225 46 c)^2) := bsq (sGlobal52_hz72 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal52_hz99 {c : ℝ} (hc : B (121 / 200) (61 / 100) c) : B (523724771762058791 / 1000000000000000000) (4129643664009051 / 7812500000000000) ((1 : ℝ) - ((s3c1 12225 46 c)^2)) := bsub (bpoint (1 : ℝ)) (sGlobal52_hz98 hc) (by norm_num) (by norm_num)

theorem sGlobal52_hz100 {c : ℝ} (hc : B (121 / 200) (61 / 100) c) : B (723688311196235081 / 1000000000000000000) (45440310650396367 / 62500000000000000) (√((1 : ℝ) - ((s3c1 12225 46 c)^2))) := bsqrt (sGlobal52_hz99 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal52_hz101 {c : ℝ} (hc : B (121 / 200) (61 / 100) c) : B (568383470485724061 / 250000000000000000) (1142039568928986129 / 500000000000000000) (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))) := bmul pi_mem (sGlobal52_hz100 hc) (by norm_num) (by norm_num)

theorem sGlobal52_hz102 {c : ℝ} (hc : B (121 / 200) (61 / 100) c) : B (1746596872191585051513 / 1000000000000000000) (890616512790863298357 / 500000000000000000) (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2))))) := bdiv (sGlobal52_hz97 hc) (sGlobal52_hz101 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal52_hz103 {c : ℝ} (hc : B (121 / 200) (61 / 100) c) : B (168409513038550832913 / 1000000000000000000) (754916036457785905407 / 1000000000000000000) ((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) := badd (sGlobal52_hz96 hc) (sGlobal52_hz102 hc) (by norm_num) (by norm_num)

theorem sGlobal52_hz104 : B (3762781186094069 / 250000000000000000) (376278118609407 / 25000000000000000) ((s3e0 12225 46)^2) := bsq sGlobal52_hz16 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal52_hz105 {c : ℝ} (hc : B (121 / 200) (61 / 100) c) : B (168424564163295209189 / 1000000000000000000) (754931087582530281687 / 1000000000000000000) (((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) := badd (sGlobal52_hz103 hc) sGlobal52_hz104 (by norm_num) (by norm_num)

theorem sGlobal52_hz106 {c : ℝ} (hc : B (121 / 200) (61 / 100) c) : B (5173040940363561983 / 25000000000000000) (793428161036654551703 / 1000000000000000000) ((((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) + (s3rs 12225 46 maskSlack)) := badd (sGlobal52_hz105 hc) sGlobal52_hz29 (by norm_num) (by norm_num)

theorem sGlobal52_hz107 {c : ℝ} (hc : B (121 / 200) (61 / 100) c) : B (5173040940363561983 / 25000000000000000) (793428161036654551703 / 1000000000000000000) (s3U 12225 46 maskSlack c) := by
    convert (sGlobal52_hz106 hc) using 1 <;>
      norm_num [s3U] <;> ring

theorem sGlobal52_hz108 {c : ℝ} (hc : B (121 / 200) (61 / 100) c) : B (-2279188174398588653947 / 1000000000000000000) (-2206160791492865463033 / 1000000000000000000) ((s3Cpp 12225 c) - (s3rpp 12225 46)) := bsub (sGlobal52_hz90 hc) sGlobal52_hz37 (by norm_num) (by norm_num)

theorem sGlobal52_hz109 {c : ℝ} (hc : B (121 / 200) (61 / 100) c) : B (-2279188174398588653947 / 1000000000000000000) (-2206160791492865463033 / 1000000000000000000) (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ)) := bweaken (bmin (sGlobal52_hz108 hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem sGlobal52_hz110 {c : ℝ} (hc : B (121 / 200) (61 / 100) c) : B (-1692172625283472124969 / 1000000000000000000) (-1634529428388714075379 / 1000000000000000000) ((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) := bmul (sGlobal52_hz76 hc) (sGlobal52_hz109 hc) (by norm_num) (by norm_num)

theorem sGlobal52_hz111 {c : ℝ} (hc : B (121 / 200) (61 / 100) c) : B (-1692187676408216501249 / 1000000000000000000) (-326908895902691690331 / 200000000000000000) (((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) := bsub (sGlobal52_hz110 hc) sGlobal52_hz104 (by norm_num) (by norm_num)

theorem sGlobal52_hz112 {c : ℝ} (hc : B (121 / 200) (61 / 100) c) : B (-346136949972468154253 / 200000000000000000) (-836520776482352860893 / 500000000000000000) ((((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) - (s3rs 12225 46 maskSlack)) := bsub (sGlobal52_hz111 hc) sGlobal52_hz29 (by norm_num) (by norm_num)

theorem sGlobal52_hz113 {c : ℝ} (hc : B (121 / 200) (61 / 100) c) : B (-346136949972468154253 / 200000000000000000) (-836520776482352860893 / 500000000000000000) (s3L 12225 46 maskSlack c) := by
    convert (sGlobal52_hz112 hc) using 1 <;>
      norm_num [s3L] <;> ring

theorem sGlobal52_hz114 {c : ℝ} (hc : B (121 / 200) (61 / 100) c) : B 0 (793428161036654551703 / 1000000000000000000) |(s3U 12225 46 maskSlack c)| := bweaken (babs (sGlobal52_hz107 hc)) (by norm_num) (by norm_num)

theorem sGlobal52_hz115 {c : ℝ} (hc : B (121 / 200) (61 / 100) c) : B 0 (346136949972468154253 / 200000000000000000) |(s3L 12225 46 maskSlack c)| := bweaken (babs (sGlobal52_hz113 hc)) (by norm_num) (by norm_num)

theorem sGlobal52_hz116 {c : ℝ} (hc : B (121 / 200) (61 / 100) c) : B 0 (346136949972468154253 / 200000000000000000) (max |(s3U 12225 46 maskSlack c)| |(s3L 12225 46 maskSlack c)|) := bweaken (bmax (sGlobal52_hz114 hc) (sGlobal52_hz115 hc)) (by norm_num) (by norm_num)

theorem sGlobal52_hz117 {c : ℝ} (hc : B (121 / 200) (61 / 100) c) : B 0 (346136949972468154253 / 200000000000000000) (s3nks 12225 46 maskSlack c) := by
    convert (sGlobal52_hz116 hc) using 1 <;>
      norm_num [s3nks] <;> ring

theorem sGlobal52 {c : ℝ} (hc : B (121 / 200) (61 / 100) c) :
    0 < s3am 12225 46 ∧ 0 ≤ s3dm 12225 46 c ∧
    s3dm 12225 46 c ^ 2 ≤ 2 * s3ap 12225 46 ^ 2 ∧ s3c1 12225 46 c < 1 ∧
    0 ≤ s3Cpa 12225 c - s3r1 12225 46 ∧
    s3e0 12225 46 ≤ (s3Cpa 12225 c - s3r1 12225 46) / s3ap 12225 46 ∧
    s3nks 12225 46 maskSlack c ≤ 12225 * (14157 / 100000) := by

  refine ⟨lt_of_lt_of_le (by norm_num) sGlobal52_hz14.1,
    le_trans (by norm_num) (sGlobal52_hz64 hc).1, ?_,
    lt_of_le_of_lt (sGlobal52_hz72 hc).2 (by norm_num), ?_, ?_,
    le_trans (sGlobal52_hz117 hc).2 (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (sGlobal52_hz64 hc).1) (sGlobal52_hz64 hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) sGlobal52_hz9.1 2
    nlinarith only [h1, h2]
  · linarith only [(sGlobal52_hz84 hc).1, sGlobal52_hz33.2]
  · have hap : 0 < s3ap 12225 46 := lt_of_lt_of_le (by norm_num) sGlobal52_hz9.1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul sGlobal52_hz16.2 sGlobal52_hz9.2 (le_trans (by norm_num) sGlobal52_hz9.1) (by norm_num)
    linarith only [h, (sGlobal52_hz84 hc).1, sGlobal52_hz33.2]

end BstLean.Part255
