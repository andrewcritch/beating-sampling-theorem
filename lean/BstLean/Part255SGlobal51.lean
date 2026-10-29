import BstLean.Part255SGlobal47
import BstLean.Part255Numeric10
namespace BstLean.Part255
open Real BstLean.Part130 BstLean.Part182 BstLean.Part197 BstLean.Part246
theorem sGlobal51_hz0 : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal51_hz1 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) ((√(23 : ℝ)) / (12225 : ℝ)) := bdiv sGlobal51_hz0 (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal51_hz2 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) maskSlack := by
    convert sGlobal51_hz1 using 1 <;>
      norm_num [maskSlack] <;> ring

theorem sGlobal51_hz3 : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal51_hz4 : B (6395294793910793 / 500000000000000000) (12790589587821587 / 1000000000000000000) (√((2 / 12225) : ℝ)) := bsqrt (bpoint ((2 / 12225) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal51_hz5 : B (7230130686979 / 62500000000000000) (23136418198333 / 200000000000000000) (√((2 / 149450625) : ℝ)) := bsqrt (bpoint ((2 / 149450625) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal51_hz6 : B (2211334438749598093 / 20000000000000000) (110566721937479904651 / 1000000000000000000) (√(12225 : ℝ)) := bsqrt (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal51_hz7 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))) := bmul sGlobal51_hz3 sGlobal51_hz4 (by norm_num) (by norm_num)

theorem sGlobal51_hz8 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) ((√(12225 : ℝ)) + ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := badd sGlobal51_hz6 sGlobal51_hz7 (by norm_num) (by norm_num)

theorem sGlobal51_hz9 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) (s3ap 12225 46) := by
    convert sGlobal51_hz8 using 1 <;>
      norm_num [s3ap, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal51_hz10 : B (163599182004089 / 1000000000000000000) (16359918200409 / 100000000000000000) ((2 : ℝ) / (12225 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal51_hz11 : B (1222499983640081799591 / 100000000000000000) (12224999836400817995911 / 1000000000000000000) ((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ))) := bsub (bpoint (12225 : ℝ)) sGlobal51_hz10 (by norm_num) (by norm_num)

theorem sGlobal51_hz12 : B (110566721197658827907 / 1000000000000000000) (27641680299414706977 / 250000000000000000) (√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) := bsqrt sGlobal51_hz11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal51_hz13 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) ((√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) - ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bsub sGlobal51_hz12 sGlobal51_hz7 (by norm_num) (by norm_num)

theorem sGlobal51_hz14 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) (s3am 12225 46) := by
    convert sGlobal51_hz13 using 1 <;>
      norm_num [s3am, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal51_hz15 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√((2 / 12225) : ℝ)) * (√(92 : ℝ))) := bmul sGlobal51_hz4 sGlobal51_hz3 (by norm_num) (by norm_num)

theorem sGlobal51_hz16 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) (s3e0 12225 46) := by
    convert sGlobal51_hz15 using 1 <;>
      norm_num [s3e0, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal51_hz17 : B (250196148528560847 / 500000000000000000) (100078459411424339 / 200000000000000000) (((1 / 2) : ℝ) + maskSlack) := badd (bpoint ((1 / 2) : ℝ)) sGlobal51_hz2 (by norm_num) (by norm_num)

theorem sGlobal51_hz18 : B (59827153232297998295487 / 800000000000000) (23930861292919199366019 / 320000000000000) ((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack)) := bmul (bpoint (149450625 : ℝ)) sGlobal51_hz17 (by norm_num) (by norm_num)

theorem sGlobal51_hz19 : B (1729554180017180009583 / 200000000000000000) (8647770900085900056557 / 1000000000000000000) (√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) := bsqrt sGlobal51_hz18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal51_hz20 : B (4328681281566262743499 / 500000000000000000) (8657362563132525495641 / 1000000000000000000) ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))) := badd sGlobal51_hz19 sGlobal51_hz3 (by norm_num) (by norm_num)

theorem sGlobal51_hz21 : B (110732771457999278473 / 1000000000000000000) (55366385728999643621 / 500000000000000000) ((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ)))) := bmul sGlobal51_hz4 sGlobal51_hz20 (by norm_num) (by norm_num)

theorem sGlobal51_hz22 : B (209099159 / 15625000000000000) (13382346177 / 1000000000000000000) ((2 : ℝ) / (149450625 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (149450625 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal51_hz23 : B (2452349334953899930479 / 200000000000000000) (12261746674769501594427 / 1000000000000000000) (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2) := bsq sGlobal51_hz21 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal51_hz24 : B (82045469362091 / 500000000000000000) (32818187747289 / 200000000000000000) (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2)) := bmul sGlobal51_hz22 sGlobal51_hz23 (by norm_num) (by norm_num)

theorem sGlobal51_hz25 : B (82045469362091 / 250000000000000000) (32818187747289 / 100000000000000000) ((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) := bmul (bpoint (2 : ℝ)) sGlobal51_hz24 (by norm_num) (by norm_num)

theorem sGlobal51_hz26 : B (117258080744995992792057 / 1000000000000000000) (58629040372497996396029 / 500000000000000000) (√(13749457500 : ℝ)) := bsqrt (bpoint (13749457500 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal51_hz27 : B (117304080744995992792057 / 1000000000000000000) (58652040372497996396029 / 500000000000000000) ((√(13749457500 : ℝ)) + (46 : ℝ)) := badd sGlobal51_hz26 (bpoint (46 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal51_hz28 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal51_hz25 sGlobal51_hz27 (by norm_num) (by norm_num)

theorem sGlobal51_hz29 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (s3rs 12225 46 maskSlack) := by
    convert sGlobal51_hz28 using 1 <;>
      norm_num [s3rs, s3pp, s3K, mA, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal51_hz30 : B (490797546012267 / 1000000000000000000) (49079754601227 / 100000000000000000) ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (3 : ℝ)) sGlobal51_hz10 (by norm_num) (by norm_num)

theorem sGlobal51_hz31 : B (490797546012267 / 500000000000000000) (49079754601227 / 50000000000000000) ((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal51_hz30 (by norm_num) (by norm_num)

theorem sGlobal51_hz32 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal51_hz31 sGlobal51_hz27 (by norm_num) (by norm_num)

theorem sGlobal51_hz33 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (s3r1 12225 46) := by
    convert sGlobal51_hz32 using 1 <;>
      norm_num [s3r1, mA] <;> ring

theorem sGlobal51_hz34 : B (163599182004089 / 500000000000000000) (16359918200409 / 50000000000000000) ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (2 : ℝ)) sGlobal51_hz10 (by norm_num) (by norm_num)

theorem sGlobal51_hz35 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal51_hz34 (by norm_num) (by norm_num)

theorem sGlobal51_hz36 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal51_hz35 sGlobal51_hz27 (by norm_num) (by norm_num)

theorem sGlobal51_hz37 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (s3rpp 12225 46) := by
    convert sGlobal51_hz36 using 1 <;>
      norm_num [s3rpp, mA] <;> ring

theorem sGlobal51_hz38 {c : ℝ} (hc : B (3 / 5) (121 / 200) c) : B (3 / 5) (121 / 200) c := hc

theorem sGlobal51_hz39 : B (352416382349566723 / 500000000000000000) (352416382349566747 / 500000000000000000) (kdot ((3 / 5))) := by
    constructor
    · apply bkdot_lower (q := (1 / 2)) (a := (115911902250201531 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (1 / 2)) (a := (9272952180016121 / 20000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal51_hz40 : B (9 / 25) (9 / 25) (((3 / 5) : ℝ)^2) := bsq (bpoint ((3 / 5) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal51_hz41 : B (16 / 25) (16 / 25) ((1 : ℝ) - (((3 / 5) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal51_hz40 (by norm_num) (by norm_num)

theorem sGlobal51_hz42 : B (4 / 5) (4 / 5) (√((1 : ℝ) - (((3 / 5) : ℝ)^2))) := bsqrt sGlobal51_hz41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal51_hz43 : B (254647908947032537 / 1000000000000000000) (127323954473516269 / 500000000000000000) ((√((1 : ℝ) - (((3 / 5) : ℝ)^2))) / Real.pi) := bdiv sGlobal51_hz42 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal51_hz44 : B (422899658819480067 / 1000000000000000000) (422899658819480097 / 1000000000000000000) (((3 / 5) : ℝ) * (kdot ((3 / 5)))) := bmul (bpoint ((3 / 5) : ℝ)) sGlobal51_hz39 (by norm_num) (by norm_num)

theorem sGlobal51_hz45 : B (169386891941628151 / 250000000000000000) (135509513553302527 / 200000000000000000) (((√((1 : ℝ) - (((3 / 5) : ℝ)^2))) / Real.pi) + (((3 / 5) : ℝ) * (kdot ((3 / 5))))) := badd sGlobal51_hz43 sGlobal51_hz44 (by norm_num) (by norm_num)

theorem sGlobal51_hz46 : B (169386891941628151 / 250000000000000000) (135509513553302527 / 200000000000000000) (kappa ((3 / 5))) := by rw [kappa_eq]; exact sGlobal51_hz45

theorem sGlobal51_hz47 : B (14136537986119283 / 20000000000000000) (88353362413245523 / 125000000000000000) (kdot ((121 / 200))) := by
    constructor
    · apply bkdot_lower (q := (19843625435010217 / 40000000000000000)) (a := (460515229685261869 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (3875708092775433 / 7812500000000000)) (a := (230257614842630909 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal51_hz48 : B (14641 / 40000) (14641 / 40000) (((121 / 200) : ℝ)^2) := bsq (bpoint ((121 / 200) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal51_hz49 : B (25359 / 40000) (25359 / 40000) ((1 : ℝ) - (((121 / 200) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal51_hz48 (by norm_num) (by norm_num)

theorem sGlobal51_hz50 : B (199056367644946239 / 250000000000000000) (796225470579784957 / 1000000000000000000) (√((1 : ℝ) - (((121 / 200) : ℝ)^2))) := bsqrt sGlobal51_hz49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal51_hz51 : B (253446438916886517 / 1000000000000000000) (126723219458443259 / 500000000000000000) ((√((1 : ℝ) - (((121 / 200) : ℝ)^2))) / Real.pi) := bdiv sGlobal51_hz50 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal51_hz52 : B (42763027408010831 / 100000000000000000) (106907568520027083 / 250000000000000000) (((121 / 200) : ℝ) * (kdot ((121 / 200)))) := bmul (bpoint ((121 / 200) : ℝ)) sGlobal51_hz47 (by norm_num) (by norm_num)

theorem sGlobal51_hz53 : B (681076712996994827 / 1000000000000000000) (13621534259939897 / 20000000000000000) (((√((1 : ℝ) - (((121 / 200) : ℝ)^2))) / Real.pi) + (((121 / 200) : ℝ) * (kdot ((121 / 200))))) := badd sGlobal51_hz51 sGlobal51_hz52 (by norm_num) (by norm_num)

theorem sGlobal51_hz54 : B (681076712996994827 / 1000000000000000000) (13621534259939897 / 20000000000000000) (kappa ((121 / 200))) := by rw [kappa_eq]; exact sGlobal51_hz53

theorem sGlobal51_hz55 {c : ℝ} (hc : B (3 / 5) (121 / 200) c) : B (169386891941628151 / 250000000000000000) (13621534259939897 / 20000000000000000) (kappa c) := bkappa (sGlobal51_hz38 hc) (by norm_num) (by norm_num) sGlobal51_hz46.1 sGlobal51_hz54.2

theorem sGlobal51_hz56 : B 24450 24450 ((2 : ℝ) * (12225 : ℝ)) := bmul (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal51_hz57 {c : ℝ} (hc : B (3 / 5) (121 / 200) c) : B (6378465740060103 / 20000000000000000) (80613108058371849 / 250000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (sGlobal51_hz55 hc) (by norm_num) (by norm_num)

theorem sGlobal51_hz58 {c : ℝ} (hc : B (3 / 5) (121 / 200) c) : B (3119069746889390367 / 400000000000000) (39419809840543834161 / 5000000000000000) (((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) := bmul sGlobal51_hz56 (sGlobal51_hz57 hc) (by norm_num) (by norm_num)

theorem sGlobal51_hz59 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (4 : ℝ)) sGlobal51_hz10 (by norm_num) (by norm_num)

theorem sGlobal51_hz60 {c : ℝ} (hc : B (3 / 5) (121 / 200) c) : B (389883685641337395057 / 50000000000000000) (1970990328428009703961 / 250000000000000000) ((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bsub (sGlobal51_hz58 hc) sGlobal51_hz59 (by norm_num) (by norm_num)

theorem sGlobal51_hz61 {c : ℝ} (hc : B (3 / 5) (121 / 200) c) : B (88304437673464338193 / 1000000000000000000) (693684950572930879 / 7812500000000000) (√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) := bsqrt (sGlobal51_hz60 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal51_hz62 : B (30670756373515103 / 125000000000000000) (122683025494060423 / 500000000000000000) ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal51_hz7 (by norm_num) (by norm_num)

theorem sGlobal51_hz63 {c : ℝ} (hc : B (3 / 5) (121 / 200) c) : B (88059071622476217347 / 1000000000000000000) (11068288452793378961 / 125000000000000000) ((√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) - ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))))) := bsub (sGlobal51_hz61 hc) sGlobal51_hz62 (by norm_num) (by norm_num)

theorem sGlobal51_hz64 {c : ℝ} (hc : B (3 / 5) (121 / 200) c) : B (88059071622476217347 / 1000000000000000000) (11068288452793378961 / 125000000000000000) (s3dm 12225 46 c) := by
    convert (sGlobal51_hz63 hc) using 1 <;>
      norm_num [s3dm, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal51_hz65 : B (6126072185528622723889 / 500000000000000000) (2450428874211449090087 / 200000000000000000) ((s3ap 12225 46)^2) := bsq sGlobal51_hz9 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal51_hz66 : B (6126072185528622723889 / 250000000000000000) (2450428874211449090087 / 100000000000000000) ((2 : ℝ) * ((s3ap 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal51_hz65 (by norm_num) (by norm_num)

theorem sGlobal51_hz67 {c : ℝ} (hc : B (3 / 5) (121 / 200) c) : B (3877200047506198112909 / 500000000000000000) (1568089718710262408817 / 200000000000000000) ((s3dm 12225 46 c)^2) := bsq (sGlobal51_hz64 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal51_hz68 {c : ℝ} (hc : B (3 / 5) (121 / 200) c) : B (16663840148563178851471 / 1000000000000000000) (4187472161775523668763 / 250000000000000000) (((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) := bsub sGlobal51_hz66 (sGlobal51_hz67 hc) (by norm_num) (by norm_num)

theorem sGlobal51_hz69 : B (1524735695971823534271 / 125000000000000000) (609894278388729413841 / 50000000000000000) ((s3am 12225 46)^2) := bsq sGlobal51_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal51_hz70 : B (1524735695971823534271 / 62500000000000000) (609894278388729413841 / 25000000000000000) ((2 : ℝ) * ((s3am 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal51_hz69 (by norm_num) (by norm_num)

theorem sGlobal51_hz71 {c : ℝ} (hc : B (3 / 5) (121 / 200) c) : B (683062652784148479 / 1000000000000000000) (686589841904787801 / 1000000000000000000) ((((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) / ((2 : ℝ) * ((s3am 12225 46)^2))) := bdiv (sGlobal51_hz68 hc) sGlobal51_hz70 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal51_hz72 {c : ℝ} (hc : B (3 / 5) (121 / 200) c) : B (683062652784148479 / 1000000000000000000) (686589841904787801 / 1000000000000000000) (s3c1 12225 46 c) := by
    convert (sGlobal51_hz71 hc) using 1 <;>
      norm_num [s3c1] <;> ring

theorem sGlobal51_hz73 {c : ℝ} (hc : B (3 / 5) (121 / 200) c) : B (352416382349566723 / 500000000000000000) (88353362413245523 / 125000000000000000) (kdot c) := bkdot (sGlobal51_hz38 hc) sGlobal51_hz39.1 sGlobal51_hz47.2

theorem sGlobal51_hz74 : B (369676209998249907 / 500000000000000000) (739352419996499817 / 1000000000000000000) (kdot ((683062652784148479 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (17357875100349641 / 40000000000000000)) (a := (204712130628738519 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (13560839922148157 / 31250000000000000)) (a := (102356065314369259 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal51_hz75 : B (1481786309222421 / 2000000000000000) (370446577305605251 / 500000000000000000) (kdot ((686589841904787801 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (431073964957145371 / 1000000000000000000)) (a := (407004080984123743 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (43107396495714537 / 100000000000000000)) (a := (407004080984123741 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal51_hz76 {c : ℝ} (hc : B (3 / 5) (121 / 200) c) : B (369676209998249907 / 500000000000000000) (370446577305605251 / 500000000000000000) (kdot (s3c1 12225 46 c)) := bkdot (sGlobal51_hz72 hc) sGlobal51_hz74.1 sGlobal51_hz75.2

theorem sGlobal51_hz77 {c : ℝ} (hc : B (3 / 5) (121 / 200) c) : B (9 / 25) (14641 / 40000) (c^2) := bsq (sGlobal51_hz38 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal51_hz78 {c : ℝ} (hc : B (3 / 5) (121 / 200) c) : B (25359 / 40000) (16 / 25) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (sGlobal51_hz77 hc) (by norm_num) (by norm_num)

theorem sGlobal51_hz79 {c : ℝ} (hc : B (3 / 5) (121 / 200) c) : B (199056367644946239 / 250000000000000000) (4 / 5) (√((1 : ℝ) - (c^2))) := bsqrt (sGlobal51_hz78 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal51_hz80 : B (39119999999999765769 / 1600000000000000) (3912000000000000489 / 160000000000000) ((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (149450625 : ℝ)) sGlobal51_hz10 (by norm_num) (by norm_num)

theorem sGlobal51_hz81 {c : ℝ} (hc : B (3 / 5) (121 / 200) c) : B (56120579975261837 / 100000000000000000) (141365379861192837 / 250000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (sGlobal51_hz79 hc) (sGlobal51_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal51_hz82 {c : ℝ} (hc : B (3 / 5) (121 / 200) c) : B (13721481803951436989127 / 1000000000000000000) (1728191768803082648349 / 125000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) := bmul sGlobal51_hz80 (sGlobal51_hz81 hc) (by norm_num) (by norm_num)

theorem sGlobal51_hz83 {c : ℝ} (hc : B (3 / 5) (121 / 200) c) : B (6860740901975718494563 / 1000000000000000000) (1728191768803082648349 / 250000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) / (2 : ℝ)) := bdiv (sGlobal51_hz82 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal51_hz84 {c : ℝ} (hc : B (3 / 5) (121 / 200) c) : B (6860740901975718494563 / 1000000000000000000) (1728191768803082648349 / 250000000000000000) (s3Cpa 12225 c) := by
    convert (sGlobal51_hz83 hc) using 1 <;>
      norm_num [s3Cpa, mA] <;> ring

theorem sGlobal51_hz85 {c : ℝ} (hc : B (3 / 5) (121 / 200) c) : B (253446438916886517 / 1000000000000000000) (127323954473516269 / 500000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (sGlobal51_hz79 hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal51_hz86 {c : ℝ} (hc : B (3 / 5) (121 / 200) c) : B (422899658819480067 / 1000000000000000000) (106907568520027083 / 250000000000000000) (c * (kdot c)) := bmul (sGlobal51_hz38 hc) (sGlobal51_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal51_hz87 {c : ℝ} (hc : B (3 / 5) (121 / 200) c) : B (-34836767032644363 / 200000000000000000) (-168251749872447529 / 1000000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (sGlobal51_hz85 hc) (sGlobal51_hz86 hc) (by norm_num) (by norm_num)

theorem sGlobal51_hz88 {c : ℝ} (hc : B (3 / 5) (121 / 200) c) : B (-42587947697407739091 / 10000000000000000) (-205687764219065872647 / 50000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) := bmul sGlobal51_hz80 (sGlobal51_hz87 hc) (by norm_num) (by norm_num)

theorem sGlobal51_hz89 {c : ℝ} (hc : B (3 / 5) (121 / 200) c) : B (-42587947697407739091 / 20000000000000000) (-205687764219065872647 / 100000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) / (2 : ℝ)) := bdiv (sGlobal51_hz88 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal51_hz90 {c : ℝ} (hc : B (3 / 5) (121 / 200) c) : B (-42587947697407739091 / 20000000000000000) (-205687764219065872647 / 100000000000000000) (s3Cpp 12225 c) := by
    convert (sGlobal51_hz89 hc) using 1 <;>
      norm_num [s3Cpp, mA] <;> ring

theorem sGlobal51_hz91 {c : ℝ} (hc : B (3 / 5) (121 / 200) c) : B (1743971502977364050741 / 250000000000000000) (3513956092573034502811 / 500000000000000000) ((s3Cpa 12225 c) + (s3r1 12225 46)) := badd (sGlobal51_hz84 hc) sGlobal51_hz33 (by norm_num) (by norm_num)

theorem sGlobal51_hz92 {c : ℝ} (hc : B (3 / 5) (121 / 200) c) : B (15790544531328967009 / 250000000000000000) (63633241788847549461 / 1000000000000000000) (((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) := bdiv (sGlobal51_hz91 hc) sGlobal51_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal51_hz93 {c : ℝ} (hc : B (3 / 5) (121 / 200) c) : B (247206488870351283 / 3906250000000000) (15938981203585402471 / 250000000000000000) ((((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) + (s3e0 12225 46)) := badd (sGlobal51_hz92 hc) sGlobal51_hz16 (by norm_num) (by norm_num)

theorem sGlobal51_hz94 {c : ℝ} (hc : B (3 / 5) (121 / 200) c) : B (247206488870351283 / 3906250000000000) (15938981203585402471 / 250000000000000000) (s3Lam 12225 46 c) := by
    convert (sGlobal51_hz93 hc) using 1 <;>
      norm_num [s3Lam] <;> ring

theorem sGlobal51_hz95 {c : ℝ} (hc : B (3 / 5) (121 / 200) c) : B (-41052679564957902979 / 20000000000000000) (-495028558892041612913 / 250000000000000000) ((s3Cpp 12225 c) + (s3rpp 12225 46)) := badd (sGlobal51_hz90 hc) sGlobal51_hz37 (by norm_num) (by norm_num)

theorem sGlobal51_hz96 {c : ℝ} (hc : B (3 / 5) (121 / 200) c) : B (-304156492681248375007 / 200000000000000000) (-495028558892041612913 / 500000000000000000) (if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) := bweaken (bfirst (sGlobal51_hz95 hc) (sGlobal51_hz76 hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem sGlobal51_hz97 {c : ℝ} (hc : B (3 / 5) (121 / 200) c) : B (2002486825438645870623 / 500000000000000000) (4064817948931980242757 / 1000000000000000000) ((s3Lam 12225 46 c)^2) := bsq (sGlobal51_hz94 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal51_hz98 {c : ℝ} (hc : B (3 / 5) (121 / 200) c) : B (466574587628518183 / 1000000000000000000) (471405611006841507 / 1000000000000000000) ((s3c1 12225 46 c)^2) := bsq (sGlobal51_hz72 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal51_hz99 {c : ℝ} (hc : B (3 / 5) (121 / 200) c) : B (528594388993158493 / 1000000000000000000) (533425412371481817 / 1000000000000000000) ((1 : ℝ) - ((s3c1 12225 46 c)^2)) := bsub (bpoint (1 : ℝ)) (sGlobal51_hz98 hc) (by norm_num) (by norm_num)

theorem sGlobal51_hz100 {c : ℝ} (hc : B (3 / 5) (121 / 200) c) : B (727044970406341847 / 1000000000000000000) (730359782827259607 / 1000000000000000000) (√((1 : ℝ) - ((s3c1 12225 46 c)^2))) := bsqrt (sGlobal51_hz99 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal51_hz101 {c : ℝ} (hc : B (3 / 5) (121 / 200) c) : B (1142039568928986089 / 500000000000000000) (573623232051888903 / 250000000000000000) (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))) := bmul pi_mem (sGlobal51_hz100 hc) (by norm_num) (by norm_num)

theorem sGlobal51_hz102 {c : ℝ} (hc : B (3 / 5) (121 / 200) c) : B (1745472213769668758677 / 1000000000000000000) (177963096004808277881 / 100000000000000000) (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2))))) := bdiv (sGlobal51_hz97 hc) (sGlobal51_hz101 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal51_hz103 {c : ℝ} (hc : B (3 / 5) (121 / 200) c) : B (112344875181713441821 / 500000000000000000) (98696730282999944123 / 125000000000000000) ((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) := badd (sGlobal51_hz96 hc) (sGlobal51_hz102 hc) (by norm_num) (by norm_num)

theorem sGlobal51_hz104 : B (3762781186094069 / 250000000000000000) (376278118609407 / 25000000000000000) ((s3e0 12225 46)^2) := bsq sGlobal51_hz16 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal51_hz105 {c : ℝ} (hc : B (3 / 5) (121 / 200) c) : B (112352400744085629959 / 500000000000000000) (49349305836796495579 / 62500000000000000) (((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) := badd (sGlobal51_hz103 hc) sGlobal51_hz104 (by norm_num) (by norm_num)

theorem sGlobal51_hz106 {c : ℝ} (hc : B (3 / 5) (121 / 200) c) : B (263201874939418530049 / 1000000000000000000) (10351074585535852491 / 12500000000000000) ((((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) + (s3rs 12225 46 maskSlack)) := badd (sGlobal51_hz105 hc) sGlobal51_hz29 (by norm_num) (by norm_num)

theorem sGlobal51_hz107 {c : ℝ} (hc : B (3 / 5) (121 / 200) c) : B (263201874939418530049 / 1000000000000000000) (10351074585535852491 / 12500000000000000) (s3U 12225 46 maskSlack c) := by
    convert (sGlobal51_hz106 hc) using 1 <;>
      norm_num [s3U] <;> ring

theorem sGlobal51_hz108 {c : ℝ} (hc : B (3 / 5) (121 / 200) c) : B (-275770098936609903671 / 125000000000000000) (-213364104881315053207 / 100000000000000000) ((s3Cpp 12225 c) - (s3rpp 12225 46)) := bsub (sGlobal51_hz90 hc) sGlobal51_hz37 (by norm_num) (by norm_num)

theorem sGlobal51_hz109 {c : ℝ} (hc : B (3 / 5) (121 / 200) c) : B (-275770098936609903671 / 125000000000000000) (-213364104881315053207 / 100000000000000000) (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ)) := bweaken (bmin (sGlobal51_hz108 hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem sGlobal51_hz110 {c : ℝ} (hc : B (3 / 5) (121 / 200) c) : B (-1634529428388724305649 / 1000000000000000000) (-788756336421936416591 / 500000000000000000) ((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) := bmul (sGlobal51_hz76 hc) (sGlobal51_hz109 hc) (by norm_num) (by norm_num)

theorem sGlobal51_hz111 {c : ℝ} (hc : B (3 / 5) (121 / 200) c) : B (-1634544479513468681929 / 1000000000000000000) (-788763861984308604729 / 500000000000000000) (((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) := bsub (sGlobal51_hz110 hc) sGlobal51_hz104 (by norm_num) (by norm_num)

theorem sGlobal51_hz112 {c : ℝ} (hc : B (3 / 5) (121 / 200) c) : B (-334608310593518590389 / 200000000000000000) (-1616024797419864479589 / 1000000000000000000) ((((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) - (s3rs 12225 46 maskSlack)) := bsub (sGlobal51_hz111 hc) sGlobal51_hz29 (by norm_num) (by norm_num)

theorem sGlobal51_hz113 {c : ℝ} (hc : B (3 / 5) (121 / 200) c) : B (-334608310593518590389 / 200000000000000000) (-1616024797419864479589 / 1000000000000000000) (s3L 12225 46 maskSlack c) := by
    convert (sGlobal51_hz112 hc) using 1 <;>
      norm_num [s3L] <;> ring

theorem sGlobal51_hz114 {c : ℝ} (hc : B (3 / 5) (121 / 200) c) : B 0 (10351074585535852491 / 12500000000000000) |(s3U 12225 46 maskSlack c)| := bweaken (babs (sGlobal51_hz107 hc)) (by norm_num) (by norm_num)

theorem sGlobal51_hz115 {c : ℝ} (hc : B (3 / 5) (121 / 200) c) : B 0 (334608310593518590389 / 200000000000000000) |(s3L 12225 46 maskSlack c)| := bweaken (babs (sGlobal51_hz113 hc)) (by norm_num) (by norm_num)

theorem sGlobal51_hz116 {c : ℝ} (hc : B (3 / 5) (121 / 200) c) : B 0 (334608310593518590389 / 200000000000000000) (max |(s3U 12225 46 maskSlack c)| |(s3L 12225 46 maskSlack c)|) := bweaken (bmax (sGlobal51_hz114 hc) (sGlobal51_hz115 hc)) (by norm_num) (by norm_num)

theorem sGlobal51_hz117 {c : ℝ} (hc : B (3 / 5) (121 / 200) c) : B 0 (334608310593518590389 / 200000000000000000) (s3nks 12225 46 maskSlack c) := by
    convert (sGlobal51_hz116 hc) using 1 <;>
      norm_num [s3nks] <;> ring

theorem sGlobal51 {c : ℝ} (hc : B (3 / 5) (121 / 200) c) :
    0 < s3am 12225 46 ∧ 0 ≤ s3dm 12225 46 c ∧
    s3dm 12225 46 c ^ 2 ≤ 2 * s3ap 12225 46 ^ 2 ∧ s3c1 12225 46 c < 1 ∧
    0 ≤ s3Cpa 12225 c - s3r1 12225 46 ∧
    s3e0 12225 46 ≤ (s3Cpa 12225 c - s3r1 12225 46) / s3ap 12225 46 ∧
    s3nks 12225 46 maskSlack c ≤ 12225 * (27371 / 200000) := by

  refine ⟨lt_of_lt_of_le (by norm_num) sGlobal51_hz14.1,
    le_trans (by norm_num) (sGlobal51_hz64 hc).1, ?_,
    lt_of_le_of_lt (sGlobal51_hz72 hc).2 (by norm_num), ?_, ?_,
    le_trans (sGlobal51_hz117 hc).2 (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (sGlobal51_hz64 hc).1) (sGlobal51_hz64 hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) sGlobal51_hz9.1 2
    nlinarith only [h1, h2]
  · linarith only [(sGlobal51_hz84 hc).1, sGlobal51_hz33.2]
  · have hap : 0 < s3ap 12225 46 := lt_of_lt_of_le (by norm_num) sGlobal51_hz9.1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul sGlobal51_hz16.2 sGlobal51_hz9.2 (le_trans (by norm_num) sGlobal51_hz9.1) (by norm_num)
    linarith only [h, (sGlobal51_hz84 hc).1, sGlobal51_hz33.2]

end BstLean.Part255
