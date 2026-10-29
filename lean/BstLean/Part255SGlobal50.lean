import BstLean.Part255SGlobal46
import BstLean.Part255Numeric10
namespace BstLean.Part255
open Real BstLean.Part130 BstLean.Part182 BstLean.Part197 BstLean.Part246
theorem sGlobal50_hz0 : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal50_hz1 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) ((√(23 : ℝ)) / (12225 : ℝ)) := bdiv sGlobal50_hz0 (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal50_hz2 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) maskSlack := by
    convert sGlobal50_hz1 using 1 <;>
      norm_num [maskSlack] <;> ring

theorem sGlobal50_hz3 : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal50_hz4 : B (6395294793910793 / 500000000000000000) (12790589587821587 / 1000000000000000000) (√((2 / 12225) : ℝ)) := bsqrt (bpoint ((2 / 12225) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal50_hz5 : B (7230130686979 / 62500000000000000) (23136418198333 / 200000000000000000) (√((2 / 149450625) : ℝ)) := bsqrt (bpoint ((2 / 149450625) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal50_hz6 : B (2211334438749598093 / 20000000000000000) (110566721937479904651 / 1000000000000000000) (√(12225 : ℝ)) := bsqrt (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal50_hz7 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))) := bmul sGlobal50_hz3 sGlobal50_hz4 (by norm_num) (by norm_num)

theorem sGlobal50_hz8 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) ((√(12225 : ℝ)) + ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := badd sGlobal50_hz6 sGlobal50_hz7 (by norm_num) (by norm_num)

theorem sGlobal50_hz9 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) (s3ap 12225 46) := by
    convert sGlobal50_hz8 using 1 <;>
      norm_num [s3ap, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal50_hz10 : B (163599182004089 / 1000000000000000000) (16359918200409 / 100000000000000000) ((2 : ℝ) / (12225 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal50_hz11 : B (1222499983640081799591 / 100000000000000000) (12224999836400817995911 / 1000000000000000000) ((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ))) := bsub (bpoint (12225 : ℝ)) sGlobal50_hz10 (by norm_num) (by norm_num)

theorem sGlobal50_hz12 : B (110566721197658827907 / 1000000000000000000) (27641680299414706977 / 250000000000000000) (√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) := bsqrt sGlobal50_hz11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal50_hz13 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) ((√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) - ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bsub sGlobal50_hz12 sGlobal50_hz7 (by norm_num) (by norm_num)

theorem sGlobal50_hz14 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) (s3am 12225 46) := by
    convert sGlobal50_hz13 using 1 <;>
      norm_num [s3am, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal50_hz15 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√((2 / 12225) : ℝ)) * (√(92 : ℝ))) := bmul sGlobal50_hz4 sGlobal50_hz3 (by norm_num) (by norm_num)

theorem sGlobal50_hz16 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) (s3e0 12225 46) := by
    convert sGlobal50_hz15 using 1 <;>
      norm_num [s3e0, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal50_hz17 : B (250196148528560847 / 500000000000000000) (100078459411424339 / 200000000000000000) (((1 / 2) : ℝ) + maskSlack) := badd (bpoint ((1 / 2) : ℝ)) sGlobal50_hz2 (by norm_num) (by norm_num)

theorem sGlobal50_hz18 : B (59827153232297998295487 / 800000000000000) (23930861292919199366019 / 320000000000000) ((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack)) := bmul (bpoint (149450625 : ℝ)) sGlobal50_hz17 (by norm_num) (by norm_num)

theorem sGlobal50_hz19 : B (1729554180017180009583 / 200000000000000000) (8647770900085900056557 / 1000000000000000000) (√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) := bsqrt sGlobal50_hz18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal50_hz20 : B (4328681281566262743499 / 500000000000000000) (8657362563132525495641 / 1000000000000000000) ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))) := badd sGlobal50_hz19 sGlobal50_hz3 (by norm_num) (by norm_num)

theorem sGlobal50_hz21 : B (110732771457999278473 / 1000000000000000000) (55366385728999643621 / 500000000000000000) ((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ)))) := bmul sGlobal50_hz4 sGlobal50_hz20 (by norm_num) (by norm_num)

theorem sGlobal50_hz22 : B (209099159 / 15625000000000000) (13382346177 / 1000000000000000000) ((2 : ℝ) / (149450625 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (149450625 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal50_hz23 : B (2452349334953899930479 / 200000000000000000) (12261746674769501594427 / 1000000000000000000) (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2) := bsq sGlobal50_hz21 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal50_hz24 : B (82045469362091 / 500000000000000000) (32818187747289 / 200000000000000000) (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2)) := bmul sGlobal50_hz22 sGlobal50_hz23 (by norm_num) (by norm_num)

theorem sGlobal50_hz25 : B (82045469362091 / 250000000000000000) (32818187747289 / 100000000000000000) ((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) := bmul (bpoint (2 : ℝ)) sGlobal50_hz24 (by norm_num) (by norm_num)

theorem sGlobal50_hz26 : B (117258080744995992792057 / 1000000000000000000) (58629040372497996396029 / 500000000000000000) (√(13749457500 : ℝ)) := bsqrt (bpoint (13749457500 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal50_hz27 : B (117304080744995992792057 / 1000000000000000000) (58652040372497996396029 / 500000000000000000) ((√(13749457500 : ℝ)) + (46 : ℝ)) := badd sGlobal50_hz26 (bpoint (46 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal50_hz28 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal50_hz25 sGlobal50_hz27 (by norm_num) (by norm_num)

theorem sGlobal50_hz29 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (s3rs 12225 46 maskSlack) := by
    convert sGlobal50_hz28 using 1 <;>
      norm_num [s3rs, s3pp, s3K, mA, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal50_hz30 : B (490797546012267 / 1000000000000000000) (49079754601227 / 100000000000000000) ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (3 : ℝ)) sGlobal50_hz10 (by norm_num) (by norm_num)

theorem sGlobal50_hz31 : B (490797546012267 / 500000000000000000) (49079754601227 / 50000000000000000) ((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal50_hz30 (by norm_num) (by norm_num)

theorem sGlobal50_hz32 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal50_hz31 sGlobal50_hz27 (by norm_num) (by norm_num)

theorem sGlobal50_hz33 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (s3r1 12225 46) := by
    convert sGlobal50_hz32 using 1 <;>
      norm_num [s3r1, mA] <;> ring

theorem sGlobal50_hz34 : B (163599182004089 / 500000000000000000) (16359918200409 / 50000000000000000) ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (2 : ℝ)) sGlobal50_hz10 (by norm_num) (by norm_num)

theorem sGlobal50_hz35 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal50_hz34 (by norm_num) (by norm_num)

theorem sGlobal50_hz36 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal50_hz35 sGlobal50_hz27 (by norm_num) (by norm_num)

theorem sGlobal50_hz37 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (s3rpp 12225 46) := by
    convert sGlobal50_hz36 using 1 <;>
      norm_num [s3rpp, mA] <;> ring

theorem sGlobal50_hz38 {c : ℝ} (hc : B (119 / 200) (3 / 5) c) : B (119 / 200) (3 / 5) c := hc

theorem sGlobal50_hz39 : B (140569591221326651 / 200000000000000000) (28113918244265333 / 40000000000000000) (kdot ((119 / 200))) := by
    constructor
    · apply bkdot_lower (q := (503903259860268857 / 1000000000000000000)) (a := (466765339047296373 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (62987907482533607 / 125000000000000000)) (a := (93353067809459253 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal50_hz40 : B (14161 / 40000) (14161 / 40000) (((119 / 200) : ℝ)^2) := bsq (bpoint ((119 / 200) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal50_hz41 : B (25839 / 40000) (25839 / 40000) ((1 : ℝ) - (((119 / 200) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal50_hz40 (by norm_num) (by norm_num)

theorem sGlobal50_hz42 : B (401862849738564413 / 500000000000000000) (803725699477128827 / 1000000000000000000) (√((1 : ℝ) - (((119 / 200) : ℝ)^2))) := bsqrt sGlobal50_hz41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal50_hz43 : B (127916917961776211 / 500000000000000000) (255833835923552423 / 1000000000000000000) ((√((1 : ℝ) - (((119 / 200) : ℝ)^2))) / Real.pi) := bdiv sGlobal50_hz42 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal50_hz44 : B (209097266941723393 / 500000000000000000) (418194533883446829 / 1000000000000000000) (((119 / 200) : ℝ) * (kdot ((119 / 200)))) := bmul (bpoint ((119 / 200) : ℝ)) sGlobal50_hz39 (by norm_num) (by norm_num)

theorem sGlobal50_hz45 : B (84253546225874901 / 125000000000000000) (168507092451749813 / 250000000000000000) (((√((1 : ℝ) - (((119 / 200) : ℝ)^2))) / Real.pi) + (((119 / 200) : ℝ) * (kdot ((119 / 200))))) := badd sGlobal50_hz43 sGlobal50_hz44 (by norm_num) (by norm_num)

theorem sGlobal50_hz46 : B (84253546225874901 / 125000000000000000) (168507092451749813 / 250000000000000000) (kappa ((119 / 200))) := by rw [kappa_eq]; exact sGlobal50_hz45

theorem sGlobal50_hz47 : B (352416382349566723 / 500000000000000000) (352416382349566747 / 500000000000000000) (kdot ((3 / 5))) := by
    constructor
    · apply bkdot_lower (q := (1 / 2)) (a := (115911902250201531 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (1 / 2)) (a := (9272952180016121 / 20000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal50_hz48 : B (9 / 25) (9 / 25) (((3 / 5) : ℝ)^2) := bsq (bpoint ((3 / 5) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal50_hz49 : B (16 / 25) (16 / 25) ((1 : ℝ) - (((3 / 5) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal50_hz48 (by norm_num) (by norm_num)

theorem sGlobal50_hz50 : B (4 / 5) (4 / 5) (√((1 : ℝ) - (((3 / 5) : ℝ)^2))) := bsqrt sGlobal50_hz49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal50_hz51 : B (254647908947032537 / 1000000000000000000) (127323954473516269 / 500000000000000000) ((√((1 : ℝ) - (((3 / 5) : ℝ)^2))) / Real.pi) := bdiv sGlobal50_hz50 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal50_hz52 : B (422899658819480067 / 1000000000000000000) (422899658819480097 / 1000000000000000000) (((3 / 5) : ℝ) * (kdot ((3 / 5)))) := bmul (bpoint ((3 / 5) : ℝ)) sGlobal50_hz47 (by norm_num) (by norm_num)

theorem sGlobal50_hz53 : B (169386891941628151 / 250000000000000000) (135509513553302527 / 200000000000000000) (((√((1 : ℝ) - (((3 / 5) : ℝ)^2))) / Real.pi) + (((3 / 5) : ℝ) * (kdot ((3 / 5))))) := badd sGlobal50_hz51 sGlobal50_hz52 (by norm_num) (by norm_num)

theorem sGlobal50_hz54 : B (169386891941628151 / 250000000000000000) (135509513553302527 / 200000000000000000) (kappa ((3 / 5))) := by rw [kappa_eq]; exact sGlobal50_hz53

theorem sGlobal50_hz55 {c : ℝ} (hc : B (119 / 200) (3 / 5) c) : B (84253546225874901 / 125000000000000000) (135509513553302527 / 200000000000000000) (kappa c) := bkappa (sGlobal50_hz38 hc) (by norm_num) (by norm_num) sGlobal50_hz46.1 sGlobal50_hz54.2

theorem sGlobal50_hz56 : B 24450 24450 ((2 : ℝ) * (12225 : ℝ)) := bmul (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal50_hz57 {c : ℝ} (hc : B (119 / 200) (3 / 5) c) : B (64490486446697473 / 200000000000000000) (40746453774125099 / 125000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (sGlobal50_hz55 hc) (by norm_num) (by norm_num)

theorem sGlobal50_hz58 {c : ℝ} (hc : B (119 / 200) (3 / 5) c) : B (31535847872435064297 / 4000000000000000) (19925015895547173411 / 2500000000000000) (((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) := bmul sGlobal50_hz56 (sGlobal50_hz57 hc) (by norm_num) (by norm_num)

theorem sGlobal50_hz59 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (4 : ℝ)) sGlobal50_hz10 (by norm_num) (by norm_num)

theorem sGlobal50_hz60 {c : ℝ} (hc : B (119 / 200) (3 / 5) c) : B (788396131371203805789 / 100000000000000000) (1992501425955535337011 / 250000000000000000) ((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bsub (sGlobal50_hz58 hc) sGlobal50_hz59 (by norm_num) (by norm_num)

theorem sGlobal50_hz61 {c : ℝ} (hc : B (119 / 200) (3 / 5) c) : B (88791673673335148243 / 1000000000000000000) (17854977685589126883 / 200000000000000000) (√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) := bsqrt (sGlobal50_hz60 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal50_hz62 : B (30670756373515103 / 125000000000000000) (122683025494060423 / 500000000000000000) ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal50_hz7 (by norm_num) (by norm_num)

theorem sGlobal50_hz63 {c : ℝ} (hc : B (119 / 200) (3 / 5) c) : B (88546307622347027397 / 1000000000000000000) (89029522376957513591 / 1000000000000000000) ((√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) - ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))))) := bsub (sGlobal50_hz61 hc) sGlobal50_hz62 (by norm_num) (by norm_num)

theorem sGlobal50_hz64 {c : ℝ} (hc : B (119 / 200) (3 / 5) c) : B (88546307622347027397 / 1000000000000000000) (89029522376957513591 / 1000000000000000000) (s3dm 12225 46 c) := by
    convert (sGlobal50_hz63 hc) using 1 <;>
      norm_num [s3dm, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal50_hz65 : B (6126072185528622723889 / 500000000000000000) (2450428874211449090087 / 200000000000000000) ((s3ap 12225 46)^2) := bsq sGlobal50_hz9 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal50_hz66 : B (6126072185528622723889 / 250000000000000000) (2450428874211449090087 / 100000000000000000) ((2 : ℝ) * ((s3ap 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal50_hz65 (by norm_num) (by norm_num)

theorem sGlobal50_hz67 {c : ℝ} (hc : B (119 / 200) (3 / 5) c) : B (392022429677565564209 / 50000000000000000) (990781981833647330091 / 125000000000000000) ((s3dm 12225 46 c)^2) := bsq (sGlobal50_hz64 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal50_hz68 {c : ℝ} (hc : B (119 / 200) (3 / 5) c) : B (4144508221861328063707 / 250000000000000000) (1666384014856317961669 / 100000000000000000) (((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) := bsub sGlobal50_hz66 (sGlobal50_hz67 hc) (by norm_num) (by norm_num)

theorem sGlobal50_hz69 : B (1524735695971823534271 / 125000000000000000) (609894278388729413841 / 50000000000000000) ((s3am 12225 46)^2) := bsq sGlobal50_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal50_hz70 : B (1524735695971823534271 / 62500000000000000) (609894278388729413841 / 25000000000000000) ((2 : ℝ) * ((s3am 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal50_hz69 (by norm_num) (by norm_num)

theorem sGlobal50_hz71 {c : ℝ} (hc : B (119 / 200) (3 / 5) c) : B (679545352156875851 / 1000000000000000000) (683062652784148511 / 1000000000000000000) ((((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) / ((2 : ℝ) * ((s3am 12225 46)^2))) := bdiv (sGlobal50_hz68 hc) sGlobal50_hz70 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal50_hz72 {c : ℝ} (hc : B (119 / 200) (3 / 5) c) : B (679545352156875851 / 1000000000000000000) (683062652784148511 / 1000000000000000000) (s3c1 12225 46 c) := by
    convert (sGlobal50_hz71 hc) using 1 <;>
      norm_num [s3c1] <;> ring

theorem sGlobal50_hz73 {c : ℝ} (hc : B (119 / 200) (3 / 5) c) : B (140569591221326651 / 200000000000000000) (352416382349566747 / 500000000000000000) (kdot c) := bkdot (sGlobal50_hz38 hc) sGlobal50_hz39.1 sGlobal50_hz47.2

theorem sGlobal50_hz74 : B (184455729813305287 / 250000000000000000) (14756458385064423 / 20000000000000000) (kdot ((679545352156875851 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (54600602214166723 / 125000000000000000)) (a := (25739174712928077 / 62500000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (436804817713333783 / 1000000000000000000)) (a := (41182679540684923 / 100000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal50_hz75 : B (184838104999124957 / 250000000000000000) (739352419996499831 / 1000000000000000000) (kdot ((683062652784148511 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (433946877508740999 / 1000000000000000000)) (a := (51178032657184627 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (216973438754370499 / 500000000000000000)) (a := (204712130628738507 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal50_hz76 {c : ℝ} (hc : B (119 / 200) (3 / 5) c) : B (184455729813305287 / 250000000000000000) (739352419996499831 / 1000000000000000000) (kdot (s3c1 12225 46 c)) := bkdot (sGlobal50_hz72 hc) sGlobal50_hz74.1 sGlobal50_hz75.2

theorem sGlobal50_hz77 {c : ℝ} (hc : B (119 / 200) (3 / 5) c) : B (14161 / 40000) (9 / 25) (c^2) := bsq (sGlobal50_hz38 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal50_hz78 {c : ℝ} (hc : B (119 / 200) (3 / 5) c) : B (16 / 25) (25839 / 40000) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (sGlobal50_hz77 hc) (by norm_num) (by norm_num)

theorem sGlobal50_hz79 {c : ℝ} (hc : B (119 / 200) (3 / 5) c) : B (4 / 5) (803725699477128827 / 1000000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (sGlobal50_hz78 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal50_hz80 : B (39119999999999765769 / 1600000000000000) (3912000000000000489 / 160000000000000) ((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (149450625 : ℝ)) sGlobal50_hz10 (by norm_num) (by norm_num)

theorem sGlobal50_hz81 {c : ℝ} (hc : B (119 / 200) (3 / 5) c) : B (140569591221326651 / 250000000000000000) (566492206822209623 / 1000000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (sGlobal50_hz79 hc) (sGlobal50_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal50_hz82 {c : ℝ} (hc : B (119 / 200) (3 / 5) c) : B (1374770602144566415341 / 100000000000000000) (3462683614200756753423 / 250000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) := bmul sGlobal50_hz80 (sGlobal50_hz81 hc) (by norm_num) (by norm_num)

theorem sGlobal50_hz83 {c : ℝ} (hc : B (119 / 200) (3 / 5) c) : B (1374770602144566415341 / 200000000000000000) (3462683614200756753423 / 500000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) / (2 : ℝ)) := bdiv (sGlobal50_hz82 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal50_hz84 {c : ℝ} (hc : B (119 / 200) (3 / 5) c) : B (1374770602144566415341 / 200000000000000000) (3462683614200756753423 / 500000000000000000) (s3Cpa 12225 c) := by
    convert (sGlobal50_hz83 hc) using 1 <;>
      norm_num [s3Cpa, mA] <;> ring

theorem sGlobal50_hz85 {c : ℝ} (hc : B (119 / 200) (3 / 5) c) : B (254647908947032537 / 1000000000000000000) (255833835923552423 / 1000000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (sGlobal50_hz79 hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal50_hz86 {c : ℝ} (hc : B (119 / 200) (3 / 5) c) : B (209097266941723393 / 500000000000000000) (422899658819480097 / 1000000000000000000) (c * (kdot c)) := bmul (sGlobal50_hz38 hc) (sGlobal50_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal50_hz87 {c : ℝ} (hc : B (119 / 200) (3 / 5) c) : B (-4206293746811189 / 25000000000000000) (-162360697959894363 / 1000000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (sGlobal50_hz85 hc) (sGlobal50_hz86 hc) (by norm_num) (by norm_num)

theorem sGlobal50_hz88 {c : ℝ} (hc : B (119 / 200) (3 / 5) c) : B (-205687764219067167811 / 50000000000000000) (-3969719065119393406657 / 1000000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) := bmul sGlobal50_hz80 (sGlobal50_hz87 hc) (by norm_num) (by norm_num)

theorem sGlobal50_hz89 {c : ℝ} (hc : B (119 / 200) (3 / 5) c) : B (-205687764219067167811 / 100000000000000000) (-62026860392490521979 / 31250000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) / (2 : ℝ)) := bdiv (sGlobal50_hz88 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal50_hz90 {c : ℝ} (hc : B (119 / 200) (3 / 5) c) : B (-205687764219067167811 / 100000000000000000) (-62026860392490521979 / 31250000000000000) (s3Cpp 12225 c) := by
    convert (sGlobal50_hz89 hc) using 1 <;>
      norm_num [s3Cpp, mA] <;> ring

theorem sGlobal50_hz91 {c : ℝ} (hc : B (119 / 200) (3 / 5) c) : B (3494499060328284892553 / 500000000000000000) (220016010572976622471 / 31250000000000000) ((s3Cpa 12225 c) + (s3r1 12225 46)) := badd (sGlobal50_hz84 hc) sGlobal50_hz33 (by norm_num) (by norm_num)

theorem sGlobal50_hz92 {c : ℝ} (hc : B (119 / 200) (3 / 5) c) : B (3955056241787485833 / 62500000000000000) (31873664051291786337 / 500000000000000000) (((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) := bdiv (sGlobal50_hz91 hc) sGlobal50_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal50_hz93 {c : ℝ} (hc : B (119 / 200) (3 / 5) c) : B (3170179144704691687 / 50000000000000000) (63870011128077633097 / 1000000000000000000) ((((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) + (s3e0 12225 46)) := badd (sGlobal50_hz92 hc) sGlobal50_hz16 (by norm_num) (by norm_num)

theorem sGlobal50_hz94 {c : ℝ} (hc : B (119 / 200) (3 / 5) c) : B (3170179144704691687 / 50000000000000000) (63870011128077633097 / 1000000000000000000) (s3Lam 12225 46 c) := by
    convert (sGlobal50_hz93 hc) using 1 <;>
      norm_num [s3Lam] <;> ring

theorem sGlobal50_hz95 {c : ℝ} (hc : B (119 / 200) (3 / 5) c) : B (-198011423556817987251 / 100000000000000000) (-190809612593720442851 / 100000000000000000) ((s3Cpp 12225 c) + (s3rpp 12225 46)) := badd (sGlobal50_hz90 hc) sGlobal50_hz37 (by norm_num) (by norm_num)

theorem sGlobal50_hz96 {c : ℝ} (hc : B (119 / 200) (3 / 5) c) : B (-183000281492106641159 / 125000000000000000) (-190809612593720442851 / 200000000000000000) (if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) := bweaken (bfirst (sGlobal50_hz95 hc) (sGlobal50_hz76 hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem sGlobal50_hz97 {c : ℝ} (hc : B (119 / 200) (3 / 5) c) : B (201000716190411410293 / 50000000000000000) (4079378321500760685923 / 1000000000000000000) ((s3Lam 12225 46 c)^2) := bsq (sGlobal50_hz94 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal50_hz98 {c : ℝ} (hc : B (119 / 200) (3 / 5) c) : B (230890942819006207 / 500000000000000000) (116643646907129557 / 250000000000000000) ((s3c1 12225 46 c)^2) := bsq (sGlobal50_hz72 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal50_hz99 {c : ℝ} (hc : B (119 / 200) (3 / 5) c) : B (133356353092870443 / 250000000000000000) (269109057180993793 / 500000000000000000) ((1 : ℝ) - ((s3c1 12225 46 c)^2)) := bsub (bpoint (1 : ℝ)) (sGlobal50_hz98 hc) (by norm_num) (by norm_num)

theorem sGlobal50_hz100 {c : ℝ} (hc : B (119 / 200) (3 / 5) c) : B (91294972853407447 / 125000000000000000) (733633501390161153 / 1000000000000000000) (√((1 : ℝ) - ((s3c1 12225 46 c)^2))) := bsqrt (sGlobal50_hz99 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal50_hz101 {c : ℝ} (hc : B (119 / 200) (3 / 5) c) : B (2294492928207555513 / 1000000000000000000) (576194404598671911 / 250000000000000000) (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))) := bmul pi_mem (sGlobal50_hz100 hc) (by norm_num) (by norm_num)

theorem sGlobal50_hz102 {c : ℝ} (hc : B (119 / 200) (3 / 5) c) : B (1744209199067209262719 / 1000000000000000000) (1777899714290053283033 / 1000000000000000000) (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2))))) := bdiv (sGlobal50_hz97 hc) (sGlobal50_hz101 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal50_hz103 {c : ℝ} (hc : B (119 / 200) (3 / 5) c) : B (280206947130356133447 / 1000000000000000000) (411925825660725534389 / 500000000000000000) ((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) := badd (sGlobal50_hz96 hc) (sGlobal50_hz102 hc) (by norm_num) (by norm_num)

theorem sGlobal50_hz104 : B (3762781186094069 / 250000000000000000) (376278118609407 / 25000000000000000) ((s3e0 12225 46)^2) := bsq sGlobal50_hz16 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal50_hz105 {c : ℝ} (hc : B (119 / 200) (3 / 5) c) : B (280221998255100509723 / 1000000000000000000) (411933351223097722529 / 500000000000000000) (((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) := badd (sGlobal50_hz103 hc) sGlobal50_hz104 (by norm_num) (by norm_num)

theorem sGlobal50_hz106 {c : ℝ} (hc : B (119 / 200) (3 / 5) c) : B (159359535853173889927 / 500000000000000000) (431181887950159857537 / 500000000000000000) ((((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) + (s3rs 12225 46 maskSlack)) := badd (sGlobal50_hz105 hc) sGlobal50_hz29 (by norm_num) (by norm_num)

theorem sGlobal50_hz107 {c : ℝ} (hc : B (119 / 200) (3 / 5) c) : B (159359535853173889927 / 500000000000000000) (431181887950159857537 / 500000000000000000) (s3U 12225 46 maskSlack c) := by
    convert (sGlobal50_hz106 hc) using 1 <;>
      norm_num [s3U] <;> ring

theorem sGlobal50_hz108 {c : ℝ} (hc : B (119 / 200) (3 / 5) c) : B (-66676282775411373529 / 31250000000000000) (-8053214606180423863 / 3906250000000000) ((s3Cpp 12225 c) - (s3rpp 12225 46)) := bsub (sGlobal50_hz90 hc) sGlobal50_hz37 (by norm_num) (by norm_num)

theorem sGlobal50_hz109 {c : ℝ} (hc : B (119 / 200) (3 / 5) c) : B (-66676282775411373529 / 31250000000000000) (-8053214606180423863 / 3906250000000000) (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ)) := bweaken (bmin (sGlobal50_hz108 hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem sGlobal50_hz110 {c : ℝ} (hc : B (119 / 200) (3 / 5) c) : B (-788756336421941396099 / 500000000000000000) (-380278163846702081467 / 250000000000000000) ((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) := bmul (sGlobal50_hz76 hc) (sGlobal50_hz109 hc) (by norm_num) (by norm_num)

theorem sGlobal50_hz111 {c : ℝ} (hc : B (119 / 200) (3 / 5) c) : B (-788763861984313584239 / 500000000000000000) (-23767620414243010971 / 15625000000000000) (((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) := bsub (sGlobal50_hz110 hc) sGlobal50_hz104 (by norm_num) (by norm_num)

theorem sGlobal50_hz112 {c : ℝ} (hc : B (119 / 200) (3 / 5) c) : B (-808012398711375719247 / 500000000000000000) (-62384991198511998891 / 40000000000000000) ((((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) - (s3rs 12225 46 maskSlack)) := bsub (sGlobal50_hz111 hc) sGlobal50_hz29 (by norm_num) (by norm_num)

theorem sGlobal50_hz113 {c : ℝ} (hc : B (119 / 200) (3 / 5) c) : B (-808012398711375719247 / 500000000000000000) (-62384991198511998891 / 40000000000000000) (s3L 12225 46 maskSlack c) := by
    convert (sGlobal50_hz112 hc) using 1 <;>
      norm_num [s3L] <;> ring

theorem sGlobal50_hz114 {c : ℝ} (hc : B (119 / 200) (3 / 5) c) : B 0 (431181887950159857537 / 500000000000000000) |(s3U 12225 46 maskSlack c)| := bweaken (babs (sGlobal50_hz107 hc)) (by norm_num) (by norm_num)

theorem sGlobal50_hz115 {c : ℝ} (hc : B (119 / 200) (3 / 5) c) : B 0 (808012398711375719247 / 500000000000000000) |(s3L 12225 46 maskSlack c)| := bweaken (babs (sGlobal50_hz113 hc)) (by norm_num) (by norm_num)

theorem sGlobal50_hz116 {c : ℝ} (hc : B (119 / 200) (3 / 5) c) : B 0 (808012398711375719247 / 500000000000000000) (max |(s3U 12225 46 maskSlack c)| |(s3L 12225 46 maskSlack c)|) := bweaken (bmax (sGlobal50_hz114 hc) (sGlobal50_hz115 hc)) (by norm_num) (by norm_num)

theorem sGlobal50_hz117 {c : ℝ} (hc : B (119 / 200) (3 / 5) c) : B 0 (808012398711375719247 / 500000000000000000) (s3nks 12225 46 maskSlack c) := by
    convert (sGlobal50_hz116 hc) using 1 <;>
      norm_num [s3nks] <;> ring

theorem sGlobal50 {c : ℝ} (hc : B (119 / 200) (3 / 5) c) :
    0 < s3am 12225 46 ∧ 0 ≤ s3dm 12225 46 c ∧
    s3dm 12225 46 c ^ 2 ≤ 2 * s3ap 12225 46 ^ 2 ∧ s3c1 12225 46 c < 1 ∧
    0 ≤ s3Cpa 12225 c - s3r1 12225 46 ∧
    s3e0 12225 46 ≤ (s3Cpa 12225 c - s3r1 12225 46) / s3ap 12225 46 ∧
    s3nks 12225 46 maskSlack c ≤ 12225 * (132191 / 1000000) := by

  refine ⟨lt_of_lt_of_le (by norm_num) sGlobal50_hz14.1,
    le_trans (by norm_num) (sGlobal50_hz64 hc).1, ?_,
    lt_of_le_of_lt (sGlobal50_hz72 hc).2 (by norm_num), ?_, ?_,
    le_trans (sGlobal50_hz117 hc).2 (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (sGlobal50_hz64 hc).1) (sGlobal50_hz64 hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) sGlobal50_hz9.1 2
    nlinarith only [h1, h2]
  · linarith only [(sGlobal50_hz84 hc).1, sGlobal50_hz33.2]
  · have hap : 0 < s3ap 12225 46 := lt_of_lt_of_le (by norm_num) sGlobal50_hz9.1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul sGlobal50_hz16.2 sGlobal50_hz9.2 (le_trans (by norm_num) sGlobal50_hz9.1) (by norm_num)
    linarith only [h, (sGlobal50_hz84 hc).1, sGlobal50_hz33.2]

end BstLean.Part255
