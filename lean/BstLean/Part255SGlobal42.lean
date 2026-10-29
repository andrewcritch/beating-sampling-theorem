import BstLean.Part255SGlobal38
import BstLean.Part255Numeric10
namespace BstLean.Part255
open Real BstLean.Part130 BstLean.Part182 BstLean.Part197 BstLean.Part246
theorem sGlobal42_hz0 : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal42_hz1 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) ((√(23 : ℝ)) / (12225 : ℝ)) := bdiv sGlobal42_hz0 (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal42_hz2 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) maskSlack := by
    convert sGlobal42_hz1 using 1 <;>
      norm_num [maskSlack] <;> ring

theorem sGlobal42_hz3 : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal42_hz4 : B (6395294793910793 / 500000000000000000) (12790589587821587 / 1000000000000000000) (√((2 / 12225) : ℝ)) := bsqrt (bpoint ((2 / 12225) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal42_hz5 : B (7230130686979 / 62500000000000000) (23136418198333 / 200000000000000000) (√((2 / 149450625) : ℝ)) := bsqrt (bpoint ((2 / 149450625) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal42_hz6 : B (2211334438749598093 / 20000000000000000) (110566721937479904651 / 1000000000000000000) (√(12225 : ℝ)) := bsqrt (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal42_hz7 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))) := bmul sGlobal42_hz3 sGlobal42_hz4 (by norm_num) (by norm_num)

theorem sGlobal42_hz8 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) ((√(12225 : ℝ)) + ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := badd sGlobal42_hz6 sGlobal42_hz7 (by norm_num) (by norm_num)

theorem sGlobal42_hz9 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) (s3ap 12225 46) := by
    convert sGlobal42_hz8 using 1 <;>
      norm_num [s3ap, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal42_hz10 : B (163599182004089 / 1000000000000000000) (16359918200409 / 100000000000000000) ((2 : ℝ) / (12225 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal42_hz11 : B (1222499983640081799591 / 100000000000000000) (12224999836400817995911 / 1000000000000000000) ((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ))) := bsub (bpoint (12225 : ℝ)) sGlobal42_hz10 (by norm_num) (by norm_num)

theorem sGlobal42_hz12 : B (110566721197658827907 / 1000000000000000000) (27641680299414706977 / 250000000000000000) (√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) := bsqrt sGlobal42_hz11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal42_hz13 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) ((√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) - ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bsub sGlobal42_hz12 sGlobal42_hz7 (by norm_num) (by norm_num)

theorem sGlobal42_hz14 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) (s3am 12225 46) := by
    convert sGlobal42_hz13 using 1 <;>
      norm_num [s3am, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal42_hz15 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√((2 / 12225) : ℝ)) * (√(92 : ℝ))) := bmul sGlobal42_hz4 sGlobal42_hz3 (by norm_num) (by norm_num)

theorem sGlobal42_hz16 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) (s3e0 12225 46) := by
    convert sGlobal42_hz15 using 1 <;>
      norm_num [s3e0, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal42_hz17 : B (250196148528560847 / 500000000000000000) (100078459411424339 / 200000000000000000) (((1 / 2) : ℝ) + maskSlack) := badd (bpoint ((1 / 2) : ℝ)) sGlobal42_hz2 (by norm_num) (by norm_num)

theorem sGlobal42_hz18 : B (59827153232297998295487 / 800000000000000) (23930861292919199366019 / 320000000000000) ((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack)) := bmul (bpoint (149450625 : ℝ)) sGlobal42_hz17 (by norm_num) (by norm_num)

theorem sGlobal42_hz19 : B (1729554180017180009583 / 200000000000000000) (8647770900085900056557 / 1000000000000000000) (√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) := bsqrt sGlobal42_hz18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal42_hz20 : B (4328681281566262743499 / 500000000000000000) (8657362563132525495641 / 1000000000000000000) ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))) := badd sGlobal42_hz19 sGlobal42_hz3 (by norm_num) (by norm_num)

theorem sGlobal42_hz21 : B (110732771457999278473 / 1000000000000000000) (55366385728999643621 / 500000000000000000) ((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ)))) := bmul sGlobal42_hz4 sGlobal42_hz20 (by norm_num) (by norm_num)

theorem sGlobal42_hz22 : B (209099159 / 15625000000000000) (13382346177 / 1000000000000000000) ((2 : ℝ) / (149450625 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (149450625 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal42_hz23 : B (2452349334953899930479 / 200000000000000000) (12261746674769501594427 / 1000000000000000000) (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2) := bsq sGlobal42_hz21 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal42_hz24 : B (82045469362091 / 500000000000000000) (32818187747289 / 200000000000000000) (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2)) := bmul sGlobal42_hz22 sGlobal42_hz23 (by norm_num) (by norm_num)

theorem sGlobal42_hz25 : B (82045469362091 / 250000000000000000) (32818187747289 / 100000000000000000) ((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) := bmul (bpoint (2 : ℝ)) sGlobal42_hz24 (by norm_num) (by norm_num)

theorem sGlobal42_hz26 : B (117258080744995992792057 / 1000000000000000000) (58629040372497996396029 / 500000000000000000) (√(13749457500 : ℝ)) := bsqrt (bpoint (13749457500 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal42_hz27 : B (117304080744995992792057 / 1000000000000000000) (58652040372497996396029 / 500000000000000000) ((√(13749457500 : ℝ)) + (46 : ℝ)) := badd sGlobal42_hz26 (bpoint (46 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal42_hz28 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal42_hz25 sGlobal42_hz27 (by norm_num) (by norm_num)

theorem sGlobal42_hz29 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (s3rs 12225 46 maskSlack) := by
    convert sGlobal42_hz28 using 1 <;>
      norm_num [s3rs, s3pp, s3K, mA, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal42_hz30 : B (490797546012267 / 1000000000000000000) (49079754601227 / 100000000000000000) ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (3 : ℝ)) sGlobal42_hz10 (by norm_num) (by norm_num)

theorem sGlobal42_hz31 : B (490797546012267 / 500000000000000000) (49079754601227 / 50000000000000000) ((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal42_hz30 (by norm_num) (by norm_num)

theorem sGlobal42_hz32 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal42_hz31 sGlobal42_hz27 (by norm_num) (by norm_num)

theorem sGlobal42_hz33 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (s3r1 12225 46) := by
    convert sGlobal42_hz32 using 1 <;>
      norm_num [s3r1, mA] <;> ring

theorem sGlobal42_hz34 : B (163599182004089 / 500000000000000000) (16359918200409 / 50000000000000000) ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (2 : ℝ)) sGlobal42_hz10 (by norm_num) (by norm_num)

theorem sGlobal42_hz35 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal42_hz34 (by norm_num) (by norm_num)

theorem sGlobal42_hz36 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal42_hz35 sGlobal42_hz27 (by norm_num) (by norm_num)

theorem sGlobal42_hz37 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (s3rpp 12225 46) := by
    convert sGlobal42_hz36 using 1 <;>
      norm_num [s3rpp, mA] <;> ring

theorem sGlobal42_hz38 {c : ℝ} (hc : B (111 / 200) (14 / 25) c) : B (111 / 200) (14 / 25) c := hc

theorem sGlobal42_hz39 : B (85910218598212437 / 125000000000000000) (687281748785700763 / 1000000000000000000) (kdot ((111 / 200))) := by
    constructor
    · apply bkdot_lower (q := (33434499482226583 / 62500000000000000)) (a := (491216680329146951 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (534951991715625327 / 1000000000000000000)) (a := (245608340164572481 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal42_hz40 : B (12321 / 40000) (12321 / 40000) (((111 / 200) : ℝ)^2) := bsq (bpoint ((111 / 200) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal42_hz41 : B (27679 / 40000) (27679 / 40000) ((1 : ℝ) - (((111 / 200) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal42_hz40 (by norm_num) (by norm_num)

theorem sGlobal42_hz42 : B (103981293389724673 / 125000000000000000) (166370069423559477 / 200000000000000000) (√((1 : ℝ) - (((111 / 200) : ℝ)^2))) := bsqrt sGlobal42_hz41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal42_hz43 : B (264786189313012847 / 1000000000000000000) (264786189313012849 / 1000000000000000000) ((√((1 : ℝ) - (((111 / 200) : ℝ)^2))) / Real.pi) := bdiv sGlobal42_hz42 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal42_hz44 : B (19072068528803161 / 50000000000000000) (95360342644015981 / 250000000000000000) (((111 / 200) : ℝ) * (kdot ((111 / 200)))) := bmul (bpoint ((111 / 200) : ℝ)) sGlobal42_hz39 (by norm_num) (by norm_num)

theorem sGlobal42_hz45 : B (646227559889076067 / 1000000000000000000) (646227559889076773 / 1000000000000000000) (((√((1 : ℝ) - (((111 / 200) : ℝ)^2))) / Real.pi) + (((111 / 200) : ℝ) * (kdot ((111 / 200))))) := badd sGlobal42_hz43 sGlobal42_hz44 (by norm_num) (by norm_num)

theorem sGlobal42_hz46 : B (646227559889076067 / 1000000000000000000) (646227559889076773 / 1000000000000000000) (kappa ((111 / 200))) := by rw [kappa_eq]; exact sGlobal42_hz45

theorem sGlobal42_hz47 : B (34459943817379969 / 50000000000000000) (689198876347600269 / 1000000000000000000) (kdot ((14 / 25))) := by
    constructor
    · apply bkdot_lower (q := (531085004543794337 / 1000000000000000000)) (a := (488205263396917357 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (16596406391993573 / 31250000000000000)) (a := (244102631698457981 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal42_hz48 : B (196 / 625) (196 / 625) (((14 / 25) : ℝ)^2) := bsq (bpoint ((14 / 25) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal42_hz49 : B (429 / 625) (429 / 625) ((1 : ℝ) - (((14 / 25) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal42_hz48 (by norm_num) (by norm_num)

theorem sGlobal42_hz50 : B (165698521417663833 / 200000000000000000) (414246303544159583 / 500000000000000000) (√((1 : ℝ) - (((14 / 25) : ℝ)^2))) := bsqrt sGlobal42_hz49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal42_hz51 : B (263717387466394877 / 1000000000000000000) (263717387466394879 / 1000000000000000000) ((√((1 : ℝ) - (((14 / 25) : ℝ)^2))) / Real.pi) := bdiv sGlobal42_hz50 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal42_hz52 : B (96487842688663913 / 250000000000000000) (385951370754656151 / 1000000000000000000) (((14 / 25) : ℝ) * (kdot ((14 / 25)))) := bmul (bpoint ((14 / 25) : ℝ)) sGlobal42_hz47 (by norm_num) (by norm_num)

theorem sGlobal42_hz53 : B (649668758221050529 / 1000000000000000000) (64966875822105103 / 100000000000000000) (((√((1 : ℝ) - (((14 / 25) : ℝ)^2))) / Real.pi) + (((14 / 25) : ℝ) * (kdot ((14 / 25))))) := badd sGlobal42_hz51 sGlobal42_hz52 (by norm_num) (by norm_num)

theorem sGlobal42_hz54 : B (649668758221050529 / 1000000000000000000) (64966875822105103 / 100000000000000000) (kappa ((14 / 25))) := by rw [kappa_eq]; exact sGlobal42_hz53

theorem sGlobal42_hz55 {c : ℝ} (hc : B (111 / 200) (14 / 25) c) : B (646227559889076067 / 1000000000000000000) (64966875822105103 / 100000000000000000) (kappa c) := bkappa (sGlobal42_hz38 hc) (by norm_num) (by norm_num) sGlobal42_hz46.1 sGlobal42_hz54.2

theorem sGlobal42_hz56 : B 24450 24450 ((2 : ℝ) * (12225 : ℝ)) := bmul (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal42_hz57 {c : ℝ} (hc : B (111 / 200) (14 / 25) c) : B (35033124177894897 / 100000000000000000) (353772440110923933 / 1000000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (sGlobal42_hz55 hc) (by norm_num) (by norm_num)

theorem sGlobal42_hz58 {c : ℝ} (hc : B (111 / 200) (14 / 25) c) : B (17131197722990604633 / 2000000000000000) (172994723214241803237 / 20000000000000000) (((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) := bmul sGlobal42_hz56 (sGlobal42_hz57 hc) (by norm_num) (by norm_num)

theorem sGlobal42_hz59 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (4 : ℝ)) sGlobal42_hz10 (by norm_num) (by norm_num)

theorem sGlobal42_hz60 {c : ℝ} (hc : B (111 / 200) (14 / 25) c) : B (428279910354928715007 / 50000000000000000) (4324867753157681072747 / 500000000000000000) ((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bsub (sGlobal42_hz58 hc) sGlobal42_hz59 (by norm_num) (by norm_num)

theorem sGlobal42_hz61 {c : ℝ} (hc : B (111 / 200) (14 / 25) c) : B (46275258527366906273 / 500000000000000000) (2906373570342617853 / 31250000000000000) (√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) := bsqrt (sGlobal42_hz60 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal42_hz62 : B (30670756373515103 / 125000000000000000) (122683025494060423 / 500000000000000000) ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal42_hz7 (by norm_num) (by norm_num)

theorem sGlobal42_hz63 {c : ℝ} (hc : B (111 / 200) (14 / 25) c) : B (923051510037456917 / 10000000000000000) (11594823524996956309 / 125000000000000000) ((√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) - ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))))) := bsub (sGlobal42_hz61 hc) sGlobal42_hz62 (by norm_num) (by norm_num)

theorem sGlobal42_hz64 {c : ℝ} (hc : B (111 / 200) (14 / 25) c) : B (923051510037456917 / 10000000000000000) (11594823524996956309 / 125000000000000000) (s3dm 12225 46 c) := by
    convert (sGlobal42_hz63 hc) using 1 <;>
      norm_num [s3dm, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal42_hz65 : B (6126072185528622723889 / 500000000000000000) (2450428874211449090087 / 200000000000000000) ((s3ap 12225 46)^2) := bsq sGlobal42_hz9 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal42_hz66 : B (6126072185528622723889 / 250000000000000000) (2450428874211449090087 / 100000000000000000) ((2 : ℝ) * ((s3ap 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal42_hz65 (by norm_num) (by norm_num)

theorem sGlobal42_hz67 {c : ℝ} (hc : B (111 / 200) (14 / 25) c) : B (8520240901824294275949 / 1000000000000000000) (8604155684852661984319 / 1000000000000000000) ((s3dm 12225 46 c)^2) := bsq (sGlobal42_hz64 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal42_hz68 {c : ℝ} (hc : B (111 / 200) (14 / 25) c) : B (15900133057261828911237 / 1000000000000000000) (15984047840290196624921 / 1000000000000000000) (((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) := bsub sGlobal42_hz66 (sGlobal42_hz67 hc) (by norm_num) (by norm_num)

theorem sGlobal42_hz69 : B (1524735695971823534271 / 125000000000000000) (609894278388729413841 / 50000000000000000) ((s3am 12225 46)^2) := bsq sGlobal42_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal42_hz70 : B (1524735695971823534271 / 62500000000000000) (609894278388729413841 / 25000000000000000) ((2 : ℝ) * ((s3am 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal42_hz69 (by norm_num) (by norm_num)

theorem sGlobal42_hz71 {c : ℝ} (hc : B (111 / 200) (14 / 25) c) : B (651757756248679401 / 1000000000000000000) (32759874142692021 / 50000000000000000) ((((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) / ((2 : ℝ) * ((s3am 12225 46)^2))) := bdiv (sGlobal42_hz68 hc) sGlobal42_hz70 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal42_hz72 {c : ℝ} (hc : B (111 / 200) (14 / 25) c) : B (651757756248679401 / 1000000000000000000) (32759874142692021 / 50000000000000000) (s3c1 12225 46 c) := by
    convert (sGlobal42_hz71 hc) using 1 <;>
      norm_num [s3c1] <;> ring

theorem sGlobal42_hz73 {c : ℝ} (hc : B (111 / 200) (14 / 25) c) : B (85910218598212437 / 125000000000000000) (689198876347600269 / 1000000000000000000) (kdot c) := bkdot (sGlobal42_hz38 hc) sGlobal42_hz39.1 sGlobal42_hz47.2

theorem sGlobal42_hz74 : B (181492028654479527 / 250000000000000000) (725968114617918111 / 1000000000000000000) (kdot ((651757756248679401 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (459163702046450581 / 1000000000000000000)) (a := (10761206974571359 / 25000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (22958185102322529 / 50000000000000000)) (a := (430448278982854357 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal42_hz75 : B (727414588035923243 / 1000000000000000000) (363707294017961623 / 500000000000000000) (kdot ((32759874142692021 / 50000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (456415416397964049 / 1000000000000000000)) (a := (85635232770209087 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (28525963524872753 / 62500000000000000)) (a := (428176163851045433 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal42_hz76 {c : ℝ} (hc : B (111 / 200) (14 / 25) c) : B (181492028654479527 / 250000000000000000) (363707294017961623 / 500000000000000000) (kdot (s3c1 12225 46 c)) := bkdot (sGlobal42_hz72 hc) sGlobal42_hz74.1 sGlobal42_hz75.2

theorem sGlobal42_hz77 {c : ℝ} (hc : B (111 / 200) (14 / 25) c) : B (12321 / 40000) (196 / 625) (c^2) := bsq (sGlobal42_hz38 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal42_hz78 {c : ℝ} (hc : B (111 / 200) (14 / 25) c) : B (429 / 625) (27679 / 40000) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (sGlobal42_hz77 hc) (by norm_num) (by norm_num)

theorem sGlobal42_hz79 {c : ℝ} (hc : B (111 / 200) (14 / 25) c) : B (165698521417663833 / 200000000000000000) (166370069423559477 / 200000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (sGlobal42_hz78 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal42_hz80 : B (39119999999999765769 / 1600000000000000) (3912000000000000489 / 160000000000000) ((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (149450625 : ℝ)) sGlobal42_hz10 (by norm_num) (by norm_num)

theorem sGlobal42_hz81 {c : ℝ} (hc : B (111 / 200) (14 / 25) c) : B (569407847855683409 / 1000000000000000000) (286655162261473601 / 500000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (sGlobal42_hz79 hc) (sGlobal42_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal42_hz82 {c : ℝ} (hc : B (111 / 200) (14 / 25) c) : B (13922021880071375991943 / 1000000000000000000) (350435935864651521027 / 25000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) := bmul sGlobal42_hz80 (sGlobal42_hz81 hc) (by norm_num) (by norm_num)

theorem sGlobal42_hz83 {c : ℝ} (hc : B (111 / 200) (14 / 25) c) : B (6961010940035687995971 / 1000000000000000000) (350435935864651521027 / 50000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) / (2 : ℝ)) := bdiv (sGlobal42_hz82 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal42_hz84 {c : ℝ} (hc : B (111 / 200) (14 / 25) c) : B (6961010940035687995971 / 1000000000000000000) (350435935864651521027 / 50000000000000000) (s3Cpa 12225 c) := by
    convert (sGlobal42_hz83 hc) using 1 <;>
      norm_num [s3Cpa, mA] <;> ring

theorem sGlobal42_hz85 {c : ℝ} (hc : B (111 / 200) (14 / 25) c) : B (263717387466394877 / 1000000000000000000) (264786189313012849 / 1000000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (sGlobal42_hz79 hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal42_hz86 {c : ℝ} (hc : B (111 / 200) (14 / 25) c) : B (19072068528803161 / 50000000000000000) (385951370754656151 / 1000000000000000000) (c * (kdot c)) := bmul (sGlobal42_hz38 hc) (sGlobal42_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal42_hz87 {c : ℝ} (hc : B (111 / 200) (14 / 25) c) : B (-61116991644130637 / 500000000000000000) (-116655181263050371 / 1000000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (sGlobal42_hz85 hc) (sGlobal42_hz86 hc) (by norm_num) (by norm_num)

theorem sGlobal42_hz88 {c : ℝ} (hc : B (111 / 200) (14 / 25) c) : B (-1494310445698994261439 / 500000000000000000) (-2852219181881564493287 / 1000000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) := bmul sGlobal42_hz80 (sGlobal42_hz87 hc) (by norm_num) (by norm_num)

theorem sGlobal42_hz89 {c : ℝ} (hc : B (111 / 200) (14 / 25) c) : B (-1494310445698994261439 / 1000000000000000000) (-1426109590940782246643 / 1000000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) / (2 : ℝ)) := bdiv (sGlobal42_hz88 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal42_hz90 {c : ℝ} (hc : B (111 / 200) (14 / 25) c) : B (-1494310445698994261439 / 1000000000000000000) (-1426109590940782246643 / 1000000000000000000) (s3Cpp 12225 c) := by
    convert (sGlobal42_hz89 hc) using 1 <;>
      norm_num [s3Cpp, mA] <;> ring

theorem sGlobal42_hz91 {c : ℝ} (hc : B (111 / 200) (14 / 25) c) : B (1769039012492356426093 / 250000000000000000) (3561931913613384416383 / 500000000000000000) ((s3Cpa 12225 c) + (s3r1 12225 46)) := badd (sGlobal42_hz84 hc) sGlobal42_hz33 (by norm_num) (by norm_num)

theorem sGlobal42_hz92 {c : ℝ} (hc : B (111 / 200) (14 / 25) c) : B (32035029536582223119 / 500000000000000000) (64502022428062555439 / 1000000000000000000) (((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) := bdiv (sGlobal42_hz91 hc) sGlobal42_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal42_hz93 {c : ℝ} (hc : B (111 / 200) (14 / 25) c) : B (1283854841973170133 / 20000000000000000) (32312352726778307931 / 500000000000000000) ((((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) + (s3e0 12225 46)) := badd (sGlobal42_hz92 hc) sGlobal42_hz16 (by norm_num) (by norm_num)

theorem sGlobal42_hz94 {c : ℝ} (hc : B (111 / 200) (14 / 25) c) : B (1283854841973170133 / 20000000000000000) (32312352726778307931 / 500000000000000000) (s3Lam 12225 46 c) := by
    convert (sGlobal42_hz93 hc) using 1 <;>
      norm_num [s3Lam] <;> ring

theorem sGlobal42_hz95 {c : ℝ} (hc : B (111 / 200) (14 / 25) c) : B (-1417547039076502455839 / 1000000000000000000) (-53973847372731598873 / 40000000000000000) ((s3Cpp 12225 c) + (s3rpp 12225 46)) := badd (sGlobal42_hz90 hc) sGlobal42_hz37 (by norm_num) (by norm_num)

theorem sGlobal42_hz96 {c : ℝ} (hc : B (111 / 200) (14 / 25) c) : B (-1031144395451376825397 / 1000000000000000000) (-84334136519893123239 / 125000000000000000) (if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) := bweaken (bfirst (sGlobal42_hz95 hc) (sGlobal42_hz76 hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem sGlobal42_hz97 {c : ℝ} (hc : B (111 / 200) (14 / 25) c) : B (412070813814488413671 / 100000000000000000) (2088176277479475103737 / 500000000000000000) ((s3Lam 12225 46 c)^2) := bsq (sGlobal42_hz94 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal42_hz98 {c : ℝ} (hc : B (111 / 200) (14 / 25) c) : B (13274630400947281 / 31250000000000000) (6707558461531383 / 15625000000000000) ((s3c1 12225 46 c)^2) := bsq (sGlobal42_hz72 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal42_hz99 {c : ℝ} (hc : B (111 / 200) (14 / 25) c) : B (8917441538468617 / 15625000000000000) (17975369599052719 / 31250000000000000) ((1 : ℝ) - ((s3c1 12225 46 c)^2)) := bsub (bpoint (1 : ℝ)) (sGlobal42_hz98 hc) (by norm_num) (by norm_num)

theorem sGlobal42_hz100 {c : ℝ} (hc : B (111 / 200) (14 / 25) c) : B (755457648357597533 / 1000000000000000000) (6067417649944659 / 8000000000000000) (√((1 : ℝ) - ((s3c1 12225 46 c)^2))) := bsqrt (sGlobal42_hz99 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal42_hz101 {c : ℝ} (hc : B (111 / 200) (14 / 25) c) : B (2373340198178449739 / 1000000000000000000) (7445841685674683 / 3125000000000000) (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))) := bmul pi_mem (sGlobal42_hz100 hc) (by norm_num) (by norm_num)

theorem sGlobal42_hz102 {c : ℝ} (hc : B (111 / 200) (14 / 25) c) : B (54045321013194209777 / 31250000000000000) (439923505084134304629 / 250000000000000000) (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2))))) := bdiv (sGlobal42_hz97 hc) (sGlobal42_hz101 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal42_hz103 {c : ℝ} (hc : B (111 / 200) (14 / 25) c) : B (698305876970837887467 / 1000000000000000000) (271255232044348058151 / 250000000000000000) ((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) := badd (sGlobal42_hz96 hc) (sGlobal42_hz102 hc) (by norm_num) (by norm_num)

theorem sGlobal42_hz104 : B (3762781186094069 / 250000000000000000) (376278118609407 / 25000000000000000) ((s3e0 12225 46)^2) := bsq sGlobal42_hz16 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal42_hz105 {c : ℝ} (hc : B (111 / 200) (14 / 25) c) : B (698320928095582263743 / 1000000000000000000) (271258994825534152221 / 250000000000000000) (((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) := badd (sGlobal42_hz103 hc) sGlobal42_hz104 (by norm_num) (by norm_num)

theorem sGlobal42_hz106 {c : ℝ} (hc : B (111 / 200) (14 / 25) c) : B (368409000773414766937 / 500000000000000000) (11235330527562608789 / 10000000000000000) ((((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) + (s3rs 12225 46 maskSlack)) := badd (sGlobal42_hz105 hc) sGlobal42_hz29 (by norm_num) (by norm_num)

theorem sGlobal42_hz107 {c : ℝ} (hc : B (111 / 200) (14 / 25) c) : B (368409000773414766937 / 500000000000000000) (11235330527562608789 / 10000000000000000) (s3U 12225 46 maskSlack c) := by
    convert (sGlobal42_hz106 hc) using 1 <;>
      norm_num [s3U] <;> ring

theorem sGlobal42_hz108 {c : ℝ} (hc : B (111 / 200) (14 / 25) c) : B (-1571073852321486536257 / 1000000000000000000) (-1502872997563274052243 / 1000000000000000000) ((s3Cpp 12225 c) - (s3rpp 12225 46)) := bsub (sGlobal42_hz90 hc) sGlobal42_hz37 (by norm_num) (by norm_num)

theorem sGlobal42_hz109 {c : ℝ} (hc : B (111 / 200) (14 / 25) c) : B (-1571073852321486536257 / 1000000000000000000) (-1502872997563274052243 / 1000000000000000000) (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ)) := bweaken (bmin (sGlobal42_hz108 hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem sGlobal42_hz110 {c : ℝ} (hc : B (111 / 200) (14 / 25) c) : B (-1142822039060445044801 / 1000000000000000000) (-109103787655118909859 / 100000000000000000) ((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) := bmul (sGlobal42_hz76 hc) (sGlobal42_hz109 hc) (by norm_num) (by norm_num)

theorem sGlobal42_hz111 {c : ℝ} (hc : B (111 / 200) (14 / 25) c) : B (-1142837090185189421081 / 1000000000000000000) (-545526463837966737433 / 500000000000000000) (((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) := bsub (sGlobal42_hz110 hc) sGlobal42_hz104 (by norm_num) (by norm_num)

theorem sGlobal42_hz112 {c : ℝ} (hc : B (111 / 200) (14 / 25) c) : B (-1181334163639313691097 / 1000000000000000000) (-1129550001127180744997 / 1000000000000000000) ((((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) - (s3rs 12225 46 maskSlack)) := bsub (sGlobal42_hz111 hc) sGlobal42_hz29 (by norm_num) (by norm_num)

theorem sGlobal42_hz113 {c : ℝ} (hc : B (111 / 200) (14 / 25) c) : B (-1181334163639313691097 / 1000000000000000000) (-1129550001127180744997 / 1000000000000000000) (s3L 12225 46 maskSlack c) := by
    convert (sGlobal42_hz112 hc) using 1 <;>
      norm_num [s3L] <;> ring

theorem sGlobal42_hz114 {c : ℝ} (hc : B (111 / 200) (14 / 25) c) : B 0 (11235330527562608789 / 10000000000000000) |(s3U 12225 46 maskSlack c)| := bweaken (babs (sGlobal42_hz107 hc)) (by norm_num) (by norm_num)

theorem sGlobal42_hz115 {c : ℝ} (hc : B (111 / 200) (14 / 25) c) : B 0 (1181334163639313691097 / 1000000000000000000) |(s3L 12225 46 maskSlack c)| := bweaken (babs (sGlobal42_hz113 hc)) (by norm_num) (by norm_num)

theorem sGlobal42_hz116 {c : ℝ} (hc : B (111 / 200) (14 / 25) c) : B 0 (1181334163639313691097 / 1000000000000000000) (max |(s3U 12225 46 maskSlack c)| |(s3L 12225 46 maskSlack c)|) := bweaken (bmax (sGlobal42_hz114 hc) (sGlobal42_hz115 hc)) (by norm_num) (by norm_num)

theorem sGlobal42_hz117 {c : ℝ} (hc : B (111 / 200) (14 / 25) c) : B 0 (1181334163639313691097 / 1000000000000000000) (s3nks 12225 46 maskSlack c) := by
    convert (sGlobal42_hz116 hc) using 1 <;>
      norm_num [s3nks] <;> ring

theorem sGlobal42 {c : ℝ} (hc : B (111 / 200) (14 / 25) c) :
    0 < s3am 12225 46 ∧ 0 ≤ s3dm 12225 46 c ∧
    s3dm 12225 46 c ^ 2 ≤ 2 * s3ap 12225 46 ^ 2 ∧ s3c1 12225 46 c < 1 ∧
    0 ≤ s3Cpa 12225 c - s3r1 12225 46 ∧
    s3e0 12225 46 ≤ (s3Cpa 12225 c - s3r1 12225 46) / s3ap 12225 46 ∧
    s3nks 12225 46 maskSlack c ≤ 12225 * (96633 / 1000000) := by

  refine ⟨lt_of_lt_of_le (by norm_num) sGlobal42_hz14.1,
    le_trans (by norm_num) (sGlobal42_hz64 hc).1, ?_,
    lt_of_le_of_lt (sGlobal42_hz72 hc).2 (by norm_num), ?_, ?_,
    le_trans (sGlobal42_hz117 hc).2 (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (sGlobal42_hz64 hc).1) (sGlobal42_hz64 hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) sGlobal42_hz9.1 2
    nlinarith only [h1, h2]
  · linarith only [(sGlobal42_hz84 hc).1, sGlobal42_hz33.2]
  · have hap : 0 < s3ap 12225 46 := lt_of_lt_of_le (by norm_num) sGlobal42_hz9.1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul sGlobal42_hz16.2 sGlobal42_hz9.2 (le_trans (by norm_num) sGlobal42_hz9.1) (by norm_num)
    linarith only [h, (sGlobal42_hz84 hc).1, sGlobal42_hz33.2]

end BstLean.Part255
