import BstLean.Part255SGlobal30
import BstLean.Part255Numeric10
namespace BstLean.Part255
open Real BstLean.Part130 BstLean.Part182 BstLean.Part197 BstLean.Part246
theorem sGlobal34_hz0 : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal34_hz1 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) ((√(23 : ℝ)) / (12225 : ℝ)) := bdiv sGlobal34_hz0 (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal34_hz2 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) maskSlack := by
    convert sGlobal34_hz1 using 1 <;>
      norm_num [maskSlack] <;> ring

theorem sGlobal34_hz3 : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal34_hz4 : B (6395294793910793 / 500000000000000000) (12790589587821587 / 1000000000000000000) (√((2 / 12225) : ℝ)) := bsqrt (bpoint ((2 / 12225) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal34_hz5 : B (7230130686979 / 62500000000000000) (23136418198333 / 200000000000000000) (√((2 / 149450625) : ℝ)) := bsqrt (bpoint ((2 / 149450625) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal34_hz6 : B (2211334438749598093 / 20000000000000000) (110566721937479904651 / 1000000000000000000) (√(12225 : ℝ)) := bsqrt (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal34_hz7 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))) := bmul sGlobal34_hz3 sGlobal34_hz4 (by norm_num) (by norm_num)

theorem sGlobal34_hz8 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) ((√(12225 : ℝ)) + ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := badd sGlobal34_hz6 sGlobal34_hz7 (by norm_num) (by norm_num)

theorem sGlobal34_hz9 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) (s3ap 12225 46) := by
    convert sGlobal34_hz8 using 1 <;>
      norm_num [s3ap, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal34_hz10 : B (163599182004089 / 1000000000000000000) (16359918200409 / 100000000000000000) ((2 : ℝ) / (12225 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal34_hz11 : B (1222499983640081799591 / 100000000000000000) (12224999836400817995911 / 1000000000000000000) ((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ))) := bsub (bpoint (12225 : ℝ)) sGlobal34_hz10 (by norm_num) (by norm_num)

theorem sGlobal34_hz12 : B (110566721197658827907 / 1000000000000000000) (27641680299414706977 / 250000000000000000) (√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) := bsqrt sGlobal34_hz11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal34_hz13 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) ((√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) - ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bsub sGlobal34_hz12 sGlobal34_hz7 (by norm_num) (by norm_num)

theorem sGlobal34_hz14 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) (s3am 12225 46) := by
    convert sGlobal34_hz13 using 1 <;>
      norm_num [s3am, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal34_hz15 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√((2 / 12225) : ℝ)) * (√(92 : ℝ))) := bmul sGlobal34_hz4 sGlobal34_hz3 (by norm_num) (by norm_num)

theorem sGlobal34_hz16 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) (s3e0 12225 46) := by
    convert sGlobal34_hz15 using 1 <;>
      norm_num [s3e0, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal34_hz17 : B (250196148528560847 / 500000000000000000) (100078459411424339 / 200000000000000000) (((1 / 2) : ℝ) + maskSlack) := badd (bpoint ((1 / 2) : ℝ)) sGlobal34_hz2 (by norm_num) (by norm_num)

theorem sGlobal34_hz18 : B (59827153232297998295487 / 800000000000000) (23930861292919199366019 / 320000000000000) ((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack)) := bmul (bpoint (149450625 : ℝ)) sGlobal34_hz17 (by norm_num) (by norm_num)

theorem sGlobal34_hz19 : B (1729554180017180009583 / 200000000000000000) (8647770900085900056557 / 1000000000000000000) (√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) := bsqrt sGlobal34_hz18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal34_hz20 : B (4328681281566262743499 / 500000000000000000) (8657362563132525495641 / 1000000000000000000) ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))) := badd sGlobal34_hz19 sGlobal34_hz3 (by norm_num) (by norm_num)

theorem sGlobal34_hz21 : B (110732771457999278473 / 1000000000000000000) (55366385728999643621 / 500000000000000000) ((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ)))) := bmul sGlobal34_hz4 sGlobal34_hz20 (by norm_num) (by norm_num)

theorem sGlobal34_hz22 : B (209099159 / 15625000000000000) (13382346177 / 1000000000000000000) ((2 : ℝ) / (149450625 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (149450625 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal34_hz23 : B (2452349334953899930479 / 200000000000000000) (12261746674769501594427 / 1000000000000000000) (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2) := bsq sGlobal34_hz21 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal34_hz24 : B (82045469362091 / 500000000000000000) (32818187747289 / 200000000000000000) (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2)) := bmul sGlobal34_hz22 sGlobal34_hz23 (by norm_num) (by norm_num)

theorem sGlobal34_hz25 : B (82045469362091 / 250000000000000000) (32818187747289 / 100000000000000000) ((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) := bmul (bpoint (2 : ℝ)) sGlobal34_hz24 (by norm_num) (by norm_num)

theorem sGlobal34_hz26 : B (117258080744995992792057 / 1000000000000000000) (58629040372497996396029 / 500000000000000000) (√(13749457500 : ℝ)) := bsqrt (bpoint (13749457500 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal34_hz27 : B (117304080744995992792057 / 1000000000000000000) (58652040372497996396029 / 500000000000000000) ((√(13749457500 : ℝ)) + (46 : ℝ)) := badd sGlobal34_hz26 (bpoint (46 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal34_hz28 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal34_hz25 sGlobal34_hz27 (by norm_num) (by norm_num)

theorem sGlobal34_hz29 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (s3rs 12225 46 maskSlack) := by
    convert sGlobal34_hz28 using 1 <;>
      norm_num [s3rs, s3pp, s3K, mA, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal34_hz30 : B (490797546012267 / 1000000000000000000) (49079754601227 / 100000000000000000) ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (3 : ℝ)) sGlobal34_hz10 (by norm_num) (by norm_num)

theorem sGlobal34_hz31 : B (490797546012267 / 500000000000000000) (49079754601227 / 50000000000000000) ((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal34_hz30 (by norm_num) (by norm_num)

theorem sGlobal34_hz32 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal34_hz31 sGlobal34_hz27 (by norm_num) (by norm_num)

theorem sGlobal34_hz33 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (s3r1 12225 46) := by
    convert sGlobal34_hz32 using 1 <;>
      norm_num [s3r1, mA] <;> ring

theorem sGlobal34_hz34 : B (163599182004089 / 500000000000000000) (16359918200409 / 50000000000000000) ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (2 : ℝ)) sGlobal34_hz10 (by norm_num) (by norm_num)

theorem sGlobal34_hz35 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal34_hz34 (by norm_num) (by norm_num)

theorem sGlobal34_hz36 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal34_hz35 sGlobal34_hz27 (by norm_num) (by norm_num)

theorem sGlobal34_hz37 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (s3rpp 12225 46) := by
    convert sGlobal34_hz36 using 1 <;>
      norm_num [s3rpp, mA] <;> ring

theorem sGlobal34_hz38 {c : ℝ} (hc : B (103 / 200) (13 / 25) c) : B (103 / 200) (13 / 25) c := hc

theorem sGlobal34_hz39 : B (336104041628554777 / 500000000000000000) (672208083257129293 / 1000000000000000000) (kdot ((103 / 200))) := by
    constructor
    · apply bkdot_lower (q := (141450524301193413 / 250000000000000000)) (a := (102978867754558177 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (565802097204773651 / 1000000000000000000)) (a := (514894338772759881 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal34_hz40 : B (10609 / 40000) (10609 / 40000) (((103 / 200) : ℝ)^2) := bsq (bpoint ((103 / 200) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal34_hz41 : B (29391 / 40000) (29391 / 40000) ((1 : ℝ) - (((103 / 200) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal34_hz40 (by norm_num) (by norm_num)

theorem sGlobal34_hz42 : B (428595088632616041 / 500000000000000000) (857190177265232083 / 1000000000000000000) (√((1 : ℝ) - (((103 / 200) : ℝ)^2))) := bsqrt sGlobal34_hz41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal34_hz43 : B (136426053881579687 / 500000000000000000) (87312674484211 / 320000000000000) ((√((1 : ℝ) - (((103 / 200) : ℝ)^2))) / Real.pi) := bdiv sGlobal34_hz42 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal34_hz44 : B (17309358143870571 / 50000000000000000) (173093581438710793 / 500000000000000000) (((103 / 200) : ℝ) * (kdot ((103 / 200)))) := bmul (bpoint ((103 / 200) : ℝ)) sGlobal34_hz39 (by norm_num) (by norm_num)

theorem sGlobal34_hz45 : B (309519635320285397 / 500000000000000000) (619039270640580961 / 1000000000000000000) (((√((1 : ℝ) - (((103 / 200) : ℝ)^2))) / Real.pi) + (((103 / 200) : ℝ) * (kdot ((103 / 200))))) := badd sGlobal34_hz43 sGlobal34_hz44 (by norm_num) (by norm_num)

theorem sGlobal34_hz46 : B (309519635320285397 / 500000000000000000) (619039270640580961 / 1000000000000000000) (kappa ((103 / 200))) := by rw [kappa_eq]; exact sGlobal34_hz45

theorem sGlobal34_hz47 : B (674068063875522049 / 1000000000000000000) (26962722555021447 / 40000000000000000) (kdot ((13 / 25))) := by
    constructor
    · apply bkdot_lower (q := (28097574347450819 / 50000000000000000)) (a := (255986344024739419 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (561951486949016379 / 1000000000000000000)) (a := (10239453760989133 / 20000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal34_hz48 : B (169 / 625) (169 / 625) (((13 / 25) : ℝ)^2) := bsq (bpoint ((13 / 25) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal34_hz49 : B (456 / 625) (456 / 625) ((1 : ℝ) - (((13 / 25) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal34_hz48 (by norm_num) (by norm_num)

theorem sGlobal34_hz50 : B (13346347815039139 / 15625000000000000) (854166260162504897 / 1000000000000000000) (√((1 : ℝ) - (((13 / 25) : ℝ)^2))) := bsqrt sGlobal34_hz49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal34_hz51 : B (54377913010872213 / 200000000000000000) (135944782527180533 / 500000000000000000) ((√((1 : ℝ) - (((13 / 25) : ℝ)^2))) / Real.pi) := bdiv sGlobal34_hz50 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal34_hz52 : B (70103078643054293 / 200000000000000000) (350515393215278811 / 1000000000000000000) (((13 / 25) : ℝ) * (kdot ((13 / 25)))) := bmul (bpoint ((13 / 25) : ℝ)) sGlobal34_hz47 (by norm_num) (by norm_num)

theorem sGlobal34_hz53 : B (62240495826963253 / 100000000000000000) (622404958269639877 / 1000000000000000000) (((√((1 : ℝ) - (((13 / 25) : ℝ)^2))) / Real.pi) + (((13 / 25) : ℝ) * (kdot ((13 / 25))))) := badd sGlobal34_hz51 sGlobal34_hz52 (by norm_num) (by norm_num)

theorem sGlobal34_hz54 : B (62240495826963253 / 100000000000000000) (622404958269639877 / 1000000000000000000) (kappa ((13 / 25))) := by rw [kappa_eq]; exact sGlobal34_hz53

theorem sGlobal34_hz55 {c : ℝ} (hc : B (103 / 200) (13 / 25) c) : B (309519635320285397 / 500000000000000000) (622404958269639877 / 1000000000000000000) (kappa c) := bkappa (sGlobal34_hz38 hc) (by norm_num) (by norm_num) sGlobal34_hz46.1 sGlobal34_hz54.2

theorem sGlobal34_hz56 : B 24450 24450 ((2 : ℝ) * (12225 : ℝ)) := bmul (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal34_hz57 {c : ℝ} (hc : B (103 / 200) (13 / 25) c) : B (377595041730360123 / 1000000000000000000) (190480364679714603 / 500000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (sGlobal34_hz55 hc) (by norm_num) (by norm_num)

theorem sGlobal34_hz58 {c : ℝ} (hc : B (103 / 200) (13 / 25) c) : B (184643975406146100147 / 20000000000000000) (93144898328380440867 / 10000000000000000) (((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) := bmul sGlobal34_hz56 (sGlobal34_hz57 hc) (by norm_num) (by norm_num)

theorem sGlobal34_hz59 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (4 : ℝ)) sGlobal34_hz10 (by norm_num) (by norm_num)

theorem sGlobal34_hz60 {c : ℝ} (hc : B (103 / 200) (13 / 25) c) : B (923219811591057699099 / 100000000000000000) (1164311147305164508793 / 125000000000000000) ((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bsub (sGlobal34_hz58 hc) sGlobal34_hz59 (by norm_num) (by norm_num)

theorem sGlobal34_hz61 {c : ℝ} (hc : B (103 / 200) (13 / 25) c) : B (96084328149342736563 / 1000000000000000000) (19302320252696374813 / 200000000000000000) (√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) := bsqrt (sGlobal34_hz60 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal34_hz62 : B (30670756373515103 / 125000000000000000) (122683025494060423 / 500000000000000000) ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal34_hz7 (by norm_num) (by norm_num)

theorem sGlobal34_hz63 {c : ℝ} (hc : B (103 / 200) (13 / 25) c) : B (95838962098354615717 / 1000000000000000000) (96266235212493753241 / 1000000000000000000) ((√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) - ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))))) := bsub (sGlobal34_hz61 hc) sGlobal34_hz62 (by norm_num) (by norm_num)

theorem sGlobal34_hz64 {c : ℝ} (hc : B (103 / 200) (13 / 25) c) : B (95838962098354615717 / 1000000000000000000) (96266235212493753241 / 1000000000000000000) (s3dm 12225 46 c) := by
    convert (sGlobal34_hz63 hc) using 1 <;>
      norm_num [s3dm, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal34_hz65 : B (6126072185528622723889 / 500000000000000000) (2450428874211449090087 / 200000000000000000) ((s3ap 12225 46)^2) := bsq sGlobal34_hz9 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal34_hz66 : B (6126072185528622723889 / 250000000000000000) (2450428874211449090087 / 100000000000000000) ((2 : ℝ) * ((s3ap 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal34_hz65 (by norm_num) (by norm_num)

theorem sGlobal34_hz67 {c : ℝ} (hc : B (103 / 200) (13 / 25) c) : B (73480853248718820529 / 8000000000000000) (4633594020993586108107 / 500000000000000000) ((s3dm 12225 46 c)^2) := bsq (sGlobal34_hz64 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal34_hz68 {c : ℝ} (hc : B (103 / 200) (13 / 25) c) : B (7618550350063659339671 / 500000000000000000) (3063836417204927666949 / 200000000000000000) (((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) := bsub sGlobal34_hz66 (sGlobal34_hz67 hc) (by norm_num) (by norm_num)

theorem sGlobal34_hz69 : B (1524735695971823534271 / 125000000000000000) (609894278388729413841 / 50000000000000000) ((s3am 12225 46)^2) := bsq sGlobal34_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal34_hz70 : B (1524735695971823534271 / 62500000000000000) (609894278388729413841 / 25000000000000000) ((2 : ℝ) * ((s3am 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal34_hz69 (by norm_num) (by norm_num)

theorem sGlobal34_hz71 {c : ℝ} (hc : B (103 / 200) (13 / 25) c) : B (39036224289309379 / 62500000000000000) (313972081491241333 / 500000000000000000) ((((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) / ((2 : ℝ) * ((s3am 12225 46)^2))) := bdiv (sGlobal34_hz68 hc) sGlobal34_hz70 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal34_hz72 {c : ℝ} (hc : B (103 / 200) (13 / 25) c) : B (39036224289309379 / 62500000000000000) (313972081491241333 / 500000000000000000) (s3c1 12225 46 c) := by
    convert (sGlobal34_hz71 hc) using 1 <;>
      norm_num [s3c1] <;> ring

theorem sGlobal34_hz73 {c : ℝ} (hc : B (103 / 200) (13 / 25) c) : B (336104041628554777 / 500000000000000000) (26962722555021447 / 40000000000000000) (kdot c) := bkdot (sGlobal34_hz38 hc) sGlobal34_hz39.1 sGlobal34_hz47.2

theorem sGlobal34_hz74 : B (71472965014331161 / 100000000000000000) (35736482507165581 / 50000000000000000) (kdot ((39036224289309379 / 62500000000000000))) := by
    constructor
    · apply bkdot_lower (q := (96143170584255709 / 200000000000000000)) (a := (89620323539676237 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (30044740807579909 / 62500000000000000)) (a := (112025404424595293 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal34_hz75 : B (358051691531594963 / 500000000000000000) (716103383063189933 / 1000000000000000000) (kdot ((313972081491241333 / 500000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (59757761654098219 / 125000000000000000)) (a := (445943763073839099 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (478062093232785751 / 1000000000000000000)) (a := (445943763073839089 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal34_hz76 {c : ℝ} (hc : B (103 / 200) (13 / 25) c) : B (71472965014331161 / 100000000000000000) (716103383063189933 / 1000000000000000000) (kdot (s3c1 12225 46 c)) := bkdot (sGlobal34_hz72 hc) sGlobal34_hz74.1 sGlobal34_hz75.2

theorem sGlobal34_hz77 {c : ℝ} (hc : B (103 / 200) (13 / 25) c) : B (10609 / 40000) (169 / 625) (c^2) := bsq (sGlobal34_hz38 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal34_hz78 {c : ℝ} (hc : B (103 / 200) (13 / 25) c) : B (456 / 625) (29391 / 40000) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (sGlobal34_hz77 hc) (by norm_num) (by norm_num)

theorem sGlobal34_hz79 {c : ℝ} (hc : B (103 / 200) (13 / 25) c) : B (13346347815039139 / 15625000000000000) (857190177265232083 / 1000000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (sGlobal34_hz78 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal34_hz80 : B (39119999999999765769 / 1600000000000000) (3912000000000000489 / 160000000000000) ((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (149450625 : ℝ)) sGlobal34_hz10 (by norm_num) (by norm_num)

theorem sGlobal34_hz81 {c : ℝ} (hc : B (103 / 200) (13 / 25) c) : B (57417746452673099 / 100000000000000000) (577804523162302637 / 1000000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (sGlobal34_hz79 hc) (sGlobal34_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal34_hz82 {c : ℝ} (hc : B (103 / 200) (13 / 25) c) : B (3509659751919622162287 / 250000000000000000) (7063660295659150620283 / 500000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) := bmul sGlobal34_hz80 (sGlobal34_hz81 hc) (by norm_num) (by norm_num)

theorem sGlobal34_hz83 {c : ℝ} (hc : B (103 / 200) (13 / 25) c) : B (3509659751919622162287 / 500000000000000000) (7063660295659150620283 / 1000000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) / (2 : ℝ)) := bdiv (sGlobal34_hz82 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal34_hz84 {c : ℝ} (hc : B (103 / 200) (13 / 25) c) : B (3509659751919622162287 / 500000000000000000) (7063660295659150620283 / 1000000000000000000) (s3Cpa 12225 c) := by
    convert (sGlobal34_hz83 hc) using 1 <;>
      norm_num [s3Cpa, mA] <;> ring

theorem sGlobal34_hz85 {c : ℝ} (hc : B (103 / 200) (13 / 25) c) : B (54377913010872213 / 200000000000000000) (87312674484211 / 320000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (sGlobal34_hz79 hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal34_hz86 {c : ℝ} (hc : B (103 / 200) (13 / 25) c) : B (17309358143870571 / 50000000000000000) (350515393215278811 / 1000000000000000000) (c * (kdot c)) := bmul (sGlobal34_hz38 hc) (sGlobal34_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal34_hz87 {c : ℝ} (hc : B (103 / 200) (13 / 25) c) : B (-39312914080458873 / 500000000000000000) (-14667011022850409 / 200000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (sGlobal34_hz85 hc) (sGlobal34_hz86 hc) (by norm_num) (by norm_num)

theorem sGlobal34_hz88 {c : ℝ} (hc : B (103 / 200) (13 / 25) c) : B (-1922401498534439130001 / 1000000000000000000) (-179304209754345176441 / 100000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) := bmul sGlobal34_hz80 (sGlobal34_hz87 hc) (by norm_num) (by norm_num)

theorem sGlobal34_hz89 {c : ℝ} (hc : B (103 / 200) (13 / 25) c) : B (-961200749267219565001 / 1000000000000000000) (-179304209754345176441 / 200000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) / (2 : ℝ)) := bdiv (sGlobal34_hz88 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal34_hz90 {c : ℝ} (hc : B (103 / 200) (13 / 25) c) : B (-961200749267219565001 / 1000000000000000000) (-179304209754345176441 / 200000000000000000) (s3Cpp 12225 c) := by
    convert (sGlobal34_hz89 hc) using 1 <;>
      norm_num [s3Cpp, mA] <;> ring

theorem sGlobal34_hz91 {c : ℝ} (hc : B (103 / 200) (13 / 25) c) : B (285378584550919281319 / 40000000000000000) (7178805405592889032509 / 1000000000000000000) ((s3Cpa 12225 c) + (s3r1 12225 46)) := badd (sGlobal34_hz84 hc) sGlobal34_hz33 (by norm_num) (by norm_num)

theorem sGlobal34_hz92 {c : ℝ} (hc : B (103 / 200) (13 / 25) c) : B (16149501439478972579 / 250000000000000000) (64999483217032214251 / 1000000000000000000) (((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) := bdiv (sGlobal34_hz91 hc) sGlobal34_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal34_hz93 {c : ℝ} (hc : B (103 / 200) (13 / 25) c) : B (8090086097926243841 / 125000000000000000) (32561083121263137337 / 500000000000000000) ((((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) + (s3e0 12225 46)) := badd (sGlobal34_hz92 hc) sGlobal34_hz16 (by norm_num) (by norm_num)

theorem sGlobal34_hz94 {c : ℝ} (hc : B (103 / 200) (13 / 25) c) : B (8090086097926243841 / 125000000000000000) (32561083121263137337 / 500000000000000000) (s3Lam 12225 46 c) := by
    convert (sGlobal34_hz93 hc) using 1 <;>
      norm_num [s3Lam] <;> ring

theorem sGlobal34_hz95 {c : ℝ} (hc : B (103 / 200) (13 / 25) c) : B (-884437342644727759401 / 1000000000000000000) (-819757642149233607387 / 1000000000000000000) ((s3Cpp 12225 c) + (s3rpp 12225 46)) := badd (sGlobal34_hz90 hc) sGlobal34_hz37 (by norm_num) (by norm_num)

theorem sGlobal34_hz96 {c : ℝ} (hc : B (103 / 200) (13 / 25) c) : B (-316674286587653626023 / 500000000000000000) (-409878821074616803693 / 1000000000000000000) (if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) := bweaken (bfirst (sGlobal34_hz95 hc) (sGlobal34_hz76 hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem sGlobal34_hz97 {c : ℝ} (hc : B (103 / 200) (13 / 25) c) : B (837753511319801321611 / 200000000000000000) (4240896536119228696183 / 1000000000000000000) ((s3Lam 12225 46 c)^2) := bsq (sGlobal34_hz94 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal34_hz98 {c : ℝ} (hc : B (103 / 200) (13 / 25) c) : B (48762457816488561 / 125000000000000000) (197156935911885377 / 500000000000000000) ((s3c1 12225 46 c)^2) := bsq (sGlobal34_hz72 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal34_hz99 {c : ℝ} (hc : B (103 / 200) (13 / 25) c) : B (302843064088114623 / 500000000000000000) (76237542183511439 / 125000000000000000) ((1 : ℝ) - ((s3c1 12225 46 c)^2)) := bsub (bpoint (1 : ℝ)) (sGlobal34_hz98 hc) (by norm_num) (by norm_num)

theorem sGlobal34_hz100 {c : ℝ} (hc : B (103 / 200) (13 / 25) c) : B (77825839422150099 / 100000000000000000) (390480581293132781 / 500000000000000000) (√((1 : ℝ) - ((s3c1 12225 46 c)^2))) := bsqrt (sGlobal34_hz99 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal34_hz101 {c : ℝ} (hc : B (103 / 200) (13 / 25) c) : B (2444970853880856703 / 1000000000000000000) (1226730925559977991 / 500000000000000000) (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))) := bmul pi_mem (sGlobal34_hz100 hc) (by norm_num) (by norm_num)

theorem sGlobal34_hz102 {c : ℝ} (hc : B (103 / 200) (13 / 25) c) : B (341457728775111663411 / 200000000000000000) (867269343801733383403 / 500000000000000000) (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2))))) := bdiv (sGlobal34_hz97 hc) (sGlobal34_hz101 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal34_hz103 {c : ℝ} (hc : B (103 / 200) (13 / 25) c) : B (1073940070700251065009 / 1000000000000000000) (1324659866528849963113 / 1000000000000000000) ((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) := badd (sGlobal34_hz96 hc) (sGlobal34_hz102 hc) (by norm_num) (by norm_num)

theorem sGlobal34_hz104 : B (3762781186094069 / 250000000000000000) (376278118609407 / 25000000000000000) ((s3e0 12225 46)^2) := bsq sGlobal34_hz16 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal34_hz105 {c : ℝ} (hc : B (103 / 200) (13 / 25) c) : B (214791024364999088257 / 200000000000000000) (1324674917653594339393 / 1000000000000000000) (((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) := badd (sGlobal34_hz103 hc) sGlobal34_hz104 (by norm_num) (by norm_num)

theorem sGlobal34_hz106 {c : ℝ} (hc : B (103 / 200) (13 / 25) c) : B (139056524409530338927 / 125000000000000000) (1363171991107718609409 / 1000000000000000000) ((((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) + (s3rs 12225 46 maskSlack)) := badd (sGlobal34_hz105 hc) sGlobal34_hz29 (by norm_num) (by norm_num)

theorem sGlobal34_hz107 {c : ℝ} (hc : B (103 / 200) (13 / 25) c) : B (139056524409530338927 / 125000000000000000) (1363171991107718609409 / 1000000000000000000) (s3U 12225 46 maskSlack c) := by
    convert (sGlobal34_hz106 hc) using 1 <;>
      norm_num [s3U] <;> ring

theorem sGlobal34_hz108 {c : ℝ} (hc : B (103 / 200) (13 / 25) c) : B (-1037964155889711839819 / 1000000000000000000) (-194656891078843537561 / 200000000000000000) ((s3Cpp 12225 c) - (s3rpp 12225 46)) := bsub (sGlobal34_hz90 hc) sGlobal34_hz37 (by norm_num) (by norm_num)

theorem sGlobal34_hz109 {c : ℝ} (hc : B (103 / 200) (13 / 25) c) : B (-1037964155889711839819 / 1000000000000000000) (-194656891078843537561 / 200000000000000000) (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ)) := bweaken (bmin (sGlobal34_hz108 hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem sGlobal34_hz110 {c : ℝ} (hc : B (103 / 200) (13 / 25) c) : B (-743289643530950908857 / 1000000000000000000) (-695635258293832782319 / 1000000000000000000) ((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) := bmul (sGlobal34_hz76 hc) (sGlobal34_hz109 hc) (by norm_num) (by norm_num)

theorem sGlobal34_hz111 {c : ℝ} (hc : B (103 / 200) (13 / 25) c) : B (-743304694655695285137 / 1000000000000000000) (-139130061883715431719 / 200000000000000000) (((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) := bsub (sGlobal34_hz110 hc) sGlobal34_hz104 (by norm_num) (by norm_num)

theorem sGlobal34_hz112 {c : ℝ} (hc : B (103 / 200) (13 / 25) c) : B (-781801768109819555153 / 1000000000000000000) (-367073691434912214363 / 500000000000000000) ((((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) - (s3rs 12225 46 maskSlack)) := bsub (sGlobal34_hz111 hc) sGlobal34_hz29 (by norm_num) (by norm_num)

theorem sGlobal34_hz113 {c : ℝ} (hc : B (103 / 200) (13 / 25) c) : B (-781801768109819555153 / 1000000000000000000) (-367073691434912214363 / 500000000000000000) (s3L 12225 46 maskSlack c) := by
    convert (sGlobal34_hz112 hc) using 1 <;>
      norm_num [s3L] <;> ring

theorem sGlobal34_hz114 {c : ℝ} (hc : B (103 / 200) (13 / 25) c) : B 0 (1363171991107718609409 / 1000000000000000000) |(s3U 12225 46 maskSlack c)| := bweaken (babs (sGlobal34_hz107 hc)) (by norm_num) (by norm_num)

theorem sGlobal34_hz115 {c : ℝ} (hc : B (103 / 200) (13 / 25) c) : B 0 (781801768109819555153 / 1000000000000000000) |(s3L 12225 46 maskSlack c)| := bweaken (babs (sGlobal34_hz113 hc)) (by norm_num) (by norm_num)

theorem sGlobal34_hz116 {c : ℝ} (hc : B (103 / 200) (13 / 25) c) : B 0 (1363171991107718609409 / 1000000000000000000) (max |(s3U 12225 46 maskSlack c)| |(s3L 12225 46 maskSlack c)|) := bweaken (bmax (sGlobal34_hz114 hc) (sGlobal34_hz115 hc)) (by norm_num) (by norm_num)

theorem sGlobal34_hz117 {c : ℝ} (hc : B (103 / 200) (13 / 25) c) : B 0 (1363171991107718609409 / 1000000000000000000) (s3nks 12225 46 maskSlack c) := by
    convert (sGlobal34_hz116 hc) using 1 <;>
      norm_num [s3nks] <;> ring

theorem sGlobal34 {c : ℝ} (hc : B (103 / 200) (13 / 25) c) :
    0 < s3am 12225 46 ∧ 0 ≤ s3dm 12225 46 c ∧
    s3dm 12225 46 c ^ 2 ≤ 2 * s3ap 12225 46 ^ 2 ∧ s3c1 12225 46 c < 1 ∧
    0 ≤ s3Cpa 12225 c - s3r1 12225 46 ∧
    s3e0 12225 46 ≤ (s3Cpa 12225 c - s3r1 12225 46) / s3ap 12225 46 ∧
    s3nks 12225 46 maskSlack c ≤ 12225 * (111507 / 1000000) := by

  refine ⟨lt_of_lt_of_le (by norm_num) sGlobal34_hz14.1,
    le_trans (by norm_num) (sGlobal34_hz64 hc).1, ?_,
    lt_of_le_of_lt (sGlobal34_hz72 hc).2 (by norm_num), ?_, ?_,
    le_trans (sGlobal34_hz117 hc).2 (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (sGlobal34_hz64 hc).1) (sGlobal34_hz64 hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) sGlobal34_hz9.1 2
    nlinarith only [h1, h2]
  · linarith only [(sGlobal34_hz84 hc).1, sGlobal34_hz33.2]
  · have hap : 0 < s3ap 12225 46 := lt_of_lt_of_le (by norm_num) sGlobal34_hz9.1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul sGlobal34_hz16.2 sGlobal34_hz9.2 (le_trans (by norm_num) sGlobal34_hz9.1) (by norm_num)
    linarith only [h, (sGlobal34_hz84 hc).1, sGlobal34_hz33.2]

end BstLean.Part255
