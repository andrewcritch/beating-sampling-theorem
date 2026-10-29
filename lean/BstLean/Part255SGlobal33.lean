import BstLean.Part255SGlobal29
import BstLean.Part255Numeric10
namespace BstLean.Part255
open Real BstLean.Part130 BstLean.Part182 BstLean.Part197 BstLean.Part246
theorem sGlobal33_hz0 : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal33_hz1 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) ((√(23 : ℝ)) / (12225 : ℝ)) := bdiv sGlobal33_hz0 (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal33_hz2 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) maskSlack := by
    convert sGlobal33_hz1 using 1 <;>
      norm_num [maskSlack] <;> ring

theorem sGlobal33_hz3 : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal33_hz4 : B (6395294793910793 / 500000000000000000) (12790589587821587 / 1000000000000000000) (√((2 / 12225) : ℝ)) := bsqrt (bpoint ((2 / 12225) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal33_hz5 : B (7230130686979 / 62500000000000000) (23136418198333 / 200000000000000000) (√((2 / 149450625) : ℝ)) := bsqrt (bpoint ((2 / 149450625) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal33_hz6 : B (2211334438749598093 / 20000000000000000) (110566721937479904651 / 1000000000000000000) (√(12225 : ℝ)) := bsqrt (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal33_hz7 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))) := bmul sGlobal33_hz3 sGlobal33_hz4 (by norm_num) (by norm_num)

theorem sGlobal33_hz8 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) ((√(12225 : ℝ)) + ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := badd sGlobal33_hz6 sGlobal33_hz7 (by norm_num) (by norm_num)

theorem sGlobal33_hz9 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) (s3ap 12225 46) := by
    convert sGlobal33_hz8 using 1 <;>
      norm_num [s3ap, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal33_hz10 : B (163599182004089 / 1000000000000000000) (16359918200409 / 100000000000000000) ((2 : ℝ) / (12225 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal33_hz11 : B (1222499983640081799591 / 100000000000000000) (12224999836400817995911 / 1000000000000000000) ((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ))) := bsub (bpoint (12225 : ℝ)) sGlobal33_hz10 (by norm_num) (by norm_num)

theorem sGlobal33_hz12 : B (110566721197658827907 / 1000000000000000000) (27641680299414706977 / 250000000000000000) (√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) := bsqrt sGlobal33_hz11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal33_hz13 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) ((√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) - ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bsub sGlobal33_hz12 sGlobal33_hz7 (by norm_num) (by norm_num)

theorem sGlobal33_hz14 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) (s3am 12225 46) := by
    convert sGlobal33_hz13 using 1 <;>
      norm_num [s3am, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal33_hz15 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√((2 / 12225) : ℝ)) * (√(92 : ℝ))) := bmul sGlobal33_hz4 sGlobal33_hz3 (by norm_num) (by norm_num)

theorem sGlobal33_hz16 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) (s3e0 12225 46) := by
    convert sGlobal33_hz15 using 1 <;>
      norm_num [s3e0, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal33_hz17 : B (250196148528560847 / 500000000000000000) (100078459411424339 / 200000000000000000) (((1 / 2) : ℝ) + maskSlack) := badd (bpoint ((1 / 2) : ℝ)) sGlobal33_hz2 (by norm_num) (by norm_num)

theorem sGlobal33_hz18 : B (59827153232297998295487 / 800000000000000) (23930861292919199366019 / 320000000000000) ((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack)) := bmul (bpoint (149450625 : ℝ)) sGlobal33_hz17 (by norm_num) (by norm_num)

theorem sGlobal33_hz19 : B (1729554180017180009583 / 200000000000000000) (8647770900085900056557 / 1000000000000000000) (√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) := bsqrt sGlobal33_hz18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal33_hz20 : B (4328681281566262743499 / 500000000000000000) (8657362563132525495641 / 1000000000000000000) ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))) := badd sGlobal33_hz19 sGlobal33_hz3 (by norm_num) (by norm_num)

theorem sGlobal33_hz21 : B (110732771457999278473 / 1000000000000000000) (55366385728999643621 / 500000000000000000) ((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ)))) := bmul sGlobal33_hz4 sGlobal33_hz20 (by norm_num) (by norm_num)

theorem sGlobal33_hz22 : B (209099159 / 15625000000000000) (13382346177 / 1000000000000000000) ((2 : ℝ) / (149450625 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (149450625 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal33_hz23 : B (2452349334953899930479 / 200000000000000000) (12261746674769501594427 / 1000000000000000000) (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2) := bsq sGlobal33_hz21 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal33_hz24 : B (82045469362091 / 500000000000000000) (32818187747289 / 200000000000000000) (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2)) := bmul sGlobal33_hz22 sGlobal33_hz23 (by norm_num) (by norm_num)

theorem sGlobal33_hz25 : B (82045469362091 / 250000000000000000) (32818187747289 / 100000000000000000) ((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) := bmul (bpoint (2 : ℝ)) sGlobal33_hz24 (by norm_num) (by norm_num)

theorem sGlobal33_hz26 : B (117258080744995992792057 / 1000000000000000000) (58629040372497996396029 / 500000000000000000) (√(13749457500 : ℝ)) := bsqrt (bpoint (13749457500 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal33_hz27 : B (117304080744995992792057 / 1000000000000000000) (58652040372497996396029 / 500000000000000000) ((√(13749457500 : ℝ)) + (46 : ℝ)) := badd sGlobal33_hz26 (bpoint (46 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal33_hz28 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal33_hz25 sGlobal33_hz27 (by norm_num) (by norm_num)

theorem sGlobal33_hz29 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (s3rs 12225 46 maskSlack) := by
    convert sGlobal33_hz28 using 1 <;>
      norm_num [s3rs, s3pp, s3K, mA, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal33_hz30 : B (490797546012267 / 1000000000000000000) (49079754601227 / 100000000000000000) ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (3 : ℝ)) sGlobal33_hz10 (by norm_num) (by norm_num)

theorem sGlobal33_hz31 : B (490797546012267 / 500000000000000000) (49079754601227 / 50000000000000000) ((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal33_hz30 (by norm_num) (by norm_num)

theorem sGlobal33_hz32 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal33_hz31 sGlobal33_hz27 (by norm_num) (by norm_num)

theorem sGlobal33_hz33 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (s3r1 12225 46) := by
    convert sGlobal33_hz32 using 1 <;>
      norm_num [s3r1, mA] <;> ring

theorem sGlobal33_hz34 : B (163599182004089 / 500000000000000000) (16359918200409 / 50000000000000000) ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (2 : ℝ)) sGlobal33_hz10 (by norm_num) (by norm_num)

theorem sGlobal33_hz35 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal33_hz34 (by norm_num) (by norm_num)

theorem sGlobal33_hz36 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal33_hz35 sGlobal33_hz27 (by norm_num) (by norm_num)

theorem sGlobal33_hz37 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (s3rpp 12225 46) := by
    convert sGlobal33_hz36 using 1 <;>
      norm_num [s3rpp, mA] <;> ring

theorem sGlobal33_hz38 {c : ℝ} (hc : B (51 / 100) (103 / 200) c) : B (51 / 100) (103 / 200) c := hc

theorem sGlobal33_hz39 : B (335177304839959399 / 500000000000000000) (167588652419986579 / 250000000000000000) (kdot ((51 / 100))) := by
    constructor
    · apply bkdot_lower (q := (569651921139811611 / 1000000000000000000)) (a := (258902884129826761 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (56965192113981161 / 100000000000000000)) (a := (258902884129805149 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal33_hz40 : B (2601 / 10000) (2601 / 10000) (((51 / 100) : ℝ)^2) := bsq (bpoint ((51 / 100) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal33_hz41 : B (7399 / 10000) (7399 / 10000) ((1 : ℝ) - (((51 / 100) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal33_hz40 (by norm_num) (by norm_num)

theorem sGlobal33_hz42 : B (860174400921115531 / 1000000000000000000) (215043600230278883 / 250000000000000000) (√((1 : ℝ) - (((51 / 100) : ℝ)^2))) := bsqrt sGlobal33_hz41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal33_hz43 : B (27380201565541061 / 100000000000000000) (273802015655410611 / 1000000000000000000) ((√((1 : ℝ) - (((51 / 100) : ℝ)^2))) / Real.pi) := bdiv sGlobal33_hz42 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal33_hz44 : B (170940425468379293 / 500000000000000000) (170940425468386311 / 500000000000000000) (((51 / 100) : ℝ) * (kdot ((51 / 100)))) := bmul (bpoint ((51 / 100) : ℝ)) sGlobal33_hz39 (by norm_num) (by norm_num)

theorem sGlobal33_hz45 : B (153920716648042299 / 250000000000000000) (615682866592183233 / 1000000000000000000) (((√((1 : ℝ) - (((51 / 100) : ℝ)^2))) / Real.pi) + (((51 / 100) : ℝ) * (kdot ((51 / 100))))) := badd sGlobal33_hz43 sGlobal33_hz44 (by norm_num) (by norm_num)

theorem sGlobal33_hz46 : B (153920716648042299 / 250000000000000000) (615682866592183233 / 1000000000000000000) (kappa ((51 / 100))) := by rw [kappa_eq]; exact sGlobal33_hz45

theorem sGlobal33_hz47 : B (336104041628554777 / 500000000000000000) (672208083257129293 / 1000000000000000000) (kdot ((103 / 200))) := by
    constructor
    · apply bkdot_lower (q := (141450524301193413 / 250000000000000000)) (a := (102978867754558177 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (565802097204773651 / 1000000000000000000)) (a := (514894338772759881 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal33_hz48 : B (10609 / 40000) (10609 / 40000) (((103 / 200) : ℝ)^2) := bsq (bpoint ((103 / 200) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal33_hz49 : B (29391 / 40000) (29391 / 40000) ((1 : ℝ) - (((103 / 200) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal33_hz48 (by norm_num) (by norm_num)

theorem sGlobal33_hz50 : B (428595088632616041 / 500000000000000000) (857190177265232083 / 1000000000000000000) (√((1 : ℝ) - (((103 / 200) : ℝ)^2))) := bsqrt sGlobal33_hz49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal33_hz51 : B (136426053881579687 / 500000000000000000) (87312674484211 / 320000000000000) ((√((1 : ℝ) - (((103 / 200) : ℝ)^2))) / Real.pi) := bdiv sGlobal33_hz50 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal33_hz52 : B (17309358143870571 / 50000000000000000) (173093581438710793 / 500000000000000000) (((103 / 200) : ℝ) * (kdot ((103 / 200)))) := bmul (bpoint ((103 / 200) : ℝ)) sGlobal33_hz47 (by norm_num) (by norm_num)

theorem sGlobal33_hz53 : B (309519635320285397 / 500000000000000000) (619039270640580961 / 1000000000000000000) (((√((1 : ℝ) - (((103 / 200) : ℝ)^2))) / Real.pi) + (((103 / 200) : ℝ) * (kdot ((103 / 200))))) := badd sGlobal33_hz51 sGlobal33_hz52 (by norm_num) (by norm_num)

theorem sGlobal33_hz54 : B (309519635320285397 / 500000000000000000) (619039270640580961 / 1000000000000000000) (kappa ((103 / 200))) := by rw [kappa_eq]; exact sGlobal33_hz53

theorem sGlobal33_hz55 {c : ℝ} (hc : B (51 / 100) (103 / 200) c) : B (153920716648042299 / 250000000000000000) (619039270640580961 / 1000000000000000000) (kappa c) := bkappa (sGlobal33_hz38 hc) (by norm_num) (by norm_num) sGlobal33_hz46.1 sGlobal33_hz54.2

theorem sGlobal33_hz56 : B 24450 24450 ((2 : ℝ) * (12225 : ℝ)) := bmul (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal33_hz57 {c : ℝ} (hc : B (51 / 100) (103 / 200) c) : B (380960729359419039 / 1000000000000000000) (96079283351957701 / 250000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (sGlobal33_hz55 hc) (by norm_num) (by norm_num)

theorem sGlobal33_hz58 {c : ℝ} (hc : B (51 / 100) (103 / 200) c) : B (186289796656755910071 / 20000000000000000) (46982769559107315789 / 5000000000000000) (((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) := bmul sGlobal33_hz56 (sGlobal33_hz57 hc) (by norm_num) (by norm_num)

theorem sGlobal33_hz59 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (4 : ℝ)) sGlobal33_hz10 (by norm_num) (by norm_num)

theorem sGlobal33_hz60 {c : ℝ} (hc : B (51 / 100) (103 / 200) c) : B (931448917844106748719 / 100000000000000000) (2349138314356183785361 / 250000000000000000) ((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bsub (sGlobal33_hz58 hc) sGlobal33_hz59 (by norm_num) (by norm_num)

theorem sGlobal33_hz61 {c : ℝ} (hc : B (51 / 100) (103 / 200) c) : B (96511601263480586223 / 1000000000000000000) (4846791015049218919 / 50000000000000000) (√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) := bsqrt (sGlobal33_hz60 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal33_hz62 : B (30670756373515103 / 125000000000000000) (122683025494060423 / 500000000000000000) ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal33_hz7 (by norm_num) (by norm_num)

theorem sGlobal33_hz63 {c : ℝ} (hc : B (51 / 100) (103 / 200) c) : B (96266235212492465377 / 1000000000000000000) (24172613562499064389 / 250000000000000000) ((√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) - ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))))) := bsub (sGlobal33_hz61 hc) sGlobal33_hz62 (by norm_num) (by norm_num)

theorem sGlobal33_hz64 {c : ℝ} (hc : B (51 / 100) (103 / 200) c) : B (96266235212492465377 / 1000000000000000000) (24172613562499064389 / 250000000000000000) (s3dm 12225 46 c) := by
    convert (sGlobal33_hz63 hc) using 1 <;>
      norm_num [s3dm, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal33_hz65 : B (6126072185528622723889 / 500000000000000000) (2450428874211449090087 / 200000000000000000) ((s3ap 12225 46)^2) := bsq sGlobal33_hz9 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal33_hz66 : B (6126072185528622723889 / 250000000000000000) (2450428874211449090087 / 100000000000000000) ((2 : ℝ) * ((s3ap 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal33_hz65 (by norm_num) (by norm_num)

theorem sGlobal33_hz67 {c : ℝ} (hc : B (51 / 100) (103 / 200) c) : B (289599626312091383143 / 31250000000000000) (14607881161047842727 / 1562500000000000) ((s3dm 12225 46 c)^2) := bsq (sGlobal33_hz64 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal33_hz68 {c : ℝ} (hc : B (51 / 100) (103 / 200) c) : B (3788811199760967887569 / 250000000000000000) (7618550350063783320147 / 500000000000000000) (((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) := bsub sGlobal33_hz66 (sGlobal33_hz67 hc) (by norm_num) (by norm_num)

theorem sGlobal33_hz69 : B (1524735695971823534271 / 125000000000000000) (609894278388729413841 / 50000000000000000) ((s3am 12225 46)^2) := bsq sGlobal33_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal33_hz70 : B (1524735695971823534271 / 62500000000000000) (609894278388729413841 / 25000000000000000) ((2 : ℝ) * ((s3am 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal33_hz69 (by norm_num) (by norm_num)

theorem sGlobal33_hz71 {c : ℝ} (hc : B (51 / 100) (103 / 200) c) : B (621224257058218617 / 1000000000000000000) (624579588628960229 / 1000000000000000000) ((((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) / ((2 : ℝ) * ((s3am 12225 46)^2))) := bdiv (sGlobal33_hz68 hc) sGlobal33_hz70 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal33_hz72 {c : ℝ} (hc : B (51 / 100) (103 / 200) c) : B (621224257058218617 / 1000000000000000000) (624579588628960229 / 1000000000000000000) (s3c1 12225 46 c) := by
    convert (sGlobal33_hz71 hc) using 1 <;>
      norm_num [s3c1] <;> ring

theorem sGlobal33_hz73 {c : ℝ} (hc : B (51 / 100) (103 / 200) c) : B (335177304839959399 / 500000000000000000) (672208083257129293 / 1000000000000000000) (kdot c) := bkdot (sGlobal33_hz38 hc) sGlobal33_hz39.1 sGlobal33_hz47.2

theorem sGlobal33_hz74 : B (5706915174614857 / 8000000000000000) (44585274801678571 / 62500000000000000) (kdot ((621224257058218617 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (483358692105216287 / 1000000000000000000)) (a := (450246152593012441 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (241679346052608143 / 500000000000000000)) (a := (225123076296506213 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal33_hz75 : B (714729650143315753 / 1000000000000000000) (714729650143315763 / 1000000000000000000) (kdot ((624579588628960229 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (480715852921270533 / 1000000000000000000)) (a := (448101617698374677 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (120178963230317633 / 250000000000000000)) (a := (56012702212296833 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal33_hz76 {c : ℝ} (hc : B (51 / 100) (103 / 200) c) : B (5706915174614857 / 8000000000000000) (714729650143315763 / 1000000000000000000) (kdot (s3c1 12225 46 c)) := bkdot (sGlobal33_hz72 hc) sGlobal33_hz74.1 sGlobal33_hz75.2

theorem sGlobal33_hz77 {c : ℝ} (hc : B (51 / 100) (103 / 200) c) : B (2601 / 10000) (10609 / 40000) (c^2) := bsq (sGlobal33_hz38 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal33_hz78 {c : ℝ} (hc : B (51 / 100) (103 / 200) c) : B (29391 / 40000) (7399 / 10000) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (sGlobal33_hz77 hc) (by norm_num) (by norm_num)

theorem sGlobal33_hz79 {c : ℝ} (hc : B (51 / 100) (103 / 200) c) : B (428595088632616041 / 500000000000000000) (215043600230278883 / 250000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (sGlobal33_hz78 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal33_hz80 : B (39119999999999765769 / 1600000000000000) (3912000000000000489 / 160000000000000) ((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (149450625 : ℝ)) sGlobal33_hz10 (by norm_num) (by norm_num)

theorem sGlobal33_hz81 {c : ℝ} (hc : B (51 / 100) (103 / 200) c) : B (35913836668880941 / 62500000000000000) (289108092655016271 / 500000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (sGlobal33_hz79 hc) (sGlobal33_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal33_hz82 {c : ℝ} (hc : B (51 / 100) (103 / 200) c) : B (14049492904866139997861 / 1000000000000000000) (7068692865415148709537 / 500000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) := bmul sGlobal33_hz80 (sGlobal33_hz81 hc) (by norm_num) (by norm_num)

theorem sGlobal33_hz83 {c : ℝ} (hc : B (51 / 100) (103 / 200) c) : B (702474645243306999893 / 100000000000000000) (7068692865415148709537 / 1000000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) / (2 : ℝ)) := bdiv (sGlobal33_hz82 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal33_hz84 {c : ℝ} (hc : B (51 / 100) (103 / 200) c) : B (702474645243306999893 / 100000000000000000) (7068692865415148709537 / 1000000000000000000) (s3Cpa 12225 c) := by
    convert (sGlobal33_hz83 hc) using 1 <;>
      norm_num [s3Cpa, mA] <;> ring

theorem sGlobal33_hz85 {c : ℝ} (hc : B (51 / 100) (103 / 200) c) : B (136426053881579687 / 500000000000000000) (273802015655410611 / 1000000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (sGlobal33_hz79 hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal33_hz86 {c : ℝ} (hc : B (51 / 100) (103 / 200) c) : B (170940425468379293 / 500000000000000000) (173093581438710793 / 500000000000000000) (c * (kdot c)) := bmul (sGlobal33_hz38 hc) (sGlobal33_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal33_hz87 {c : ℝ} (hc : B (51 / 100) (103 / 200) c) : B (-18333763778565553 / 250000000000000000) (-2723153411253919 / 40000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (sGlobal33_hz85 hc) (sGlobal33_hz86 hc) (by norm_num) (by norm_num)

theorem sGlobal33_hz88 {c : ℝ} (hc : B (51 / 100) (103 / 200) c) : B (-1793042097543711307531 / 1000000000000000000) (-1664527522628948022391 / 1000000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) := bmul sGlobal33_hz80 (sGlobal33_hz87 hc) (by norm_num) (by norm_num)

theorem sGlobal33_hz89 {c : ℝ} (hc : B (51 / 100) (103 / 200) c) : B (-448260524385927826883 / 500000000000000000) (-166452752262894802239 / 200000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) / (2 : ℝ)) := bdiv (sGlobal33_hz88 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal33_hz90 {c : ℝ} (hc : B (51 / 100) (103 / 200) c) : B (-448260524385927826883 / 500000000000000000) (-166452752262894802239 / 200000000000000000) (s3Cpp 12225 c) := by
    convert (sGlobal33_hz89 hc) using 1 <;>
      norm_num [s3Cpp, mA] <;> ring

theorem sGlobal33_hz91 {c : ℝ} (hc : B (51 / 100) (103 / 200) c) : B (7139891562366807707331 / 1000000000000000000) (7183837975348887121763 / 1000000000000000000) ((s3Cpa 12225 c) + (s3r1 12225 46)) := badd (sGlobal33_hz84 hc) sGlobal33_hz33 (by norm_num) (by norm_num)

theorem sGlobal33_hz92 {c : ℝ} (hc : B (51 / 100) (103 / 200) c) : B (64647143300182915367 / 1000000000000000000) (65045049911616064127 / 1000000000000000000) (((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) := bdiv (sGlobal33_hz91 hc) sGlobal33_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal33_hz93 {c : ℝ} (hc : B (51 / 100) (103 / 200) c) : B (64769826325676975779 / 1000000000000000000) (1303354658742202491 / 20000000000000000) ((((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) + (s3e0 12225 46)) := badd (sGlobal33_hz92 hc) sGlobal33_hz16 (by norm_num) (by norm_num)

theorem sGlobal33_hz94 {c : ℝ} (hc : B (51 / 100) (103 / 200) c) : B (64769826325676975779 / 1000000000000000000) (1303354658742202491 / 20000000000000000) (s3Lam 12225 46 c) := by
    convert (sGlobal33_hz93 hc) using 1 <;>
      norm_num [s3Lam] <;> ring

theorem sGlobal33_hz95 {c : ℝ} (hc : B (51 / 100) (103 / 200) c) : B (-409878821074681924083 / 500000000000000000) (-755500354691981736377 / 1000000000000000000) ((s3Cpp 12225 c) + (s3rpp 12225 46)) := badd (sGlobal33_hz90 hc) sGlobal33_hz37 (by norm_num) (by norm_num)

theorem sGlobal33_hz96 {c : ℝ} (hc : B (51 / 100) (103 / 200) c) : B (-585905092775724262883 / 1000000000000000000) (-94437544336497717047 / 250000000000000000) (if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) := bweaken (bfirst (sGlobal33_hz95 hc) (sGlobal33_hz76 hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem sGlobal33_hz97 {c : ℝ} (hc : B (51 / 100) (103 / 200) c) : B (4195130402258358212889 / 1000000000000000000) (2123416708081253890249 / 500000000000000000) ((s3Lam 12225 46 c)^2) := bsq (sGlobal33_hz94 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal33_hz98 {c : ℝ} (hc : B (51 / 100) (103 / 200) c) : B (385919577557535683 / 1000000000000000000) (195049831265960593 / 500000000000000000) ((s3c1 12225 46 c)^2) := bsq (sGlobal33_hz72 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal33_hz99 {c : ℝ} (hc : B (51 / 100) (103 / 200) c) : B (304950168734039407 / 500000000000000000) (614080422442464317 / 1000000000000000000) ((1 : ℝ) - ((s3c1 12225 46 c)^2)) := bsub (bpoint (1 : ℝ)) (sGlobal33_hz98 hc) (by norm_num) (by norm_num)

theorem sGlobal33_hz100 {c : ℝ} (hc : B (51 / 100) (103 / 200) c) : B (780961162586257431 / 1000000000000000000) (156726567300182303 / 200000000000000000) (√((1 : ℝ) - ((s3c1 12225 46 c)^2))) := bsqrt (sGlobal33_hz99 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal33_hz101 {c : ℝ} (hc : B (51 / 100) (103 / 200) c) : B (2453461851119930437 / 1000000000000000000) (307731895282874399 / 125000000000000000) (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))) := bmul pi_mem (sGlobal33_hz100 hc) (by norm_num) (by norm_num)

theorem sGlobal33_hz102 {c : ℝ} (hc : B (51 / 100) (103 / 200) c) : B (1704052483088442797237 / 1000000000000000000) (865477776681947993443 / 500000000000000000) (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2))))) := bdiv (sGlobal33_hz97 hc) (sGlobal33_hz101 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal33_hz103 {c : ℝ} (hc : B (51 / 100) (103 / 200) c) : B (559073695156359267177 / 500000000000000000) (676602688008952559349 / 500000000000000000) ((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) := badd (sGlobal33_hz96 hc) (sGlobal33_hz102 hc) (by norm_num) (by norm_num)

theorem sGlobal33_hz104 : B (3762781186094069 / 250000000000000000) (376278118609407 / 25000000000000000) ((s3e0 12225 46)^2) := bsq sGlobal33_hz16 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal33_hz105 {c : ℝ} (hc : B (51 / 100) (103 / 200) c) : B (111816244143746291063 / 100000000000000000) (676610213571324747489 / 500000000000000000) (((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) := badd (sGlobal33_hz103 hc) sGlobal33_hz104 (by norm_num) (by norm_num)

theorem sGlobal33_hz106 {c : ℝ} (hc : B (51 / 100) (103 / 200) c) : B (1156659514888710180761 / 1000000000000000000) (695858750298386882497 / 500000000000000000) ((((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) + (s3rs 12225 46 maskSlack)) := badd (sGlobal33_hz105 hc) sGlobal33_hz29 (by norm_num) (by norm_num)

theorem sGlobal33_hz107 {c : ℝ} (hc : B (51 / 100) (103 / 200) c) : B (1156659514888710180761 / 1000000000000000000) (695858750298386882497 / 500000000000000000) (s3U 12225 46 maskSlack c) := by
    convert (sGlobal33_hz106 hc) using 1 <;>
      norm_num [s3U] <;> ring

theorem sGlobal33_hz108 {c : ℝ} (hc : B (51 / 100) (103 / 200) c) : B (-121660556924293491073 / 125000000000000000) (-181805433587393163359 / 200000000000000000) ((s3Cpp 12225 c) - (s3rpp 12225 46)) := bsub (sGlobal33_hz90 hc) sGlobal33_hz37 (by norm_num) (by norm_num)

theorem sGlobal33_hz109 {c : ℝ} (hc : B (51 / 100) (103 / 200) c) : B (-121660556924293491073 / 125000000000000000) (-181805433587393163359 / 200000000000000000) (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ)) := bweaken (bmin (sGlobal33_hz108 hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem sGlobal33_hz110 {c : ℝ} (hc : B (51 / 100) (103 / 200) c) : B (-173908814573482477829 / 250000000000000000) (-648467617354579776597 / 1000000000000000000) ((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) := bmul (sGlobal33_hz76 hc) (sGlobal33_hz109 hc) (by norm_num) (by norm_num)

theorem sGlobal33_hz111 {c : ℝ} (hc : B (51 / 100) (103 / 200) c) : B (-173912577354668571899 / 250000000000000000) (-648482668479324152873 / 1000000000000000000) (((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) := bsub (sGlobal33_hz110 hc) sGlobal33_hz104 (by norm_num) (by norm_num)

theorem sGlobal33_hz112 {c : ℝ} (hc : B (51 / 100) (103 / 200) c) : B (-183536845718199639403 / 250000000000000000) (-171744935482642855751 / 250000000000000000) ((((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) - (s3rs 12225 46 maskSlack)) := bsub (sGlobal33_hz111 hc) sGlobal33_hz29 (by norm_num) (by norm_num)

theorem sGlobal33_hz113 {c : ℝ} (hc : B (51 / 100) (103 / 200) c) : B (-183536845718199639403 / 250000000000000000) (-171744935482642855751 / 250000000000000000) (s3L 12225 46 maskSlack c) := by
    convert (sGlobal33_hz112 hc) using 1 <;>
      norm_num [s3L] <;> ring

theorem sGlobal33_hz114 {c : ℝ} (hc : B (51 / 100) (103 / 200) c) : B 0 (695858750298386882497 / 500000000000000000) |(s3U 12225 46 maskSlack c)| := bweaken (babs (sGlobal33_hz107 hc)) (by norm_num) (by norm_num)

theorem sGlobal33_hz115 {c : ℝ} (hc : B (51 / 100) (103 / 200) c) : B 0 (183536845718199639403 / 250000000000000000) |(s3L 12225 46 maskSlack c)| := bweaken (babs (sGlobal33_hz113 hc)) (by norm_num) (by norm_num)

theorem sGlobal33_hz116 {c : ℝ} (hc : B (51 / 100) (103 / 200) c) : B 0 (695858750298386882497 / 500000000000000000) (max |(s3U 12225 46 maskSlack c)| |(s3L 12225 46 maskSlack c)|) := bweaken (bmax (sGlobal33_hz114 hc) (sGlobal33_hz115 hc)) (by norm_num) (by norm_num)

theorem sGlobal33_hz117 {c : ℝ} (hc : B (51 / 100) (103 / 200) c) : B 0 (695858750298386882497 / 500000000000000000) (s3nks 12225 46 maskSlack c) := by
    convert (sGlobal33_hz116 hc) using 1 <;>
      norm_num [s3nks] <;> ring

theorem sGlobal33 {c : ℝ} (hc : B (51 / 100) (103 / 200) c) :
    0 < s3am 12225 46 ∧ 0 ≤ s3dm 12225 46 c ∧
    s3dm 12225 46 c ^ 2 ≤ 2 * s3ap 12225 46 ^ 2 ∧ s3c1 12225 46 c < 1 ∧
    0 ≤ s3Cpa 12225 c - s3r1 12225 46 ∧
    s3e0 12225 46 ≤ (s3Cpa 12225 c - s3r1 12225 46) / s3ap 12225 46 ∧
    s3nks 12225 46 maskSlack c ≤ 12225 * (56921 / 500000) := by

  refine ⟨lt_of_lt_of_le (by norm_num) sGlobal33_hz14.1,
    le_trans (by norm_num) (sGlobal33_hz64 hc).1, ?_,
    lt_of_le_of_lt (sGlobal33_hz72 hc).2 (by norm_num), ?_, ?_,
    le_trans (sGlobal33_hz117 hc).2 (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (sGlobal33_hz64 hc).1) (sGlobal33_hz64 hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) sGlobal33_hz9.1 2
    nlinarith only [h1, h2]
  · linarith only [(sGlobal33_hz84 hc).1, sGlobal33_hz33.2]
  · have hap : 0 < s3ap 12225 46 := lt_of_lt_of_le (by norm_num) sGlobal33_hz9.1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul sGlobal33_hz16.2 sGlobal33_hz9.2 (le_trans (by norm_num) sGlobal33_hz9.1) (by norm_num)
    linarith only [h, (sGlobal33_hz84 hc).1, sGlobal33_hz33.2]

end BstLean.Part255
