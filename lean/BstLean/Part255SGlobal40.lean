import BstLean.Part255SGlobal36
import BstLean.Part255Numeric10
namespace BstLean.Part255
open Real BstLean.Part130 BstLean.Part182 BstLean.Part197 BstLean.Part246
theorem sGlobal40_hz0 : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal40_hz1 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) ((√(23 : ℝ)) / (12225 : ℝ)) := bdiv sGlobal40_hz0 (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal40_hz2 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) maskSlack := by
    convert sGlobal40_hz1 using 1 <;>
      norm_num [maskSlack] <;> ring

theorem sGlobal40_hz3 : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal40_hz4 : B (6395294793910793 / 500000000000000000) (12790589587821587 / 1000000000000000000) (√((2 / 12225) : ℝ)) := bsqrt (bpoint ((2 / 12225) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal40_hz5 : B (7230130686979 / 62500000000000000) (23136418198333 / 200000000000000000) (√((2 / 149450625) : ℝ)) := bsqrt (bpoint ((2 / 149450625) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal40_hz6 : B (2211334438749598093 / 20000000000000000) (110566721937479904651 / 1000000000000000000) (√(12225 : ℝ)) := bsqrt (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal40_hz7 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))) := bmul sGlobal40_hz3 sGlobal40_hz4 (by norm_num) (by norm_num)

theorem sGlobal40_hz8 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) ((√(12225 : ℝ)) + ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := badd sGlobal40_hz6 sGlobal40_hz7 (by norm_num) (by norm_num)

theorem sGlobal40_hz9 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) (s3ap 12225 46) := by
    convert sGlobal40_hz8 using 1 <;>
      norm_num [s3ap, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal40_hz10 : B (163599182004089 / 1000000000000000000) (16359918200409 / 100000000000000000) ((2 : ℝ) / (12225 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal40_hz11 : B (1222499983640081799591 / 100000000000000000) (12224999836400817995911 / 1000000000000000000) ((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ))) := bsub (bpoint (12225 : ℝ)) sGlobal40_hz10 (by norm_num) (by norm_num)

theorem sGlobal40_hz12 : B (110566721197658827907 / 1000000000000000000) (27641680299414706977 / 250000000000000000) (√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) := bsqrt sGlobal40_hz11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal40_hz13 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) ((√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) - ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bsub sGlobal40_hz12 sGlobal40_hz7 (by norm_num) (by norm_num)

theorem sGlobal40_hz14 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) (s3am 12225 46) := by
    convert sGlobal40_hz13 using 1 <;>
      norm_num [s3am, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal40_hz15 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√((2 / 12225) : ℝ)) * (√(92 : ℝ))) := bmul sGlobal40_hz4 sGlobal40_hz3 (by norm_num) (by norm_num)

theorem sGlobal40_hz16 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) (s3e0 12225 46) := by
    convert sGlobal40_hz15 using 1 <;>
      norm_num [s3e0, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal40_hz17 : B (250196148528560847 / 500000000000000000) (100078459411424339 / 200000000000000000) (((1 / 2) : ℝ) + maskSlack) := badd (bpoint ((1 / 2) : ℝ)) sGlobal40_hz2 (by norm_num) (by norm_num)

theorem sGlobal40_hz18 : B (59827153232297998295487 / 800000000000000) (23930861292919199366019 / 320000000000000) ((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack)) := bmul (bpoint (149450625 : ℝ)) sGlobal40_hz17 (by norm_num) (by norm_num)

theorem sGlobal40_hz19 : B (1729554180017180009583 / 200000000000000000) (8647770900085900056557 / 1000000000000000000) (√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) := bsqrt sGlobal40_hz18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal40_hz20 : B (4328681281566262743499 / 500000000000000000) (8657362563132525495641 / 1000000000000000000) ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))) := badd sGlobal40_hz19 sGlobal40_hz3 (by norm_num) (by norm_num)

theorem sGlobal40_hz21 : B (110732771457999278473 / 1000000000000000000) (55366385728999643621 / 500000000000000000) ((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ)))) := bmul sGlobal40_hz4 sGlobal40_hz20 (by norm_num) (by norm_num)

theorem sGlobal40_hz22 : B (209099159 / 15625000000000000) (13382346177 / 1000000000000000000) ((2 : ℝ) / (149450625 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (149450625 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal40_hz23 : B (2452349334953899930479 / 200000000000000000) (12261746674769501594427 / 1000000000000000000) (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2) := bsq sGlobal40_hz21 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal40_hz24 : B (82045469362091 / 500000000000000000) (32818187747289 / 200000000000000000) (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2)) := bmul sGlobal40_hz22 sGlobal40_hz23 (by norm_num) (by norm_num)

theorem sGlobal40_hz25 : B (82045469362091 / 250000000000000000) (32818187747289 / 100000000000000000) ((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) := bmul (bpoint (2 : ℝ)) sGlobal40_hz24 (by norm_num) (by norm_num)

theorem sGlobal40_hz26 : B (117258080744995992792057 / 1000000000000000000) (58629040372497996396029 / 500000000000000000) (√(13749457500 : ℝ)) := bsqrt (bpoint (13749457500 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal40_hz27 : B (117304080744995992792057 / 1000000000000000000) (58652040372497996396029 / 500000000000000000) ((√(13749457500 : ℝ)) + (46 : ℝ)) := badd sGlobal40_hz26 (bpoint (46 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal40_hz28 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal40_hz25 sGlobal40_hz27 (by norm_num) (by norm_num)

theorem sGlobal40_hz29 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (s3rs 12225 46 maskSlack) := by
    convert sGlobal40_hz28 using 1 <;>
      norm_num [s3rs, s3pp, s3K, mA, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal40_hz30 : B (490797546012267 / 1000000000000000000) (49079754601227 / 100000000000000000) ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (3 : ℝ)) sGlobal40_hz10 (by norm_num) (by norm_num)

theorem sGlobal40_hz31 : B (490797546012267 / 500000000000000000) (49079754601227 / 50000000000000000) ((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal40_hz30 (by norm_num) (by norm_num)

theorem sGlobal40_hz32 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal40_hz31 sGlobal40_hz27 (by norm_num) (by norm_num)

theorem sGlobal40_hz33 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (s3r1 12225 46) := by
    convert sGlobal40_hz32 using 1 <;>
      norm_num [s3r1, mA] <;> ring

theorem sGlobal40_hz34 : B (163599182004089 / 500000000000000000) (16359918200409 / 50000000000000000) ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (2 : ℝ)) sGlobal40_hz10 (by norm_num) (by norm_num)

theorem sGlobal40_hz35 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal40_hz34 (by norm_num) (by norm_num)

theorem sGlobal40_hz36 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal40_hz35 sGlobal40_hz27 (by norm_num) (by norm_num)

theorem sGlobal40_hz37 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (s3rpp 12225 46) := by
    convert sGlobal40_hz36 using 1 <;>
      norm_num [s3rpp, mA] <;> ring

theorem sGlobal40_hz38 {c : ℝ} (hc : B (109 / 200) (11 / 20) c) : B (109 / 200) (11 / 20) c := hc

theorem sGlobal40_hz39 : B (683470353509254499 / 1000000000000000000) (136694070701851411 / 200000000000000000) (kdot ((109 / 200))) := by
    constructor
    · apply bkdot_lower (q := (54267705117963359 / 100000000000000000)) (a := (497203606029350171 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (542677051179633589 / 1000000000000000000)) (a := (497203606029346157 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal40_hz40 : B (11881 / 40000) (11881 / 40000) (((109 / 200) : ℝ)^2) := bsq (bpoint ((109 / 200) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal40_hz41 : B (28119 / 40000) (28119 / 40000) ((1 : ℝ) - (((109 / 200) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal40_hz40 (by norm_num) (by norm_num)

theorem sGlobal40_hz42 : B (167687208814506779 / 200000000000000000) (104804505509066737 / 125000000000000000) (√((1 : ℝ) - (((109 / 200) : ℝ)^2))) := bsqrt sGlobal40_hz41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal40_hz43 : B (266882481761115963 / 1000000000000000000) (66720620440278991 / 250000000000000000) ((√((1 : ℝ) - (((109 / 200) : ℝ)^2))) / Real.pi) := bdiv sGlobal40_hz42 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal40_hz44 : B (372491342662543701 / 1000000000000000000) (74498268532509019 / 200000000000000000) (((109 / 200) : ℝ) * (kdot ((109 / 200)))) := bmul (bpoint ((109 / 200) : ℝ)) sGlobal40_hz39 (by norm_num) (by norm_num)

theorem sGlobal40_hz45 : B (39960864026478729 / 62500000000000000) (639373824423661059 / 1000000000000000000) (((√((1 : ℝ) - (((109 / 200) : ℝ)^2))) / Real.pi) + (((109 / 200) : ℝ) * (kdot ((109 / 200))))) := badd sGlobal40_hz43 sGlobal40_hz44 (by norm_num) (by norm_num)

theorem sGlobal40_hz46 : B (39960864026478729 / 62500000000000000) (639373824423661059 / 1000000000000000000) (kappa ((109 / 200))) := by rw [kappa_eq]; exact sGlobal40_hz45

theorem sGlobal40_hz47 : B (27414891770940381 / 40000000000000000) (685372294273511327 / 1000000000000000000) (kdot ((11 / 20))) := by
    constructor
    · apply bkdot_lower (q := (538815906080324703 / 1000000000000000000)) (a := (247108022231538449 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (269407953040162351 / 500000000000000000)) (a := (494216044463074069 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal40_hz48 : B (121 / 400) (121 / 400) (((11 / 20) : ℝ)^2) := bsq (bpoint ((11 / 20) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal40_hz49 : B (279 / 400) (279 / 400) ((1 : ℝ) - (((11 / 20) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal40_hz48 (by norm_num) (by norm_num)

theorem sGlobal40_hz50 : B (104395581803062911 / 125000000000000000) (835164654424503289 / 1000000000000000000) (√((1 : ℝ) - (((11 / 20) : ℝ)^2))) := bsqrt sGlobal40_hz49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal40_hz51 : B (265841166094588509 / 1000000000000000000) (265841166094588511 / 1000000000000000000) ((√((1 : ℝ) - (((11 / 20) : ℝ)^2))) / Real.pi) := bdiv sGlobal40_hz50 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal40_hz52 : B (188477380925215119 / 500000000000000000) (37695476185043123 / 100000000000000000) (((11 / 20) : ℝ) * (kdot ((11 / 20)))) := bmul (bpoint ((11 / 20) : ℝ)) sGlobal40_hz47 (by norm_num) (by norm_num)

theorem sGlobal40_hz53 : B (642795927945018747 / 1000000000000000000) (642795927945019741 / 1000000000000000000) (((√((1 : ℝ) - (((11 / 20) : ℝ)^2))) / Real.pi) + (((11 / 20) : ℝ) * (kdot ((11 / 20))))) := badd sGlobal40_hz51 sGlobal40_hz52 (by norm_num) (by norm_num)

theorem sGlobal40_hz54 : B (642795927945018747 / 1000000000000000000) (642795927945019741 / 1000000000000000000) (kappa ((11 / 20))) := by rw [kappa_eq]; exact sGlobal40_hz53

theorem sGlobal40_hz55 {c : ℝ} (hc : B (109 / 200) (11 / 20) c) : B (39960864026478729 / 62500000000000000) (642795927945019741 / 1000000000000000000) (kappa c) := bkappa (sGlobal40_hz38 hc) (by norm_num) (by norm_num) sGlobal40_hz46.1 sGlobal40_hz54.2

theorem sGlobal40_hz56 : B 24450 24450 ((2 : ℝ) * (12225 : ℝ)) := bmul (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal40_hz57 {c : ℝ} (hc : B (109 / 200) (11 / 20) c) : B (357204072054980259 / 1000000000000000000) (22539135973521271 / 62500000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (sGlobal40_hz55 hc) (by norm_num) (by norm_num)

theorem sGlobal40_hz58 {c : ℝ} (hc : B (109 / 200) (11 / 20) c) : B (174672791234885346651 / 20000000000000000) (11021637491051901519 / 1250000000000000) (((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) := bmul sGlobal40_hz56 (sGlobal40_hz57 hc) (by norm_num) (by norm_num)

theorem sGlobal40_hz59 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (4 : ℝ)) sGlobal40_hz10 (by norm_num) (by norm_num)

theorem sGlobal40_hz60 {c : ℝ} (hc : B (109 / 200) (11 / 20) c) : B (873363890734753931619 / 100000000000000000) (2204327334611198299711 / 250000000000000000) ((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bsub (sGlobal40_hz58 hc) sGlobal40_hz59 (by norm_num) (by norm_num)

theorem sGlobal40_hz61 {c : ℝ} (hc : B (109 / 200) (11 / 20) c) : B (93453940031159410267 / 1000000000000000000) (23475132239303777241 / 250000000000000000) (√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) := bsqrt (sGlobal40_hz60 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal40_hz62 : B (30670756373515103 / 125000000000000000) (122683025494060423 / 500000000000000000) ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal40_hz7 (by norm_num) (by norm_num)

theorem sGlobal40_hz63 {c : ℝ} (hc : B (109 / 200) (11 / 20) c) : B (93208573980171289421 / 1000000000000000000) (4682758145311349407 / 50000000000000000) ((√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) - ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))))) := bsub (sGlobal40_hz61 hc) sGlobal40_hz62 (by norm_num) (by norm_num)

theorem sGlobal40_hz64 {c : ℝ} (hc : B (109 / 200) (11 / 20) c) : B (93208573980171289421 / 1000000000000000000) (4682758145311349407 / 50000000000000000) (s3dm 12225 46 c) := by
    convert (sGlobal40_hz63 hc) using 1 <;>
      norm_num [s3dm, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal40_hz65 : B (6126072185528622723889 / 500000000000000000) (2450428874211449090087 / 200000000000000000) ((s3ap 12225 46)^2) := bsq sGlobal40_hz9 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal40_hz66 : B (6126072185528622723889 / 250000000000000000) (2450428874211449090087 / 100000000000000000) ((2 : ℝ) * ((s3ap 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal40_hz65 (by norm_num) (by norm_num)

theorem sGlobal40_hz67 {c : ℝ} (hc : B (109 / 200) (11 / 20) c) : B (4343919131708532162869 / 500000000000000000) (1754257907798383117459 / 200000000000000000) ((s3dm 12225 46 c)^2) := bsq (sGlobal40_hz64 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal40_hz68 {c : ℝ} (hc : B (109 / 200) (11 / 20) c) : B (15732999203122575308261 / 1000000000000000000) (3954112619674356643783 / 250000000000000000) (((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) := bsub sGlobal40_hz66 (sGlobal40_hz67 hc) (by norm_num) (by norm_num)

theorem sGlobal40_hz69 : B (1524735695971823534271 / 125000000000000000) (609894278388729413841 / 50000000000000000) ((s3am 12225 46)^2) := bsq sGlobal40_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal40_hz70 : B (1524735695971823534271 / 62500000000000000) (609894278388729413841 / 25000000000000000) ((2 : ℝ) * ((s3am 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal40_hz69 (by norm_num) (by norm_num)

theorem sGlobal40_hz71 {c : ℝ} (hc : B (109 / 200) (11 / 20) c) : B (32245341038219261 / 50000000000000000) (162081886967388337 / 250000000000000000) ((((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) / ((2 : ℝ) * ((s3am 12225 46)^2))) := bdiv (sGlobal40_hz68 hc) sGlobal40_hz70 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal40_hz72 {c : ℝ} (hc : B (109 / 200) (11 / 20) c) : B (32245341038219261 / 50000000000000000) (162081886967388337 / 250000000000000000) (s3c1 12225 46 c) := by
    convert (sGlobal40_hz71 hc) using 1 <;>
      norm_num [s3c1] <;> ring

theorem sGlobal40_hz73 {c : ℝ} (hc : B (109 / 200) (11 / 20) c) : B (683470353509254499 / 1000000000000000000) (685372294273511327 / 1000000000000000000) (kdot c) := bkdot (sGlobal40_hz38 hc) sGlobal40_hz39.1 sGlobal40_hz47.2

theorem sGlobal40_hz74 : B (22596994717069657 / 31250000000000000) (723103830946229027 / 1000000000000000000) (kdot ((32245341038219261 / 50000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (232311398237465557 / 500000000000000000)) (a := (217473742626621087 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (464622796474931113 / 1000000000000000000)) (a := (43494748525324217 / 100000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal40_hz75 : B (724531247304301227 / 1000000000000000000) (72453124730430123 / 100000000000000000) (kdot ((162081886967388337 / 250000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (461899419451682531 / 1000000000000000000)) (a := (27044081555073463 / 62500000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (46189941945168253 / 100000000000000000)) (a := (86541060976235081 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal40_hz76 {c : ℝ} (hc : B (109 / 200) (11 / 20) c) : B (22596994717069657 / 31250000000000000) (72453124730430123 / 100000000000000000) (kdot (s3c1 12225 46 c)) := bkdot (sGlobal40_hz72 hc) sGlobal40_hz74.1 sGlobal40_hz75.2

theorem sGlobal40_hz77 {c : ℝ} (hc : B (109 / 200) (11 / 20) c) : B (11881 / 40000) (121 / 400) (c^2) := bsq (sGlobal40_hz38 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal40_hz78 {c : ℝ} (hc : B (109 / 200) (11 / 20) c) : B (279 / 400) (28119 / 40000) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (sGlobal40_hz77 hc) (by norm_num) (by norm_num)

theorem sGlobal40_hz79 {c : ℝ} (hc : B (109 / 200) (11 / 20) c) : B (104395581803062911 / 125000000000000000) (104804505509066737 / 125000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (sGlobal40_hz78 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal40_hz80 : B (39119999999999765769 / 1600000000000000) (3912000000000000489 / 160000000000000) ((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (149450625 : ℝ)) sGlobal40_hz10 (by norm_num) (by norm_num)

theorem sGlobal40_hz81 {c : ℝ} (hc : B (109 / 200) (11 / 20) c) : B (570810281597949631 / 1000000000000000000) (287320417563799707 / 500000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (sGlobal40_hz79 hc) (sGlobal40_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal40_hz82 {c : ℝ} (hc : B (109 / 200) (11 / 20) c) : B (2791262277013956982907 / 200000000000000000) (14049968418869807428547 / 1000000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) := bmul sGlobal40_hz80 (sGlobal40_hz81 hc) (by norm_num) (by norm_num)

theorem sGlobal40_hz83 {c : ℝ} (hc : B (109 / 200) (11 / 20) c) : B (6978155692534892457267 / 1000000000000000000) (3512492104717451857137 / 500000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) / (2 : ℝ)) := bdiv (sGlobal40_hz82 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal40_hz84 {c : ℝ} (hc : B (109 / 200) (11 / 20) c) : B (6978155692534892457267 / 1000000000000000000) (3512492104717451857137 / 500000000000000000) (s3Cpa 12225 c) := by
    convert (sGlobal40_hz83 hc) using 1 <;>
      norm_num [s3Cpa, mA] <;> ring

theorem sGlobal40_hz85 {c : ℝ} (hc : B (109 / 200) (11 / 20) c) : B (265841166094588509 / 1000000000000000000) (66720620440278991 / 250000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (sGlobal40_hz79 hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal40_hz86 {c : ℝ} (hc : B (109 / 200) (11 / 20) c) : B (372491342662543701 / 1000000000000000000) (37695476185043123 / 100000000000000000) (c * (kdot c)) := bmul (sGlobal40_hz38 hc) (sGlobal40_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal40_hz87 {c : ℝ} (hc : B (109 / 200) (11 / 20) c) : B (-111113595755842721 / 1000000000000000000) (-105608860901427737 / 1000000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (sGlobal40_hz85 hc) (sGlobal40_hz86 hc) (by norm_num) (by norm_num)

theorem sGlobal40_hz88 {c : ℝ} (hc : B (109 / 200) (11 / 20) c) : B (-2716727416230354868041 / 1000000000000000000) (-1291068324519946354553 / 500000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) := bmul sGlobal40_hz80 (sGlobal40_hz87 hc) (by norm_num) (by norm_num)

theorem sGlobal40_hz89 {c : ℝ} (hc : B (109 / 200) (11 / 20) c) : B (-1358363708115177434021 / 1000000000000000000) (-1291068324519946354553 / 1000000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) / (2 : ℝ)) := bdiv (sGlobal40_hz88 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal40_hz90 {c : ℝ} (hc : B (109 / 200) (11 / 20) c) : B (-1358363708115177434021 / 1000000000000000000) (-1291068324519946354553 / 1000000000000000000) (s3Cpp 12225 c) := by
    convert (sGlobal40_hz89 hc) using 1 <;>
      norm_num [s3Cpp, mA] <;> ring

theorem sGlobal40_hz91 {c : ℝ} (hc : B (109 / 200) (11 / 20) c) : B (1773325200617157541417 / 250000000000000000) (14280258638737284253 / 2000000000000000) ((s3Cpa 12225 c) + (s3r1 12225 46)) := badd (sGlobal40_hz84 hc) sGlobal40_hz33 (by norm_num) (by norm_num)

theorem sGlobal40_hz92 {c : ℝ} (hc : B (109 / 200) (11 / 20) c) : B (32112646910878509293 / 500000000000000000) (64649296037494673151 / 1000000000000000000) (((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) := bdiv (sGlobal40_hz91 hc) sGlobal40_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal40_hz93 {c : ℝ} (hc : B (109 / 200) (11 / 20) c) : B (32173988423625539499 / 500000000000000000) (32385989531494366787 / 500000000000000000) ((((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) + (s3e0 12225 46)) := badd (sGlobal40_hz92 hc) sGlobal40_hz16 (by norm_num) (by norm_num)

theorem sGlobal40_hz94 {c : ℝ} (hc : B (109 / 200) (11 / 20) c) : B (32173988423625539499 / 500000000000000000) (32385989531494366787 / 500000000000000000) (s3Lam 12225 46 c) := by
    convert (sGlobal40_hz93 hc) using 1 <;>
      norm_num [s3Lam] <;> ring

theorem sGlobal40_hz95 {c : ℝ} (hc : B (109 / 200) (11 / 20) c) : B (-1281600301492685628421 / 1000000000000000000) (-242860983579490815947 / 200000000000000000) ((s3Cpp 12225 c) + (s3rpp 12225 46)) := badd (sGlobal40_hz90 hc) sGlobal40_hz37 (by norm_num) (by norm_num)

theorem sGlobal40_hz96 {c : ℝ} (hc : B (109 / 200) (11 / 20) c) : B (-232139866246516006963 / 250000000000000000) (-607152458948727039867 / 1000000000000000000) (if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) := bweaken (bfirst (sGlobal40_hz95 hc) (sGlobal40_hz76 hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem sGlobal40_hz97 {c : ℝ} (hc : B (109 / 200) (11 / 20) c) : B (4140662124334360912509 / 1000000000000000000) (524426158967031357569 / 125000000000000000) ((s3Lam 12225 46 c)^2) := bsq (sGlobal40_hz94 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal40_hz98 {c : ℝ} (hc : B (109 / 200) (11 / 20) c) : B (415904807468426883 / 1000000000000000000) (105082152331636997 / 250000000000000000) ((s3c1 12225 46 c)^2) := bsq (sGlobal40_hz72 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal40_hz99 {c : ℝ} (hc : B (109 / 200) (11 / 20) c) : B (144917847668363003 / 250000000000000000) (584095192531573117 / 1000000000000000000) ((1 : ℝ) - ((s3c1 12225 46 c)^2)) := bsub (bpoint (1 : ℝ)) (sGlobal40_hz98 hc) (by norm_num) (by norm_num)

theorem sGlobal40_hz100 {c : ℝ} (hc : B (109 / 200) (11 / 20) c) : B (761361537427162137 / 1000000000000000000) (764261207004236947 / 1000000000000000000) (√((1 : ℝ) - ((s3c1 12225 46 c)^2))) := bsqrt (sGlobal40_hz99 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal40_hz101 {c : ℝ} (hc : B (109 / 200) (11 / 20) c) : B (2391887812707002979 / 1000000000000000000) (96039895733927161 / 40000000000000000) (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))) := bmul pi_mem (sGlobal40_hz100 hc) (by norm_num) (by norm_num)

theorem sGlobal40_hz102 {c : ℝ} (hc : B (109 / 200) (11 / 20) c) : B (1724559191861607146081 / 1000000000000000000) (438503976801082130869 / 250000000000000000) (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2))))) := bdiv (sGlobal40_hz97 hc) (sGlobal40_hz101 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal40_hz103 {c : ℝ} (hc : B (109 / 200) (11 / 20) c) : B (795999726875543118229 / 1000000000000000000) (1146863448255601483609 / 1000000000000000000) ((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) := badd (sGlobal40_hz96 hc) (sGlobal40_hz102 hc) (by norm_num) (by norm_num)

theorem sGlobal40_hz104 : B (3762781186094069 / 250000000000000000) (376278118609407 / 25000000000000000) ((s3e0 12225 46)^2) := bsq sGlobal40_hz16 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal40_hz105 {c : ℝ} (hc : B (109 / 200) (11 / 20) c) : B (159202955600057498901 / 200000000000000000) (1146878499380345859889 / 1000000000000000000) (((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) := badd (sGlobal40_hz103 hc) sGlobal40_hz104 (by norm_num) (by norm_num)

theorem sGlobal40_hz106 {c : ℝ} (hc : B (109 / 200) (11 / 20) c) : B (208627962862883691159 / 250000000000000000) (237075114566894025981 / 200000000000000000) ((((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) + (s3rs 12225 46 maskSlack)) := badd (sGlobal40_hz105 hc) sGlobal40_hz29 (by norm_num) (by norm_num)

theorem sGlobal40_hz107 {c : ℝ} (hc : B (109 / 200) (11 / 20) c) : B (208627962862883691159 / 250000000000000000) (237075114566894025981 / 200000000000000000) (s3U 12225 46 maskSlack c) := by
    convert (sGlobal40_hz106 hc) using 1 <;>
      norm_num [s3U] <;> ring

theorem sGlobal40_hz108 {c : ℝ} (hc : B (109 / 200) (11 / 20) c) : B (-1435127114737669708839 / 1000000000000000000) (-1367831731142438160153 / 1000000000000000000) ((s3Cpp 12225 c) - (s3rpp 12225 46)) := bsub (sGlobal40_hz90 hc) sGlobal40_hz37 (by norm_num) (by norm_num)

theorem sGlobal40_hz109 {c : ℝ} (hc : B (109 / 200) (11 / 20) c) : B (-1435127114737669708839 / 1000000000000000000) (-1367831731142438160153 / 1000000000000000000) (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ)) := bweaken (bmin (sGlobal40_hz108 hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem sGlobal40_hz110 {c : ℝ} (hc : B (109 / 200) (11 / 20) c) : B (-1039794438481106858241 / 1000000000000000000) (-989084364878909393099 / 1000000000000000000) ((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) := bmul (sGlobal40_hz76 hc) (sGlobal40_hz109 hc) (by norm_num) (by norm_num)

theorem sGlobal40_hz111 {c : ℝ} (hc : B (109 / 200) (11 / 20) c) : B (-1039809489605851234521 / 1000000000000000000) (-1582559065605846031 / 1600000000000000) (((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) := bsub (sGlobal40_hz110 hc) sGlobal40_hz104 (by norm_num) (by norm_num)

theorem sGlobal40_hz112 {c : ℝ} (hc : B (109 / 200) (11 / 20) c) : B (-1078306563059975504537 / 1000000000000000000) (-513798244727450519753 / 500000000000000000) ((((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) - (s3rs 12225 46 maskSlack)) := bsub (sGlobal40_hz111 hc) sGlobal40_hz29 (by norm_num) (by norm_num)

theorem sGlobal40_hz113 {c : ℝ} (hc : B (109 / 200) (11 / 20) c) : B (-1078306563059975504537 / 1000000000000000000) (-513798244727450519753 / 500000000000000000) (s3L 12225 46 maskSlack c) := by
    convert (sGlobal40_hz112 hc) using 1 <;>
      norm_num [s3L] <;> ring

theorem sGlobal40_hz114 {c : ℝ} (hc : B (109 / 200) (11 / 20) c) : B 0 (237075114566894025981 / 200000000000000000) |(s3U 12225 46 maskSlack c)| := bweaken (babs (sGlobal40_hz107 hc)) (by norm_num) (by norm_num)

theorem sGlobal40_hz115 {c : ℝ} (hc : B (109 / 200) (11 / 20) c) : B 0 (1078306563059975504537 / 1000000000000000000) |(s3L 12225 46 maskSlack c)| := bweaken (babs (sGlobal40_hz113 hc)) (by norm_num) (by norm_num)

theorem sGlobal40_hz116 {c : ℝ} (hc : B (109 / 200) (11 / 20) c) : B 0 (237075114566894025981 / 200000000000000000) (max |(s3U 12225 46 maskSlack c)| |(s3L 12225 46 maskSlack c)|) := bweaken (bmax (sGlobal40_hz114 hc) (sGlobal40_hz115 hc)) (by norm_num) (by norm_num)

theorem sGlobal40_hz117 {c : ℝ} (hc : B (109 / 200) (11 / 20) c) : B 0 (237075114566894025981 / 200000000000000000) (s3nks 12225 46 maskSlack c) := by
    convert (sGlobal40_hz116 hc) using 1 <;>
      norm_num [s3nks] <;> ring

theorem sGlobal40 {c : ℝ} (hc : B (109 / 200) (11 / 20) c) :
    0 < s3am 12225 46 ∧ 0 ≤ s3dm 12225 46 c ∧
    s3dm 12225 46 c ^ 2 ≤ 2 * s3ap 12225 46 ^ 2 ∧ s3c1 12225 46 c < 1 ∧
    0 ≤ s3Cpa 12225 c - s3r1 12225 46 ∧
    s3e0 12225 46 ≤ (s3Cpa 12225 c - s3r1 12225 46) / s3ap 12225 46 ∧
    s3nks 12225 46 maskSlack c ≤ 12225 * (24241 / 250000) := by

  refine ⟨lt_of_lt_of_le (by norm_num) sGlobal40_hz14.1,
    le_trans (by norm_num) (sGlobal40_hz64 hc).1, ?_,
    lt_of_le_of_lt (sGlobal40_hz72 hc).2 (by norm_num), ?_, ?_,
    le_trans (sGlobal40_hz117 hc).2 (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (sGlobal40_hz64 hc).1) (sGlobal40_hz64 hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) sGlobal40_hz9.1 2
    nlinarith only [h1, h2]
  · linarith only [(sGlobal40_hz84 hc).1, sGlobal40_hz33.2]
  · have hap : 0 < s3ap 12225 46 := lt_of_lt_of_le (by norm_num) sGlobal40_hz9.1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul sGlobal40_hz16.2 sGlobal40_hz9.2 (le_trans (by norm_num) sGlobal40_hz9.1) (by norm_num)
    linarith only [h, (sGlobal40_hz84 hc).1, sGlobal40_hz33.2]

end BstLean.Part255
