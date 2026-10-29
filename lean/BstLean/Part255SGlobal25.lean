import BstLean.Part255SGlobal21
import BstLean.Part255Numeric10
namespace BstLean.Part255
open Real BstLean.Part130 BstLean.Part182 BstLean.Part197 BstLean.Part246
theorem sGlobal25_hz0 : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal25_hz1 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) ((√(23 : ℝ)) / (12225 : ℝ)) := bdiv sGlobal25_hz0 (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal25_hz2 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) maskSlack := by
    convert sGlobal25_hz1 using 1 <;>
      norm_num [maskSlack] <;> ring

theorem sGlobal25_hz3 : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal25_hz4 : B (6395294793910793 / 500000000000000000) (12790589587821587 / 1000000000000000000) (√((2 / 12225) : ℝ)) := bsqrt (bpoint ((2 / 12225) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal25_hz5 : B (7230130686979 / 62500000000000000) (23136418198333 / 200000000000000000) (√((2 / 149450625) : ℝ)) := bsqrt (bpoint ((2 / 149450625) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal25_hz6 : B (2211334438749598093 / 20000000000000000) (110566721937479904651 / 1000000000000000000) (√(12225 : ℝ)) := bsqrt (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal25_hz7 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))) := bmul sGlobal25_hz3 sGlobal25_hz4 (by norm_num) (by norm_num)

theorem sGlobal25_hz8 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) ((√(12225 : ℝ)) + ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := badd sGlobal25_hz6 sGlobal25_hz7 (by norm_num) (by norm_num)

theorem sGlobal25_hz9 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) (s3ap 12225 46) := by
    convert sGlobal25_hz8 using 1 <;>
      norm_num [s3ap, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal25_hz10 : B (163599182004089 / 1000000000000000000) (16359918200409 / 100000000000000000) ((2 : ℝ) / (12225 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal25_hz11 : B (1222499983640081799591 / 100000000000000000) (12224999836400817995911 / 1000000000000000000) ((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ))) := bsub (bpoint (12225 : ℝ)) sGlobal25_hz10 (by norm_num) (by norm_num)

theorem sGlobal25_hz12 : B (110566721197658827907 / 1000000000000000000) (27641680299414706977 / 250000000000000000) (√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) := bsqrt sGlobal25_hz11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal25_hz13 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) ((√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) - ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bsub sGlobal25_hz12 sGlobal25_hz7 (by norm_num) (by norm_num)

theorem sGlobal25_hz14 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) (s3am 12225 46) := by
    convert sGlobal25_hz13 using 1 <;>
      norm_num [s3am, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal25_hz15 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√((2 / 12225) : ℝ)) * (√(92 : ℝ))) := bmul sGlobal25_hz4 sGlobal25_hz3 (by norm_num) (by norm_num)

theorem sGlobal25_hz16 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) (s3e0 12225 46) := by
    convert sGlobal25_hz15 using 1 <;>
      norm_num [s3e0, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal25_hz17 : B (250196148528560847 / 500000000000000000) (100078459411424339 / 200000000000000000) (((1 / 2) : ℝ) + maskSlack) := badd (bpoint ((1 / 2) : ℝ)) sGlobal25_hz2 (by norm_num) (by norm_num)

theorem sGlobal25_hz18 : B (59827153232297998295487 / 800000000000000) (23930861292919199366019 / 320000000000000) ((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack)) := bmul (bpoint (149450625 : ℝ)) sGlobal25_hz17 (by norm_num) (by norm_num)

theorem sGlobal25_hz19 : B (1729554180017180009583 / 200000000000000000) (8647770900085900056557 / 1000000000000000000) (√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) := bsqrt sGlobal25_hz18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal25_hz20 : B (4328681281566262743499 / 500000000000000000) (8657362563132525495641 / 1000000000000000000) ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))) := badd sGlobal25_hz19 sGlobal25_hz3 (by norm_num) (by norm_num)

theorem sGlobal25_hz21 : B (110732771457999278473 / 1000000000000000000) (55366385728999643621 / 500000000000000000) ((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ)))) := bmul sGlobal25_hz4 sGlobal25_hz20 (by norm_num) (by norm_num)

theorem sGlobal25_hz22 : B (209099159 / 15625000000000000) (13382346177 / 1000000000000000000) ((2 : ℝ) / (149450625 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (149450625 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal25_hz23 : B (2452349334953899930479 / 200000000000000000) (12261746674769501594427 / 1000000000000000000) (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2) := bsq sGlobal25_hz21 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal25_hz24 : B (82045469362091 / 500000000000000000) (32818187747289 / 200000000000000000) (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2)) := bmul sGlobal25_hz22 sGlobal25_hz23 (by norm_num) (by norm_num)

theorem sGlobal25_hz25 : B (82045469362091 / 250000000000000000) (32818187747289 / 100000000000000000) ((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) := bmul (bpoint (2 : ℝ)) sGlobal25_hz24 (by norm_num) (by norm_num)

theorem sGlobal25_hz26 : B (117258080744995992792057 / 1000000000000000000) (58629040372497996396029 / 500000000000000000) (√(13749457500 : ℝ)) := bsqrt (bpoint (13749457500 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal25_hz27 : B (117304080744995992792057 / 1000000000000000000) (58652040372497996396029 / 500000000000000000) ((√(13749457500 : ℝ)) + (46 : ℝ)) := badd sGlobal25_hz26 (bpoint (46 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal25_hz28 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal25_hz25 sGlobal25_hz27 (by norm_num) (by norm_num)

theorem sGlobal25_hz29 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (s3rs 12225 46 maskSlack) := by
    convert sGlobal25_hz28 using 1 <;>
      norm_num [s3rs, s3pp, s3K, mA, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal25_hz30 : B (490797546012267 / 1000000000000000000) (49079754601227 / 100000000000000000) ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (3 : ℝ)) sGlobal25_hz10 (by norm_num) (by norm_num)

theorem sGlobal25_hz31 : B (490797546012267 / 500000000000000000) (49079754601227 / 50000000000000000) ((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal25_hz30 (by norm_num) (by norm_num)

theorem sGlobal25_hz32 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal25_hz31 sGlobal25_hz27 (by norm_num) (by norm_num)

theorem sGlobal25_hz33 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (s3r1 12225 46) := by
    convert sGlobal25_hz32 using 1 <;>
      norm_num [s3r1, mA] <;> ring

theorem sGlobal25_hz34 : B (163599182004089 / 500000000000000000) (16359918200409 / 50000000000000000) ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (2 : ℝ)) sGlobal25_hz10 (by norm_num) (by norm_num)

theorem sGlobal25_hz35 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal25_hz34 (by norm_num) (by norm_num)

theorem sGlobal25_hz36 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal25_hz35 sGlobal25_hz27 (by norm_num) (by norm_num)

theorem sGlobal25_hz37 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (s3rpp 12225 46) := by
    convert sGlobal25_hz36 using 1 <;>
      norm_num [s3rpp, mA] <;> ring

theorem sGlobal25_hz38 {c : ℝ} (hc : B (47 / 100) (19 / 40) c) : B (47 / 100) (19 / 40) c := hc

theorem sGlobal25_hz39 : B (131149218372080969 / 200000000000000000) (655746091860768091 / 1000000000000000000) (kdot ((47 / 100))) := by
    constructor
    · apply bkdot_lower (q := (600453343472309121 / 1000000000000000000)) (a := (540752774390463831 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (938208349175483 / 1562500000000000)) (a := (4224631049921041 / 7812500000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal25_hz40 : B (2209 / 10000) (2209 / 10000) (((47 / 100) : ℝ)^2) := bsq (bpoint ((47 / 100) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal25_hz41 : B (7791 / 10000) (7791 / 10000) ((1 : ℝ) - (((47 / 100) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal25_hz40 (by norm_num) (by norm_num)

theorem sGlobal25_hz42 : B (882666414904294407 / 1000000000000000000) (110333301863036801 / 125000000000000000) (√((1 : ℝ) - (((47 / 100) : ℝ)^2))) := bsqrt sGlobal25_hz41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal25_hz43 : B (140480723033220253 / 500000000000000000) (70240361516610127 / 250000000000000000) ((√((1 : ℝ) - (((47 / 100) : ℝ)^2))) / Real.pi) := bdiv sGlobal25_hz42 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal25_hz44 : B (308200663174390277 / 1000000000000000000) (308200663174561003 / 1000000000000000000) (((47 / 100) : ℝ) * (kdot ((47 / 100)))) := bmul (bpoint ((47 / 100) : ℝ)) sGlobal25_hz39 (by norm_num) (by norm_num)

theorem sGlobal25_hz45 : B (589162109240830783 / 1000000000000000000) (589162109241001511 / 1000000000000000000) (((√((1 : ℝ) - (((47 / 100) : ℝ)^2))) / Real.pi) + (((47 / 100) : ℝ) * (kdot ((47 / 100))))) := badd sGlobal25_hz43 sGlobal25_hz44 (by norm_num) (by norm_num)

theorem sGlobal25_hz46 : B (589162109240830783 / 1000000000000000000) (589162109241001511 / 1000000000000000000) (kappa ((47 / 100))) := by rw [kappa_eq]; exact sGlobal25_hz45

theorem sGlobal25_hz47 : B (657551944600841127 / 1000000000000000000) (657551944601106109 / 1000000000000000000) (kdot ((19 / 40))) := by
    constructor
    · apply bkdot_lower (q := (23864021568539717 / 40000000000000000)) (a := (268958073769527011 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (149150134803373231 / 250000000000000000)) (a := (537916147538637791 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal25_hz48 : B (361 / 1600) (361 / 1600) (((19 / 40) : ℝ)^2) := bsq (bpoint ((19 / 40) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal25_hz49 : B (1239 / 1600) (1239 / 1600) ((1 : ℝ) - (((19 / 40) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal25_hz48 (by norm_num) (by norm_num)

theorem sGlobal25_hz50 : B (879985795339902063 / 1000000000000000000) (54999112208743879 / 62500000000000000) (√((1 : ℝ) - (((19 / 40) : ℝ)^2))) := bsqrt sGlobal25_hz49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal25_hz51 : B (280108178357996737 / 1000000000000000000) (140054089178998369 / 500000000000000000) ((√((1 : ℝ) - (((19 / 40) : ℝ)^2))) / Real.pi) := bdiv sGlobal25_hz50 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal25_hz52 : B (62467434737079907 / 200000000000000000) (156168586842762701 / 500000000000000000) (((19 / 40) : ℝ) * (kdot ((19 / 40)))) := bmul (bpoint ((19 / 40) : ℝ)) sGlobal25_hz47 (by norm_num) (by norm_num)

theorem sGlobal25_hz53 : B (37027834502712267 / 62500000000000000) (29622267602176107 / 50000000000000000) (((√((1 : ℝ) - (((19 / 40) : ℝ)^2))) / Real.pi) + (((19 / 40) : ℝ) * (kdot ((19 / 40))))) := badd sGlobal25_hz51 sGlobal25_hz52 (by norm_num) (by norm_num)

theorem sGlobal25_hz54 : B (37027834502712267 / 62500000000000000) (29622267602176107 / 50000000000000000) (kappa ((19 / 40))) := by rw [kappa_eq]; exact sGlobal25_hz53

theorem sGlobal25_hz55 {c : ℝ} (hc : B (47 / 100) (19 / 40) c) : B (589162109240830783 / 1000000000000000000) (29622267602176107 / 50000000000000000) (kappa c) := bkappa (sGlobal25_hz38 hc) (by norm_num) (by norm_num) sGlobal25_hz46.1 sGlobal25_hz54.2

theorem sGlobal25_hz56 : B 24450 24450 ((2 : ℝ) * (12225 : ℝ)) := bmul (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal25_hz57 {c : ℝ} (hc : B (47 / 100) (19 / 40) c) : B (20377732397823893 / 50000000000000000) (410837890759169217 / 1000000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (sGlobal25_hz55 hc) (by norm_num) (by norm_num)

theorem sGlobal25_hz58 {c : ℝ} (hc : B (47 / 100) (19 / 40) c) : B (9964711142535883677 / 1000000000000000) (200899728581233747113 / 20000000000000000) (((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) := bmul sGlobal25_hz56 (sGlobal25_hz57 hc) (by norm_num) (by norm_num)

theorem sGlobal25_hz59 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (4 : ℝ)) sGlobal25_hz10 (by norm_num) (by norm_num)

theorem sGlobal25_hz60 {c : ℝ} (hc : B (47 / 100) (19 / 40) c) : B (62279440550869722879 / 6250000000000000) (5022492887332479669647 / 500000000000000000) ((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bsub (sGlobal25_hz58 hc) sGlobal25_hz59 (by norm_num) (by norm_num)

theorem sGlobal25_hz61 {c : ℝ} (hc : B (47 / 100) (19 / 40) c) : B (99823396496708904863 / 1000000000000000000) (25056169118932765511 / 250000000000000000) (√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) := bsqrt (sGlobal25_hz60 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal25_hz62 : B (30670756373515103 / 125000000000000000) (122683025494060423 / 500000000000000000) ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal25_hz7 (by norm_num) (by norm_num)

theorem sGlobal25_hz63 {c : ℝ} (hc : B (47 / 100) (19 / 40) c) : B (99578030445720784017 / 1000000000000000000) (4998965521237147061 / 50000000000000000) ((√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) - ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))))) := bsub (sGlobal25_hz61 hc) sGlobal25_hz62 (by norm_num) (by norm_num)

theorem sGlobal25_hz64 {c : ℝ} (hc : B (47 / 100) (19 / 40) c) : B (99578030445720784017 / 1000000000000000000) (4998965521237147061 / 50000000000000000) (s3dm 12225 46 c) := by
    convert (sGlobal25_hz63 hc) using 1 <;>
      norm_num [s3dm, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal25_hz65 : B (6126072185528622723889 / 500000000000000000) (2450428874211449090087 / 200000000000000000) ((s3ap 12225 46)^2) := bsq sGlobal25_hz9 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal25_hz66 : B (6126072185528622723889 / 250000000000000000) (2450428874211449090087 / 100000000000000000) ((2 : ℝ) * ((s3ap 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal25_hz65 (by norm_num) (by norm_num)

theorem sGlobal25_hz67 {c : ℝ} (hc : B (47 / 100) (19 / 40) c) : B (9915784147448895403603 / 1000000000000000000) (9995862513007112561499 / 1000000000000000000) ((s3dm 12225 46 c)^2) := bsq (sGlobal25_hz64 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal25_hz68 {c : ℝ} (hc : B (47 / 100) (19 / 40) c) : B (14508426229107378334057 / 1000000000000000000) (14588504594665595497267 / 1000000000000000000) (((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) := bsub sGlobal25_hz66 (sGlobal25_hz67 hc) (by norm_num) (by norm_num)

theorem sGlobal25_hz69 : B (1524735695971823534271 / 125000000000000000) (609894278388729413841 / 50000000000000000) ((s3am 12225 46)^2) := bsq sGlobal25_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal25_hz70 : B (1524735695971823534271 / 62500000000000000) (609894278388729413841 / 25000000000000000) ((2 : ℝ) * ((s3am 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal25_hz69 (by norm_num) (by norm_num)

theorem sGlobal25_hz71 {c : ℝ} (hc : B (47 / 100) (19 / 40) c) : B (297355352050460551 / 500000000000000000) (37374573326684657 / 62500000000000000) ((((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) / ((2 : ℝ) * ((s3am 12225 46)^2))) := bdiv (sGlobal25_hz68 hc) sGlobal25_hz70 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal25_hz72 {c : ℝ} (hc : B (47 / 100) (19 / 40) c) : B (297355352050460551 / 500000000000000000) (37374573326684657 / 62500000000000000) (s3c1 12225 46 c) := by
    convert (sGlobal25_hz71 hc) using 1 <;>
      norm_num [s3c1] <;> ring

theorem sGlobal25_hz73 {c : ℝ} (hc : B (47 / 100) (19 / 40) c) : B (131149218372080969 / 200000000000000000) (657551944601106109 / 1000000000000000000) (kdot c) := bkdot (sGlobal25_hz38 hc) sGlobal25_hz39.1 sGlobal25_hz47.2

theorem sGlobal25_hz74 : B (702733397767742689 / 1000000000000000000) (17568334944193569 / 25000000000000000) (kdot ((297355352050460551 / 500000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (126032230055461033 / 250000000000000000)) (a := (466945286865229399 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (504128920221844131 / 1000000000000000000)) (a := (466945286865229289 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal25_hz75 : B (352017511296854759 / 500000000000000000) (352017511296854787 / 500000000000000000) (kdot ((37374573326684657 / 62500000000000000))) := by
    constructor
    · apply bkdot_lower (q := (501567345794489251 / 1000000000000000000)) (a := (464900699369735657 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (2006269383177957 / 4000000000000000)) (a := (464900699369735571 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal25_hz76 {c : ℝ} (hc : B (47 / 100) (19 / 40) c) : B (702733397767742689 / 1000000000000000000) (352017511296854787 / 500000000000000000) (kdot (s3c1 12225 46 c)) := bkdot (sGlobal25_hz72 hc) sGlobal25_hz74.1 sGlobal25_hz75.2

theorem sGlobal25_hz77 {c : ℝ} (hc : B (47 / 100) (19 / 40) c) : B (2209 / 10000) (361 / 1600) (c^2) := bsq (sGlobal25_hz38 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal25_hz78 {c : ℝ} (hc : B (47 / 100) (19 / 40) c) : B (1239 / 1600) (7791 / 10000) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (sGlobal25_hz77 hc) (by norm_num) (by norm_num)

theorem sGlobal25_hz79 {c : ℝ} (hc : B (47 / 100) (19 / 40) c) : B (879985795339902063 / 1000000000000000000) (110333301863036801 / 125000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (sGlobal25_hz78 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal25_hz80 : B (39119999999999765769 / 1600000000000000) (3912000000000000489 / 160000000000000) ((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (149450625 : ℝ)) sGlobal25_hz10 (by norm_num) (by norm_num)

theorem sGlobal25_hz81 {c : ℝ} (hc : B (47 / 100) (19 / 40) c) : B (115409449237362167 / 200000000000000000) (580399017554405537 / 1000000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (sGlobal25_hz79 hc) (sGlobal25_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal25_hz82 {c : ℝ} (hc : B (47 / 100) (19 / 40) c) : B (14108805169267440439279 / 1000000000000000000) (2838151195841043430699 / 200000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) := bmul sGlobal25_hz80 (sGlobal25_hz81 hc) (by norm_num) (by norm_num)

theorem sGlobal25_hz83 {c : ℝ} (hc : B (47 / 100) (19 / 40) c) : B (7054402584633720219639 / 1000000000000000000) (1773844497400652144187 / 250000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) / (2 : ℝ)) := bdiv (sGlobal25_hz82 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal25_hz84 {c : ℝ} (hc : B (47 / 100) (19 / 40) c) : B (7054402584633720219639 / 1000000000000000000) (1773844497400652144187 / 250000000000000000) (s3Cpa 12225 c) := by
    convert (sGlobal25_hz83 hc) using 1 <;>
      norm_num [s3Cpa, mA] <;> ring

theorem sGlobal25_hz85 {c : ℝ} (hc : B (47 / 100) (19 / 40) c) : B (280108178357996737 / 1000000000000000000) (70240361516610127 / 250000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (sGlobal25_hz79 hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal25_hz86 {c : ℝ} (hc : B (47 / 100) (19 / 40) c) : B (308200663174390277 / 1000000000000000000) (156168586842762701 / 500000000000000000) (c * (kdot c)) := bmul (sGlobal25_hz38 hc) (sGlobal25_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal25_hz87 {c : ℝ} (hc : B (47 / 100) (19 / 40) c) : B (-6445799065505733 / 200000000000000000) (-27239217107949769 / 1000000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (sGlobal25_hz85 hc) (sGlobal25_hz86 hc) (by norm_num) (by norm_num)

theorem sGlobal25_hz88 {c : ℝ} (hc : B (47 / 100) (19 / 40) c) : B (-3151995743032303831 / 4000000000000000) (-665998858289367864381 / 1000000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) := bmul sGlobal25_hz80 (sGlobal25_hz87 hc) (by norm_num) (by norm_num)

theorem sGlobal25_hz89 {c : ℝ} (hc : B (47 / 100) (19 / 40) c) : B (-3151995743032303831 / 8000000000000000) (-33299942914468393219 / 100000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) / (2 : ℝ)) := bdiv (sGlobal25_hz88 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal25_hz90 {c : ℝ} (hc : B (47 / 100) (19 / 40) c) : B (-3151995743032303831 / 8000000000000000) (-33299942914468393219 / 100000000000000000) (s3Cpp 12225 c) := by
    convert (sGlobal25_hz89 hc) using 1 <;>
      norm_num [s3Cpp, mA] <;> ring

theorem sGlobal25_hz91 {c : ℝ} (hc : B (47 / 100) (19 / 40) c) : B (179238692364186448201 / 25000000000000000) (3605261549768173494487 / 500000000000000000) ((s3Cpa 12225 c) + (s3r1 12225 46)) := badd (sGlobal25_hz84 hc) sGlobal25_hz33 (by norm_num) (by norm_num)

theorem sGlobal25_hz92 {c : ℝ} (hc : B (47 / 100) (19 / 40) c) : B (32457830287730281639 / 500000000000000000) (65286666612970844219 / 1000000000000000000) (((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) := bdiv (sGlobal25_hz91 hc) sGlobal25_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal25_hz93 {c : ℝ} (hc : B (47 / 100) (19 / 40) c) : B (6503834360095462369 / 100000000000000000) (32704674819232452321 / 500000000000000000) ((((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) + (s3e0 12225 46)) := badd (sGlobal25_hz92 hc) sGlobal25_hz16 (by norm_num) (by norm_num)

theorem sGlobal25_hz94 {c : ℝ} (hc : B (47 / 100) (19 / 40) c) : B (6503834360095462369 / 100000000000000000) (32704674819232452321 / 500000000000000000) (s3Lam 12225 46 c) := by
    convert (sGlobal25_hz93 hc) using 1 <;>
      norm_num [s3Lam] <;> ring

theorem sGlobal25_hz95 {c : ℝ} (hc : B (47 / 100) (19 / 40) c) : B (-12689442450261846931 / 40000000000000000) (-64059005630547914343 / 250000000000000000) ((s3Cpp 12225 c) + (s3rpp 12225 46)) := badd (sGlobal25_hz90 hc) sGlobal25_hz37 (by norm_num) (by norm_num)

theorem sGlobal25_hz96 {c : ℝ} (hc : B (47 / 100) (19 / 40) c) : B (-55836324388572979883 / 250000000000000000) (-64059005630547914343 / 500000000000000000) (if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) := bweaken (bfirst (sGlobal25_hz95 hc) (sGlobal25_hz76 hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem sGlobal25_hz97 {c : ℝ} (hc : B (47 / 100) (19 / 40) c) : B (2114993069177917623559 / 500000000000000000) (4278383020126948951599 / 1000000000000000000) ((s3Lam 12225 46 c)^2) := bsq (sGlobal25_hz94 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal25_hz98 {c : ℝ} (hc : B (47 / 100) (19 / 40) c) : B (70736164314442667 / 200000000000000000) (357595835226042427 / 1000000000000000000) ((s3c1 12225 46 c)^2) := bsq (sGlobal25_hz72 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal25_hz99 {c : ℝ} (hc : B (47 / 100) (19 / 40) c) : B (642404164773957573 / 1000000000000000000) (129263835685557333 / 200000000000000000) ((1 : ℝ) - ((s3c1 12225 46 c)^2)) := bsub (bpoint (1 : ℝ)) (sGlobal25_hz98 hc) (by norm_num) (by norm_num)

theorem sGlobal25_hz100 {c : ℝ} (hc : B (47 / 100) (19 / 40) c) : B (400750597246578527 / 500000000000000000) (401969892662307069 / 500000000000000000) (√((1 : ℝ) - ((s3c1 12225 46 c)^2))) := bsqrt (sGlobal25_hz99 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal25_hz101 {c : ℝ} (hc : B (47 / 100) (19 / 40) c) : B (629497566115786561 / 250000000000000000) (1262825661752181623 / 500000000000000000) (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))) := bmul pi_mem (sGlobal25_hz100 hc) (by norm_num) (by norm_num)

theorem sGlobal25_hz102 {c : ℝ} (hc : B (47 / 100) (19 / 40) c) : B (837405008955609235941 / 500000000000000000) (1699126116771992837433 / 1000000000000000000) (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2))))) := bdiv (sGlobal25_hz97 hc) (sGlobal25_hz101 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal25_hz103 {c : ℝ} (hc : B (47 / 100) (19 / 40) c) : B (29029294407138531047 / 20000000000000000) (1571008105510897008747 / 1000000000000000000) ((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) := badd (sGlobal25_hz96 hc) (sGlobal25_hz102 hc) (by norm_num) (by norm_num)

theorem sGlobal25_hz104 : B (3762781186094069 / 250000000000000000) (376278118609407 / 25000000000000000) ((s3e0 12225 46)^2) := bsq sGlobal25_hz16 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal25_hz105 {c : ℝ} (hc : B (47 / 100) (19 / 40) c) : B (725739885740835464313 / 500000000000000000) (1571023156635641385027 / 1000000000000000000) (((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) := badd (sGlobal25_hz103 hc) sGlobal25_hz104 (by norm_num) (by norm_num)

theorem sGlobal25_hz106 {c : ℝ} (hc : B (47 / 100) (19 / 40) c) : B (1489976844932918198757 / 1000000000000000000) (1609520230089765655043 / 1000000000000000000) ((((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) + (s3rs 12225 46 maskSlack)) := badd (sGlobal25_hz105 hc) sGlobal25_hz29 (by norm_num) (by norm_num)

theorem sGlobal25_hz107 {c : ℝ} (hc : B (47 / 100) (19 / 40) c) : B (1489976844932918198757 / 1000000000000000000) (1609520230089765655043 / 1000000000000000000) (s3U 12225 46 maskSlack c) := by
    convert (sGlobal25_hz106 hc) using 1 <;>
      norm_num [s3U] <;> ring

theorem sGlobal25_hz108 {c : ℝ} (hc : B (47 / 100) (19 / 40) c) : B (-470762874501530253693 / 1000000000000000000) (-40976283576717573779 / 100000000000000000) ((s3Cpp 12225 c) - (s3rpp 12225 46)) := bsub (sGlobal25_hz90 hc) sGlobal25_hz37 (by norm_num) (by norm_num)

theorem sGlobal25_hz109 {c : ℝ} (hc : B (47 / 100) (19 / 40) c) : B (-470762874501530253693 / 1000000000000000000) (-40976283576717573779 / 100000000000000000) (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ)) := bweaken (bmin (sGlobal25_hz108 hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem sGlobal25_hz110 {c : ℝ} (hc : B (47 / 100) (19 / 40) c) : B (-82858387746491129217 / 250000000000000000) (-287954029857612928697 / 1000000000000000000) ((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) := bmul (sGlobal25_hz76 hc) (sGlobal25_hz109 hc) (by norm_num) (by norm_num)

theorem sGlobal25_hz111 {c : ℝ} (hc : B (47 / 100) (19 / 40) c) : B (-82862150527677223287 / 250000000000000000) (-287969080982357304973 / 1000000000000000000) (((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) := bsub (sGlobal25_hz110 hc) sGlobal25_hz104 (by norm_num) (by norm_num)

theorem sGlobal25_hz112 {c : ℝ} (hc : B (47 / 100) (19 / 40) c) : B (-92486418891208290791 / 250000000000000000) (-2550516831512535743 / 7812500000000000) ((((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) - (s3rs 12225 46 maskSlack)) := bsub (sGlobal25_hz111 hc) sGlobal25_hz29 (by norm_num) (by norm_num)

theorem sGlobal25_hz113 {c : ℝ} (hc : B (47 / 100) (19 / 40) c) : B (-92486418891208290791 / 250000000000000000) (-2550516831512535743 / 7812500000000000) (s3L 12225 46 maskSlack c) := by
    convert (sGlobal25_hz112 hc) using 1 <;>
      norm_num [s3L] <;> ring

theorem sGlobal25_hz114 {c : ℝ} (hc : B (47 / 100) (19 / 40) c) : B 0 (1609520230089765655043 / 1000000000000000000) |(s3U 12225 46 maskSlack c)| := bweaken (babs (sGlobal25_hz107 hc)) (by norm_num) (by norm_num)

theorem sGlobal25_hz115 {c : ℝ} (hc : B (47 / 100) (19 / 40) c) : B 0 (92486418891208290791 / 250000000000000000) |(s3L 12225 46 maskSlack c)| := bweaken (babs (sGlobal25_hz113 hc)) (by norm_num) (by norm_num)

theorem sGlobal25_hz116 {c : ℝ} (hc : B (47 / 100) (19 / 40) c) : B 0 (1609520230089765655043 / 1000000000000000000) (max |(s3U 12225 46 maskSlack c)| |(s3L 12225 46 maskSlack c)|) := bweaken (bmax (sGlobal25_hz114 hc) (sGlobal25_hz115 hc)) (by norm_num) (by norm_num)

theorem sGlobal25_hz117 {c : ℝ} (hc : B (47 / 100) (19 / 40) c) : B 0 (1609520230089765655043 / 1000000000000000000) (s3nks 12225 46 maskSlack c) := by
    convert (sGlobal25_hz116 hc) using 1 <;>
      norm_num [s3nks] <;> ring

theorem sGlobal25 {c : ℝ} (hc : B (47 / 100) (19 / 40) c) :
    0 < s3am 12225 46 ∧ 0 ≤ s3dm 12225 46 c ∧
    s3dm 12225 46 c ^ 2 ≤ 2 * s3ap 12225 46 ^ 2 ∧ s3c1 12225 46 c < 1 ∧
    0 ≤ s3Cpa 12225 c - s3r1 12225 46 ∧
    s3e0 12225 46 ≤ (s3Cpa 12225 c - s3r1 12225 46) / s3ap 12225 46 ∧
    s3nks 12225 46 maskSlack c ≤ 12225 * (131659 / 1000000) := by

  refine ⟨lt_of_lt_of_le (by norm_num) sGlobal25_hz14.1,
    le_trans (by norm_num) (sGlobal25_hz64 hc).1, ?_,
    lt_of_le_of_lt (sGlobal25_hz72 hc).2 (by norm_num), ?_, ?_,
    le_trans (sGlobal25_hz117 hc).2 (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (sGlobal25_hz64 hc).1) (sGlobal25_hz64 hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) sGlobal25_hz9.1 2
    nlinarith only [h1, h2]
  · linarith only [(sGlobal25_hz84 hc).1, sGlobal25_hz33.2]
  · have hap : 0 < s3ap 12225 46 := lt_of_lt_of_le (by norm_num) sGlobal25_hz9.1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul sGlobal25_hz16.2 sGlobal25_hz9.2 (le_trans (by norm_num) sGlobal25_hz9.1) (by norm_num)
    linarith only [h, (sGlobal25_hz84 hc).1, sGlobal25_hz33.2]

end BstLean.Part255
