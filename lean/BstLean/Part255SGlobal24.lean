import BstLean.Part255SGlobal20
import BstLean.Part255Numeric10
namespace BstLean.Part255
open Real BstLean.Part130 BstLean.Part182 BstLean.Part197 BstLean.Part246
theorem sGlobal24_hz0 : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal24_hz1 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) ((√(23 : ℝ)) / (12225 : ℝ)) := bdiv sGlobal24_hz0 (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal24_hz2 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) maskSlack := by
    convert sGlobal24_hz1 using 1 <;>
      norm_num [maskSlack] <;> ring

theorem sGlobal24_hz3 : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal24_hz4 : B (6395294793910793 / 500000000000000000) (12790589587821587 / 1000000000000000000) (√((2 / 12225) : ℝ)) := bsqrt (bpoint ((2 / 12225) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal24_hz5 : B (7230130686979 / 62500000000000000) (23136418198333 / 200000000000000000) (√((2 / 149450625) : ℝ)) := bsqrt (bpoint ((2 / 149450625) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal24_hz6 : B (2211334438749598093 / 20000000000000000) (110566721937479904651 / 1000000000000000000) (√(12225 : ℝ)) := bsqrt (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal24_hz7 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))) := bmul sGlobal24_hz3 sGlobal24_hz4 (by norm_num) (by norm_num)

theorem sGlobal24_hz8 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) ((√(12225 : ℝ)) + ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := badd sGlobal24_hz6 sGlobal24_hz7 (by norm_num) (by norm_num)

theorem sGlobal24_hz9 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) (s3ap 12225 46) := by
    convert sGlobal24_hz8 using 1 <;>
      norm_num [s3ap, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal24_hz10 : B (163599182004089 / 1000000000000000000) (16359918200409 / 100000000000000000) ((2 : ℝ) / (12225 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal24_hz11 : B (1222499983640081799591 / 100000000000000000) (12224999836400817995911 / 1000000000000000000) ((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ))) := bsub (bpoint (12225 : ℝ)) sGlobal24_hz10 (by norm_num) (by norm_num)

theorem sGlobal24_hz12 : B (110566721197658827907 / 1000000000000000000) (27641680299414706977 / 250000000000000000) (√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) := bsqrt sGlobal24_hz11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal24_hz13 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) ((√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) - ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bsub sGlobal24_hz12 sGlobal24_hz7 (by norm_num) (by norm_num)

theorem sGlobal24_hz14 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) (s3am 12225 46) := by
    convert sGlobal24_hz13 using 1 <;>
      norm_num [s3am, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal24_hz15 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√((2 / 12225) : ℝ)) * (√(92 : ℝ))) := bmul sGlobal24_hz4 sGlobal24_hz3 (by norm_num) (by norm_num)

theorem sGlobal24_hz16 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) (s3e0 12225 46) := by
    convert sGlobal24_hz15 using 1 <;>
      norm_num [s3e0, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal24_hz17 : B (250196148528560847 / 500000000000000000) (100078459411424339 / 200000000000000000) (((1 / 2) : ℝ) + maskSlack) := badd (bpoint ((1 / 2) : ℝ)) sGlobal24_hz2 (by norm_num) (by norm_num)

theorem sGlobal24_hz18 : B (59827153232297998295487 / 800000000000000) (23930861292919199366019 / 320000000000000) ((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack)) := bmul (bpoint (149450625 : ℝ)) sGlobal24_hz17 (by norm_num) (by norm_num)

theorem sGlobal24_hz19 : B (1729554180017180009583 / 200000000000000000) (8647770900085900056557 / 1000000000000000000) (√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) := bsqrt sGlobal24_hz18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal24_hz20 : B (4328681281566262743499 / 500000000000000000) (8657362563132525495641 / 1000000000000000000) ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))) := badd sGlobal24_hz19 sGlobal24_hz3 (by norm_num) (by norm_num)

theorem sGlobal24_hz21 : B (110732771457999278473 / 1000000000000000000) (55366385728999643621 / 500000000000000000) ((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ)))) := bmul sGlobal24_hz4 sGlobal24_hz20 (by norm_num) (by norm_num)

theorem sGlobal24_hz22 : B (209099159 / 15625000000000000) (13382346177 / 1000000000000000000) ((2 : ℝ) / (149450625 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (149450625 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal24_hz23 : B (2452349334953899930479 / 200000000000000000) (12261746674769501594427 / 1000000000000000000) (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2) := bsq sGlobal24_hz21 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal24_hz24 : B (82045469362091 / 500000000000000000) (32818187747289 / 200000000000000000) (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2)) := bmul sGlobal24_hz22 sGlobal24_hz23 (by norm_num) (by norm_num)

theorem sGlobal24_hz25 : B (82045469362091 / 250000000000000000) (32818187747289 / 100000000000000000) ((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) := bmul (bpoint (2 : ℝ)) sGlobal24_hz24 (by norm_num) (by norm_num)

theorem sGlobal24_hz26 : B (117258080744995992792057 / 1000000000000000000) (58629040372497996396029 / 500000000000000000) (√(13749457500 : ℝ)) := bsqrt (bpoint (13749457500 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal24_hz27 : B (117304080744995992792057 / 1000000000000000000) (58652040372497996396029 / 500000000000000000) ((√(13749457500 : ℝ)) + (46 : ℝ)) := badd sGlobal24_hz26 (bpoint (46 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal24_hz28 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal24_hz25 sGlobal24_hz27 (by norm_num) (by norm_num)

theorem sGlobal24_hz29 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (s3rs 12225 46 maskSlack) := by
    convert sGlobal24_hz28 using 1 <;>
      norm_num [s3rs, s3pp, s3K, mA, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal24_hz30 : B (490797546012267 / 1000000000000000000) (49079754601227 / 100000000000000000) ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (3 : ℝ)) sGlobal24_hz10 (by norm_num) (by norm_num)

theorem sGlobal24_hz31 : B (490797546012267 / 500000000000000000) (49079754601227 / 50000000000000000) ((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal24_hz30 (by norm_num) (by norm_num)

theorem sGlobal24_hz32 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal24_hz31 sGlobal24_hz27 (by norm_num) (by norm_num)

theorem sGlobal24_hz33 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (s3r1 12225 46) := by
    convert sGlobal24_hz32 using 1 <;>
      norm_num [s3r1, mA] <;> ring

theorem sGlobal24_hz34 : B (163599182004089 / 500000000000000000) (16359918200409 / 50000000000000000) ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (2 : ℝ)) sGlobal24_hz10 (by norm_num) (by norm_num)

theorem sGlobal24_hz35 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal24_hz34 (by norm_num) (by norm_num)

theorem sGlobal24_hz36 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal24_hz35 sGlobal24_hz27 (by norm_num) (by norm_num)

theorem sGlobal24_hz37 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (s3rpp 12225 46) := by
    convert sGlobal24_hz36 using 1 <;>
      norm_num [s3rpp, mA] <;> ring

theorem sGlobal24_hz38 {c : ℝ} (hc : B (93 / 200) (47 / 100) c) : B (93 / 200) (47 / 100) c := hc

theorem sGlobal24_hz39 : B (653945678051333057 / 1000000000000000000) (326972839025915031 / 500000000000000000) (kdot ((93 / 200))) := by
    constructor
    · apply bkdot_lower (q := (604307631352261019 / 1000000000000000000)) (a := (108716171557692921 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (302153815676130509 / 500000000000000000)) (a := (67947607223460489 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal24_hz40 : B (8649 / 40000) (8649 / 40000) (((93 / 200) : ℝ)^2) := bsq (bpoint ((93 / 200) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal24_hz41 : B (31351 / 40000) (31351 / 40000) ((1 : ℝ) - (((93 / 200) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal24_hz40 (by norm_num) (by norm_num)

theorem sGlobal24_hz42 : B (110663834991382799 / 125000000000000000) (885310679931062393 / 1000000000000000000) (√((1 : ℝ) - (((93 / 200) : ℝ)^2))) := bsqrt sGlobal24_hz41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal24_hz43 : B (140901570883075401 / 500000000000000000) (281803141766150803 / 1000000000000000000) ((√((1 : ℝ) - (((93 / 200) : ℝ)^2))) / Real.pi) := bdiv sGlobal24_hz42 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal24_hz44 : B (304084740293869871 / 1000000000000000000) (304084740294100979 / 1000000000000000000) (((93 / 200) : ℝ) * (kdot ((93 / 200)))) := bmul (bpoint ((93 / 200) : ℝ)) sGlobal24_hz39 (by norm_num) (by norm_num)

theorem sGlobal24_hz45 : B (585887882060020673 / 1000000000000000000) (292943941030125891 / 500000000000000000) (((√((1 : ℝ) - (((93 / 200) : ℝ)^2))) / Real.pi) + (((93 / 200) : ℝ) * (kdot ((93 / 200))))) := badd sGlobal24_hz43 sGlobal24_hz44 (by norm_num) (by norm_num)

theorem sGlobal24_hz46 : B (585887882060020673 / 1000000000000000000) (292943941030125891 / 500000000000000000) (kappa ((93 / 200))) := by rw [kappa_eq]; exact sGlobal24_hz45

theorem sGlobal24_hz47 : B (131149218372080969 / 200000000000000000) (655746091860768091 / 1000000000000000000) (kdot ((47 / 100))) := by
    constructor
    · apply bkdot_lower (q := (600453343472309121 / 1000000000000000000)) (a := (540752774390463831 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (938208349175483 / 1562500000000000)) (a := (4224631049921041 / 7812500000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal24_hz48 : B (2209 / 10000) (2209 / 10000) (((47 / 100) : ℝ)^2) := bsq (bpoint ((47 / 100) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal24_hz49 : B (7791 / 10000) (7791 / 10000) ((1 : ℝ) - (((47 / 100) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal24_hz48 (by norm_num) (by norm_num)

theorem sGlobal24_hz50 : B (882666414904294407 / 1000000000000000000) (110333301863036801 / 125000000000000000) (√((1 : ℝ) - (((47 / 100) : ℝ)^2))) := bsqrt sGlobal24_hz49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal24_hz51 : B (140480723033220253 / 500000000000000000) (70240361516610127 / 250000000000000000) ((√((1 : ℝ) - (((47 / 100) : ℝ)^2))) / Real.pi) := bdiv sGlobal24_hz50 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal24_hz52 : B (308200663174390277 / 1000000000000000000) (308200663174561003 / 1000000000000000000) (((47 / 100) : ℝ) * (kdot ((47 / 100)))) := bmul (bpoint ((47 / 100) : ℝ)) sGlobal24_hz47 (by norm_num) (by norm_num)

theorem sGlobal24_hz53 : B (589162109240830783 / 1000000000000000000) (589162109241001511 / 1000000000000000000) (((√((1 : ℝ) - (((47 / 100) : ℝ)^2))) / Real.pi) + (((47 / 100) : ℝ) * (kdot ((47 / 100))))) := badd sGlobal24_hz51 sGlobal24_hz52 (by norm_num) (by norm_num)

theorem sGlobal24_hz54 : B (589162109240830783 / 1000000000000000000) (589162109241001511 / 1000000000000000000) (kappa ((47 / 100))) := by rw [kappa_eq]; exact sGlobal24_hz53

theorem sGlobal24_hz55 {c : ℝ} (hc : B (93 / 200) (47 / 100) c) : B (585887882060020673 / 1000000000000000000) (589162109241001511 / 1000000000000000000) (kappa c) := bkappa (sGlobal24_hz38 hc) (by norm_num) (by norm_num) sGlobal24_hz46.1 sGlobal24_hz54.2

theorem sGlobal24_hz56 : B 24450 24450 ((2 : ℝ) * (12225 : ℝ)) := bmul (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal24_hz57 {c : ℝ} (hc : B (93 / 200) (47 / 100) c) : B (410837890758998489 / 1000000000000000000) (414112117939979327 / 1000000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (sGlobal24_hz55 hc) (by norm_num) (by norm_num)

theorem sGlobal24_hz58 {c : ℝ} (hc : B (93 / 200) (47 / 100) c) : B (200899728581150261121 / 20000000000000000) (202500825672649890903 / 20000000000000000) (((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) := bmul sGlobal24_hz56 (sGlobal24_hz57 hc) (by norm_num) (by norm_num)

theorem sGlobal24_hz59 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (4 : ℝ)) sGlobal24_hz10 (by norm_num) (by norm_num)

theorem sGlobal24_hz60 {c : ℝ} (hc : B (93 / 200) (47 / 100) c) : B (1004498577466078503969 / 100000000000000000) (5062520314617883264397 / 500000000000000000) ((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bsub (sGlobal24_hz58 hc) sGlobal24_hz59 (by norm_num) (by norm_num)

theorem sGlobal24_hz61 {c : ℝ} (hc : B (93 / 200) (47 / 100) c) : B (50112338237855118667 / 500000000000000000) (50311630437791833027 / 500000000000000000) (√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) := bsqrt (sGlobal24_hz60 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal24_hz62 : B (30670756373515103 / 125000000000000000) (122683025494060423 / 500000000000000000) ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal24_hz7 (by norm_num) (by norm_num)

theorem sGlobal24_hz63 {c : ℝ} (hc : B (93 / 200) (47 / 100) c) : B (12497413803090264561 / 125000000000000000) (10037789482459554523 / 100000000000000000) ((√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) - ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))))) := bsub (sGlobal24_hz61 hc) sGlobal24_hz62 (by norm_num) (by norm_num)

theorem sGlobal24_hz64 {c : ℝ} (hc : B (93 / 200) (47 / 100) c) : B (12497413803090264561 / 125000000000000000) (10037789482459554523 / 100000000000000000) (s3dm 12225 46 c) := by
    convert (sGlobal24_hz63 hc) using 1 <;>
      norm_num [s3dm, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal24_hz65 : B (6126072185528622723889 / 500000000000000000) (2450428874211449090087 / 200000000000000000) ((s3ap 12225 46)^2) := bsq sGlobal24_hz9 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal24_hz66 : B (6126072185528622723889 / 250000000000000000) (2450428874211449090087 / 100000000000000000) ((2 : ℝ) * ((s3ap 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal24_hz65 (by norm_num) (by norm_num)

theorem sGlobal24_hz67 {c : ℝ} (hc : B (93 / 200) (47 / 100) c) : B (1249482814125368559601 / 125000000000000000) (10075721769417565143897 / 1000000000000000000) ((s3dm 12225 46 c)^2) := bsq (sGlobal24_hz64 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal24_hz68 {c : ℝ} (hc : B (93 / 200) (47 / 100) c) : B (14428566972696925751659 / 1000000000000000000) (7254213114555771212031 / 500000000000000000) (((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) := bsub sGlobal24_hz66 (sGlobal24_hz67 hc) (by norm_num) (by norm_num)

theorem sGlobal24_hz69 : B (1524735695971823534271 / 125000000000000000) (609894278388729413841 / 50000000000000000) ((s3am 12225 46)^2) := bsq sGlobal24_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal24_hz70 : B (1524735695971823534271 / 62500000000000000) (609894278388729413841 / 25000000000000000) ((2 : ℝ) * ((s3am 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal24_hz69 (by norm_num) (by norm_num)

theorem sGlobal24_hz71 {c : ℝ} (hc : B (93 / 200) (47 / 100) c) : B (591437216414603091 / 1000000000000000000) (37169419006318237 / 62500000000000000) ((((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) / ((2 : ℝ) * ((s3am 12225 46)^2))) := bdiv (sGlobal24_hz68 hc) sGlobal24_hz70 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal24_hz72 {c : ℝ} (hc : B (93 / 200) (47 / 100) c) : B (591437216414603091 / 1000000000000000000) (37169419006318237 / 62500000000000000) (s3c1 12225 46 c) := by
    convert (sGlobal24_hz71 hc) using 1 <;>
      norm_num [s3c1] <;> ring

theorem sGlobal24_hz73 {c : ℝ} (hc : B (93 / 200) (47 / 100) c) : B (653945678051333057 / 1000000000000000000) (655746091860768091 / 1000000000000000000) (kdot c) := bkdot (sGlobal24_hz38 hc) sGlobal24_hz39.1 sGlobal24_hz47.2

theorem sGlobal24_hz74 : B (701439243900150161 / 1000000000000000000) (175359810975037563 / 250000000000000000) (kdot ((591437216414603091 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (253340516254596351 / 500000000000000000)) (a := (468978139006751151 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (506681032509192701 / 1000000000000000000)) (a := (46897813900675101 / 100000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal24_hz75 : B (702733397767810271 / 1000000000000000000) (702733397767810343 / 1000000000000000000) (kdot ((37169419006318237 / 62500000000000000))) := by
    constructor
    · apply bkdot_lower (q := (252064460110855497 / 500000000000000000)) (a := (466945286865123241 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (504128920221710993 / 1000000000000000000)) (a := (46694528686512313 / 100000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal24_hz76 {c : ℝ} (hc : B (93 / 200) (47 / 100) c) : B (701439243900150161 / 1000000000000000000) (702733397767810343 / 1000000000000000000) (kdot (s3c1 12225 46 c)) := bkdot (sGlobal24_hz72 hc) sGlobal24_hz74.1 sGlobal24_hz75.2

theorem sGlobal24_hz77 {c : ℝ} (hc : B (93 / 200) (47 / 100) c) : B (8649 / 40000) (2209 / 10000) (c^2) := bsq (sGlobal24_hz38 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal24_hz78 {c : ℝ} (hc : B (93 / 200) (47 / 100) c) : B (7791 / 10000) (31351 / 40000) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (sGlobal24_hz77 hc) (by norm_num) (by norm_num)

theorem sGlobal24_hz79 {c : ℝ} (hc : B (93 / 200) (47 / 100) c) : B (882666414904294407 / 1000000000000000000) (885310679931062393 / 1000000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (sGlobal24_hz78 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal24_hz80 : B (39119999999999765769 / 1600000000000000) (3912000000000000489 / 160000000000000) ((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (149450625 : ℝ)) sGlobal24_hz10 (by norm_num) (by norm_num)

theorem sGlobal24_hz81 {c : ℝ} (hc : B (93 / 200) (47 / 100) c) : B (144303971796932019 / 250000000000000000) (290269509223696749 / 500000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (sGlobal24_hz79 hc) (sGlobal24_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal24_hz82 {c : ℝ} (hc : B (93 / 200) (47 / 100) c) : B (176411605521748336963 / 12500000000000000) (14194179001038772800373 / 1000000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) := bmul sGlobal24_hz80 (sGlobal24_hz81 hc) (by norm_num) (by norm_num)

theorem sGlobal24_hz83 {c : ℝ} (hc : B (93 / 200) (47 / 100) c) : B (176411605521748336963 / 25000000000000000) (7097089500519386400187 / 1000000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) / (2 : ℝ)) := bdiv (sGlobal24_hz82 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal24_hz84 {c : ℝ} (hc : B (93 / 200) (47 / 100) c) : B (176411605521748336963 / 25000000000000000) (7097089500519386400187 / 1000000000000000000) (s3Cpa 12225 c) := by
    convert (sGlobal24_hz83 hc) using 1 <;>
      norm_num [s3Cpa, mA] <;> ring

theorem sGlobal24_hz85 {c : ℝ} (hc : B (93 / 200) (47 / 100) c) : B (140480723033220253 / 500000000000000000) (281803141766150803 / 1000000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (sGlobal24_hz79 hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal24_hz86 {c : ℝ} (hc : B (93 / 200) (47 / 100) c) : B (304084740293869871 / 1000000000000000000) (308200663174561003 / 1000000000000000000) (c * (kdot c)) := bmul (sGlobal24_hz38 hc) (sGlobal24_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal24_hz87 {c : ℝ} (hc : B (93 / 200) (47 / 100) c) : B (-27239217108120497 / 1000000000000000000) (-5570399631929767 / 250000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (sGlobal24_hz85 hc) (sGlobal24_hz86 hc) (by norm_num) (by norm_num)

theorem sGlobal24_hz88 {c : ℝ} (hc : B (93 / 200) (47 / 100) c) : B (-6659988582935462349 / 10000000000000000) (-544785084002727950699 / 1000000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) := bmul sGlobal24_hz80 (sGlobal24_hz87 hc) (by norm_num) (by norm_num)

theorem sGlobal24_hz89 {c : ℝ} (hc : B (93 / 200) (47 / 100) c) : B (-6659988582935462349 / 20000000000000000) (-272392542001363975349 / 1000000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) / (2 : ℝ)) := bdiv (sGlobal24_hz88 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal24_hz90 {c : ℝ} (hc : B (93 / 200) (47 / 100) c) : B (-6659988582935462349 / 20000000000000000) (-272392542001363975349 / 1000000000000000000) (s3Cpp 12225 c) := by
    convert (sGlobal24_hz89 hc) using 1 <;>
      norm_num [s3Cpp, mA] <;> ring

theorem sGlobal24_hz91 {c : ℝ} (hc : B (93 / 200) (47 / 100) c) : B (7171609330803671186921 / 1000000000000000000) (7212234610453124812413 / 1000000000000000000) ((s3Cpa 12225 c) + (s3r1 12225 46)) := badd (sGlobal24_hz84 hc) sGlobal24_hz33 (by norm_num) (by norm_num)

theorem sGlobal24_hz92 {c : ℝ} (hc : B (93 / 200) (47 / 100) c) : B (3246716368530580081 / 50000000000000000) (13060432649538570947 / 200000000000000000) (((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) := bdiv (sGlobal24_hz91 hc) sGlobal24_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal24_hz93 {c : ℝ} (hc : B (93 / 200) (47 / 100) c) : B (4066063149756603877 / 62500000000000000) (32712423136593457579 / 500000000000000000) ((((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) + (s3e0 12225 46)) := badd (sGlobal24_hz92 hc) sGlobal24_hz16 (by norm_num) (by norm_num)

theorem sGlobal24_hz94 {c : ℝ} (hc : B (93 / 200) (47 / 100) c) : B (4066063149756603877 / 62500000000000000) (32712423136593457579 / 500000000000000000) (s3Lam 12225 46 c) := by
    convert (sGlobal24_hz93 hc) using 1 <;>
      norm_num [s3Lam] <;> ring

theorem sGlobal24_hz95 {c : ℝ} (hc : B (93 / 200) (47 / 100) c) : B (-5124720450485626237 / 20000000000000000) (-195629135378871700531 / 1000000000000000000) ((s3Cpp 12225 c) + (s3rpp 12225 46)) := badd (sGlobal24_hz90 hc) sGlobal24_hz37 (by norm_num) (by norm_num)

theorem sGlobal24_hz96 {c : ℝ} (hc : B (93 / 200) (47 / 100) c) : B (-45016402684749347401 / 250000000000000000) (-19562913537887170053 / 200000000000000000) (if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) := bweaken (bfirst (sGlobal24_hz95 hc) (sGlobal24_hz76 hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem sGlobal24_hz97 {c : ℝ} (hc : B (93 / 200) (47 / 100) c) : B (1058103650419750047161 / 250000000000000000) (2140205254935069890743 / 500000000000000000) ((s3Lam 12225 46 c)^2) := bsq (sGlobal24_hz94 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal24_hz98 {c : ℝ} (hc : B (93 / 200) (47 / 100) c) : B (349797980960254051 / 1000000000000000000) (176840410786208179 / 500000000000000000) ((s3c1 12225 46 c)^2) := bsq (sGlobal24_hz72 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal24_hz99 {c : ℝ} (hc : B (93 / 200) (47 / 100) c) : B (323159589213791821 / 500000000000000000) (650202019039745949 / 1000000000000000000) ((1 : ℝ) - ((s3c1 12225 46 c)^2)) := bsub (bpoint (1 : ℝ)) (sGlobal24_hz98 hc) (by norm_num) (by norm_num)

theorem sGlobal24_hz100 {c : ℝ} (hc : B (93 / 200) (47 / 100) c) : B (80393978532448787 / 100000000000000000) (16127021039730133 / 20000000000000000) (√((1 : ℝ) - ((s3c1 12225 46 c)^2))) := bsqrt (sGlobal24_hz99 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal24_hz101 {c : ℝ} (hc : B (93 / 200) (47 / 100) c) : B (1262825661751983281 / 500000000000000000) (1266613270567605373 / 500000000000000000) (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))) := bmul pi_mem (sGlobal24_hz100 hc) (by norm_num) (by norm_num)

theorem sGlobal24_hz102 {c : ℝ} (hc : B (93 / 200) (47 / 100) c) : B (417690101235708574149 / 250000000000000000) (847387458046209075563 / 500000000000000000) (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2))))) := bdiv (sGlobal24_hz97 hc) (sGlobal24_hz101 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal24_hz103 {c : ℝ} (hc : B (93 / 200) (47 / 100) c) : B (93168424637739806687 / 62500000000000000) (1596960348402982300861 / 1000000000000000000) ((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) := badd (sGlobal24_hz96 hc) (sGlobal24_hz102 hc) (by norm_num) (by norm_num)

theorem sGlobal24_hz104 : B (3762781186094069 / 250000000000000000) (376278118609407 / 25000000000000000) ((s3e0 12225 46)^2) := bsq sGlobal24_hz16 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal24_hz105 {c : ℝ} (hc : B (93 / 200) (47 / 100) c) : B (372677461332145320817 / 250000000000000000) (1596975399527726677141 / 1000000000000000000) (((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) := badd (sGlobal24_hz103 hc) sGlobal24_hz104 (by norm_num) (by norm_num)

theorem sGlobal24_hz106 {c : ℝ} (hc : B (93 / 200) (47 / 100) c) : B (1529206918779828553399 / 1000000000000000000) (1635472472981850947157 / 1000000000000000000) ((((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) + (s3rs 12225 46 maskSlack)) := badd (sGlobal24_hz105 hc) sGlobal24_hz29 (by norm_num) (by norm_num)

theorem sGlobal24_hz107 {c : ℝ} (hc : B (93 / 200) (47 / 100) c) : B (1529206918779828553399 / 1000000000000000000) (1635472472981850947157 / 1000000000000000000) (s3U 12225 46 maskSlack c) := by
    convert (sGlobal24_hz106 hc) using 1 <;>
      norm_num [s3U] <;> ring

theorem sGlobal24_hz108 {c : ℝ} (hc : B (93 / 200) (47 / 100) c) : B (-102440708942316348067 / 250000000000000000) (-349155948623855780949 / 1000000000000000000) ((s3Cpp 12225 c) - (s3rpp 12225 46)) := bsub (sGlobal24_hz90 hc) sGlobal24_hz37 (by norm_num) (by norm_num)

theorem sGlobal24_hz109 {c : ℝ} (hc : B (93 / 200) (47 / 100) c) : B (-102440708942316348067 / 250000000000000000) (-349155948623855780949 / 1000000000000000000) (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ)) := bweaken (bmin (sGlobal24_hz108 hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem sGlobal24_hz110 {c : ℝ} (hc : B (93 / 200) (47 / 100) c) : B (-17997126866194320049 / 62500000000000000) (-244911684605957074097 / 1000000000000000000) ((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) := bmul (sGlobal24_hz76 hc) (sGlobal24_hz109 hc) (by norm_num) (by norm_num)

theorem sGlobal24_hz111 {c : ℝ} (hc : B (93 / 200) (47 / 100) c) : B (-35996135122981687133 / 125000000000000000) (-244926735730701450373 / 1000000000000000000) (((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) := bsub (sGlobal24_hz110 hc) sGlobal24_hz104 (by norm_num) (by norm_num)

theorem sGlobal24_hz112 {c : ℝ} (hc : B (93 / 200) (47 / 100) c) : B (-8161653860949444177 / 25000000000000000) (-35427976147743590063 / 125000000000000000) ((((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) - (s3rs 12225 46 maskSlack)) := bsub (sGlobal24_hz111 hc) sGlobal24_hz29 (by norm_num) (by norm_num)

theorem sGlobal24_hz113 {c : ℝ} (hc : B (93 / 200) (47 / 100) c) : B (-8161653860949444177 / 25000000000000000) (-35427976147743590063 / 125000000000000000) (s3L 12225 46 maskSlack c) := by
    convert (sGlobal24_hz112 hc) using 1 <;>
      norm_num [s3L] <;> ring

theorem sGlobal24_hz114 {c : ℝ} (hc : B (93 / 200) (47 / 100) c) : B 0 (1635472472981850947157 / 1000000000000000000) |(s3U 12225 46 maskSlack c)| := bweaken (babs (sGlobal24_hz107 hc)) (by norm_num) (by norm_num)

theorem sGlobal24_hz115 {c : ℝ} (hc : B (93 / 200) (47 / 100) c) : B 0 (8161653860949444177 / 25000000000000000) |(s3L 12225 46 maskSlack c)| := bweaken (babs (sGlobal24_hz113 hc)) (by norm_num) (by norm_num)

theorem sGlobal24_hz116 {c : ℝ} (hc : B (93 / 200) (47 / 100) c) : B 0 (1635472472981850947157 / 1000000000000000000) (max |(s3U 12225 46 maskSlack c)| |(s3L 12225 46 maskSlack c)|) := bweaken (bmax (sGlobal24_hz114 hc) (sGlobal24_hz115 hc)) (by norm_num) (by norm_num)

theorem sGlobal24_hz117 {c : ℝ} (hc : B (93 / 200) (47 / 100) c) : B 0 (1635472472981850947157 / 1000000000000000000) (s3nks 12225 46 maskSlack c) := by
    convert (sGlobal24_hz116 hc) using 1 <;>
      norm_num [s3nks] <;> ring

theorem sGlobal24 {c : ℝ} (hc : B (93 / 200) (47 / 100) c) :
    0 < s3am 12225 46 ∧ 0 ≤ s3dm 12225 46 c ∧
    s3dm 12225 46 c ^ 2 ≤ 2 * s3ap 12225 46 ^ 2 ∧ s3c1 12225 46 c < 1 ∧
    0 ≤ s3Cpa 12225 c - s3r1 12225 46 ∧
    s3e0 12225 46 ≤ (s3Cpa 12225 c - s3r1 12225 46) / s3ap 12225 46 ∧
    s3nks 12225 46 maskSlack c ≤ 12225 * (133781 / 1000000) := by

  refine ⟨lt_of_lt_of_le (by norm_num) sGlobal24_hz14.1,
    le_trans (by norm_num) (sGlobal24_hz64 hc).1, ?_,
    lt_of_le_of_lt (sGlobal24_hz72 hc).2 (by norm_num), ?_, ?_,
    le_trans (sGlobal24_hz117 hc).2 (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (sGlobal24_hz64 hc).1) (sGlobal24_hz64 hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) sGlobal24_hz9.1 2
    nlinarith only [h1, h2]
  · linarith only [(sGlobal24_hz84 hc).1, sGlobal24_hz33.2]
  · have hap : 0 < s3ap 12225 46 := lt_of_lt_of_le (by norm_num) sGlobal24_hz9.1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul sGlobal24_hz16.2 sGlobal24_hz9.2 (le_trans (by norm_num) sGlobal24_hz9.1) (by norm_num)
    linarith only [h, (sGlobal24_hz84 hc).1, sGlobal24_hz33.2]

end BstLean.Part255
