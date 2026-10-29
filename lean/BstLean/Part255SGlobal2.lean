import BstLean.Part255Numeric52C
import BstLean.Part255Numeric10
namespace BstLean.Part255
open Real BstLean.Part130 BstLean.Part182 BstLean.Part197 BstLean.Part246
theorem sGlobal2_hz0 : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal2_hz1 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) ((√(23 : ℝ)) / (12225 : ℝ)) := bdiv sGlobal2_hz0 (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal2_hz2 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) maskSlack := by
    convert sGlobal2_hz1 using 1 <;>
      norm_num [maskSlack] <;> ring

theorem sGlobal2_hz3 : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal2_hz4 : B (6395294793910793 / 500000000000000000) (12790589587821587 / 1000000000000000000) (√((2 / 12225) : ℝ)) := bsqrt (bpoint ((2 / 12225) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal2_hz5 : B (7230130686979 / 62500000000000000) (23136418198333 / 200000000000000000) (√((2 / 149450625) : ℝ)) := bsqrt (bpoint ((2 / 149450625) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal2_hz6 : B (2211334438749598093 / 20000000000000000) (110566721937479904651 / 1000000000000000000) (√(12225 : ℝ)) := bsqrt (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal2_hz7 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))) := bmul sGlobal2_hz3 sGlobal2_hz4 (by norm_num) (by norm_num)

theorem sGlobal2_hz8 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) ((√(12225 : ℝ)) + ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := badd sGlobal2_hz6 sGlobal2_hz7 (by norm_num) (by norm_num)

theorem sGlobal2_hz9 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) (s3ap 12225 46) := by
    convert sGlobal2_hz8 using 1 <;>
      norm_num [s3ap, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal2_hz10 : B (163599182004089 / 1000000000000000000) (16359918200409 / 100000000000000000) ((2 : ℝ) / (12225 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal2_hz11 : B (1222499983640081799591 / 100000000000000000) (12224999836400817995911 / 1000000000000000000) ((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ))) := bsub (bpoint (12225 : ℝ)) sGlobal2_hz10 (by norm_num) (by norm_num)

theorem sGlobal2_hz12 : B (110566721197658827907 / 1000000000000000000) (27641680299414706977 / 250000000000000000) (√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) := bsqrt sGlobal2_hz11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal2_hz13 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) ((√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) - ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bsub sGlobal2_hz12 sGlobal2_hz7 (by norm_num) (by norm_num)

theorem sGlobal2_hz14 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) (s3am 12225 46) := by
    convert sGlobal2_hz13 using 1 <;>
      norm_num [s3am, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal2_hz15 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√((2 / 12225) : ℝ)) * (√(92 : ℝ))) := bmul sGlobal2_hz4 sGlobal2_hz3 (by norm_num) (by norm_num)

theorem sGlobal2_hz16 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) (s3e0 12225 46) := by
    convert sGlobal2_hz15 using 1 <;>
      norm_num [s3e0, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal2_hz17 : B (250196148528560847 / 500000000000000000) (100078459411424339 / 200000000000000000) (((1 / 2) : ℝ) + maskSlack) := badd (bpoint ((1 / 2) : ℝ)) sGlobal2_hz2 (by norm_num) (by norm_num)

theorem sGlobal2_hz18 : B (59827153232297998295487 / 800000000000000) (23930861292919199366019 / 320000000000000) ((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack)) := bmul (bpoint (149450625 : ℝ)) sGlobal2_hz17 (by norm_num) (by norm_num)

theorem sGlobal2_hz19 : B (1729554180017180009583 / 200000000000000000) (8647770900085900056557 / 1000000000000000000) (√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) := bsqrt sGlobal2_hz18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal2_hz20 : B (4328681281566262743499 / 500000000000000000) (8657362563132525495641 / 1000000000000000000) ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))) := badd sGlobal2_hz19 sGlobal2_hz3 (by norm_num) (by norm_num)

theorem sGlobal2_hz21 : B (110732771457999278473 / 1000000000000000000) (55366385728999643621 / 500000000000000000) ((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ)))) := bmul sGlobal2_hz4 sGlobal2_hz20 (by norm_num) (by norm_num)

theorem sGlobal2_hz22 : B (209099159 / 15625000000000000) (13382346177 / 1000000000000000000) ((2 : ℝ) / (149450625 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (149450625 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal2_hz23 : B (2452349334953899930479 / 200000000000000000) (12261746674769501594427 / 1000000000000000000) (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2) := bsq sGlobal2_hz21 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal2_hz24 : B (82045469362091 / 500000000000000000) (32818187747289 / 200000000000000000) (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2)) := bmul sGlobal2_hz22 sGlobal2_hz23 (by norm_num) (by norm_num)

theorem sGlobal2_hz25 : B (82045469362091 / 250000000000000000) (32818187747289 / 100000000000000000) ((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) := bmul (bpoint (2 : ℝ)) sGlobal2_hz24 (by norm_num) (by norm_num)

theorem sGlobal2_hz26 : B (117258080744995992792057 / 1000000000000000000) (58629040372497996396029 / 500000000000000000) (√(13749457500 : ℝ)) := bsqrt (bpoint (13749457500 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal2_hz27 : B (117304080744995992792057 / 1000000000000000000) (58652040372497996396029 / 500000000000000000) ((√(13749457500 : ℝ)) + (46 : ℝ)) := badd sGlobal2_hz26 (bpoint (46 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal2_hz28 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal2_hz25 sGlobal2_hz27 (by norm_num) (by norm_num)

theorem sGlobal2_hz29 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (s3rs 12225 46 maskSlack) := by
    convert sGlobal2_hz28 using 1 <;>
      norm_num [s3rs, s3pp, s3K, mA, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal2_hz30 : B (490797546012267 / 1000000000000000000) (49079754601227 / 100000000000000000) ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (3 : ℝ)) sGlobal2_hz10 (by norm_num) (by norm_num)

theorem sGlobal2_hz31 : B (490797546012267 / 500000000000000000) (49079754601227 / 50000000000000000) ((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal2_hz30 (by norm_num) (by norm_num)

theorem sGlobal2_hz32 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal2_hz31 sGlobal2_hz27 (by norm_num) (by norm_num)

theorem sGlobal2_hz33 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (s3r1 12225 46) := by
    convert sGlobal2_hz32 using 1 <;>
      norm_num [s3r1, mA] <;> ring

theorem sGlobal2_hz34 : B (163599182004089 / 500000000000000000) (16359918200409 / 50000000000000000) ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (2 : ℝ)) sGlobal2_hz10 (by norm_num) (by norm_num)

theorem sGlobal2_hz35 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal2_hz34 (by norm_num) (by norm_num)

theorem sGlobal2_hz36 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal2_hz35 sGlobal2_hz27 (by norm_num) (by norm_num)

theorem sGlobal2_hz37 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (s3rpp 12225 46) := by
    convert sGlobal2_hz36 using 1 <;>
      norm_num [s3rpp, mA] <;> ring

theorem sGlobal2_hz38 {c : ℝ} (hc : B (71 / 200) (9 / 25) c) : B (71 / 200) (9 / 25) c := hc

theorem sGlobal2_hz39 : B (153879783848994919 / 250000000000000000) (307759567862194061 / 500000000000000000) (kdot ((71 / 200))) := by
    constructor
    · apply bkdot_lower (q := (344969114613033683 / 500000000000000000)) (a := (150985282460730277 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (137987645845213473 / 200000000000000000)) (a := (60394112932705833 / 100000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal2_hz40 : B (5041 / 40000) (5041 / 40000) (((71 / 200) : ℝ)^2) := bsq (bpoint ((71 / 200) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal2_hz41 : B (34959 / 40000) (34959 / 40000) ((1 : ℝ) - (((71 / 200) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal2_hz40 (by norm_num) (by norm_num)

theorem sGlobal2_hz42 : B (934866300601321279 / 1000000000000000000) (2921457189379129 / 3125000000000000) (√((1 : ℝ) - (((71 / 200) : ℝ)^2))) := bsqrt sGlobal2_hz41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal2_hz43 : B (74394296435367003 / 250000000000000000) (148788592870734007 / 500000000000000000) ((√((1 : ℝ) - (((71 / 200) : ℝ)^2))) / Real.pi) := bdiv sGlobal2_hz42 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal2_hz44 : B (13656830816598299 / 62500000000000000) (27313661647769723 / 125000000000000000) (((71 / 200) : ℝ) * (kdot ((71 / 200)))) := bmul (bpoint ((71 / 200) : ℝ)) sGlobal2_hz39 (by norm_num) (by norm_num)

theorem sGlobal2_hz45 : B (129021619701760199 / 250000000000000000) (258043239461812899 / 500000000000000000) (((√((1 : ℝ) - (((71 / 200) : ℝ)^2))) / Real.pi) + (((71 / 200) : ℝ) * (kdot ((71 / 200))))) := badd sGlobal2_hz43 sGlobal2_hz44 (by norm_num) (by norm_num)

theorem sGlobal2_hz46 : B (129021619701760199 / 250000000000000000) (258043239461812899 / 500000000000000000) (kappa ((71 / 200))) := by rw [kappa_eq]; exact sGlobal2_hz45

theorem sGlobal2_hz47 : B (77152913900796081 / 125000000000000000) (617223311454350643 / 1000000000000000000) (kdot ((9 / 25))) := by
    constructor
    · apply bkdot_lower (q := (13719886811400707 / 20000000000000000)) (a := (120252843347949879 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (685994340570035349 / 1000000000000000000)) (a := (601264216350220189 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal2_hz48 : B (81 / 625) (81 / 625) (((9 / 25) : ℝ)^2) := bsq (bpoint ((9 / 25) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal2_hz49 : B (544 / 625) (544 / 625) ((1 : ℝ) - (((9 / 25) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal2_hz48 (by norm_num) (by norm_num)

theorem sGlobal2_hz50 : B (37318092127009923 / 40000000000000000) (233238075793812019 / 250000000000000000) (√((1 : ℝ) - (((9 / 25) : ℝ)^2))) := bsqrt sGlobal2_hz49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal2_hz51 : B (296967941438618583 / 1000000000000000000) (37120992679827323 / 125000000000000000) ((√((1 : ℝ) - (((9 / 25) : ℝ)^2))) / Real.pi) := bdiv sGlobal2_hz50 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal2_hz52 : B (222200392034292713 / 1000000000000000000) (27775049015445779 / 125000000000000000) (((9 / 25) : ℝ) * (kdot ((9 / 25)))) := bmul (bpoint ((9 / 25) : ℝ)) sGlobal2_hz47 (by norm_num) (by norm_num)

theorem sGlobal2_hz53 : B (8112005210514239 / 15625000000000000) (32448020847636551 / 62500000000000000) (((√((1 : ℝ) - (((9 / 25) : ℝ)^2))) / Real.pi) + (((9 / 25) : ℝ) * (kdot ((9 / 25))))) := badd sGlobal2_hz51 sGlobal2_hz52 (by norm_num) (by norm_num)

theorem sGlobal2_hz54 : B (8112005210514239 / 15625000000000000) (32448020847636551 / 62500000000000000) (kappa ((9 / 25))) := by rw [kappa_eq]; exact sGlobal2_hz53

theorem sGlobal2_hz55 {c : ℝ} (hc : B (71 / 200) (9 / 25) c) : B (129021619701760199 / 250000000000000000) (32448020847636551 / 62500000000000000) (kappa c) := bkappa (sGlobal2_hz38 hc) (by norm_num) (by norm_num) sGlobal2_hz46.1 sGlobal2_hz54.2

theorem sGlobal2_hz56 : B 24450 24450 ((2 : ℝ) * (12225 : ℝ)) := bmul (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal2_hz57 {c : ℝ} (hc : B (71 / 200) (9 / 25) c) : B (30051979152363449 / 62500000000000000) (120978380298239801 / 250000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (sGlobal2_hz55 hc) (by norm_num) (by norm_num)

theorem sGlobal2_hz58 {c : ℝ} (hc : B (71 / 200) (9 / 25) c) : B (14695417805505726561 / 1250000000000000) (59158427965839262689 / 5000000000000000) (((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) := bmul sGlobal2_hz56 (sGlobal2_hz57 hc) (by norm_num) (by norm_num)

theorem sGlobal2_hz59 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (4 : ℝ)) sGlobal2_hz10 (by norm_num) (by norm_num)

theorem sGlobal2_hz60 {c : ℝ} (hc : B (71 / 200) (9 / 25) c) : B (293908339750196330811 / 25000000000000000) (2957921234692781130361 / 250000000000000000) ((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bsub (sGlobal2_hz58 hc) sGlobal2_hz59 (by norm_num) (by norm_num)

theorem sGlobal2_hz61 {c : ℝ} (hc : B (71 / 200) (9 / 25) c) : B (54213313839885892997 / 500000000000000000) (4350941955718761279 / 40000000000000000) (√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) := bsqrt (sGlobal2_hz60 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal2_hz62 : B (30670756373515103 / 125000000000000000) (122683025494060423 / 500000000000000000) ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal2_hz7 (by norm_num) (by norm_num)

theorem sGlobal2_hz63 {c : ℝ} (hc : B (71 / 200) (9 / 25) c) : B (27045315407195916287 / 250000000000000000) (108528182841980911151 / 1000000000000000000) ((√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) - ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))))) := bsub (sGlobal2_hz61 hc) sGlobal2_hz62 (by norm_num) (by norm_num)

theorem sGlobal2_hz64 {c : ℝ} (hc : B (71 / 200) (9 / 25) c) : B (27045315407195916287 / 250000000000000000) (108528182841980911151 / 1000000000000000000) (s3dm 12225 46 c) := by
    convert (sGlobal2_hz63 hc) using 1 <;>
      norm_num [s3dm, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal2_hz65 : B (6126072185528622723889 / 500000000000000000) (2450428874211449090087 / 200000000000000000) ((s3ap 12225 46)^2) := bsq sGlobal2_hz9 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal2_hz66 : B (6126072185528622723889 / 250000000000000000) (2450428874211449090087 / 100000000000000000) ((2 : ℝ) * ((s3ap 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal2_hz65 (by norm_num) (by norm_num)

theorem sGlobal2_hz67 {c : ℝ} (hc : B (71 / 200) (9 / 25) c) : B (11703185367595340979193 / 1000000000000000000) (471134658839297593631 / 40000000000000000) ((s3dm 12225 46 c)^2) := bsq (sGlobal2_hz64 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal2_hz68 {c : ℝ} (hc : B (71 / 200) (9 / 25) c) : B (12725922271132051054781 / 1000000000000000000) (12801103374519149921677 / 1000000000000000000) (((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) := bsub sGlobal2_hz66 (sGlobal2_hz67 hc) (by norm_num) (by norm_num)

theorem sGlobal2_hz69 : B (1524735695971823534271 / 125000000000000000) (609894278388729413841 / 50000000000000000) ((s3am 12225 46)^2) := bsq sGlobal2_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal2_hz70 : B (1524735695971823534271 / 62500000000000000) (609894278388729413841 / 25000000000000000) ((2 : ℝ) * ((s3am 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal2_hz69 (by norm_num) (by norm_num)

theorem sGlobal2_hz71 {c : ℝ} (hc : B (71 / 200) (9 / 25) c) : B (65205574976619693 / 125000000000000000) (262363163340747223 / 500000000000000000) ((((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) / ((2 : ℝ) * ((s3am 12225 46)^2))) := bdiv (sGlobal2_hz68 hc) sGlobal2_hz70 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal2_hz72 {c : ℝ} (hc : B (71 / 200) (9 / 25) c) : B (65205574976619693 / 125000000000000000) (262363163340747223 / 500000000000000000) (s3c1 12225 46 c) := by
    convert (sGlobal2_hz71 hc) using 1 <;>
      norm_num [s3c1] <;> ring

theorem sGlobal2_hz73 {c : ℝ} (hc : B (71 / 200) (9 / 25) c) : B (153879783848994919 / 250000000000000000) (617223311454350643 / 1000000000000000000) (kdot c) := bkdot (sGlobal2_hz38 hc) sGlobal2_hz39.1 sGlobal2_hz47.2

theorem sGlobal2_hz74 : B (674681293279223531 / 1000000000000000000) (337340646639618089 / 500000000000000000) (kdot ((65205574976619693 / 125000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (280342363436144917 / 500000000000000000)) (a := (20440377182186477 / 40000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (560684726872289833 / 1000000000000000000)) (a := (25550471477732103 / 50000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal2_hz75 : B (675832341822307159 / 1000000000000000000) (84479042727789679 / 125000000000000000) (kdot ((262363163340747223 / 500000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (139577668056380597 / 250000000000000000)) (a := (101840273346244709 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (558310672225522387 / 1000000000000000000)) (a := (509201366731207409 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal2_hz76 {c : ℝ} (hc : B (71 / 200) (9 / 25) c) : B (674681293279223531 / 1000000000000000000) (84479042727789679 / 125000000000000000) (kdot (s3c1 12225 46 c)) := bkdot (sGlobal2_hz72 hc) sGlobal2_hz74.1 sGlobal2_hz75.2

theorem sGlobal2_hz77 {c : ℝ} (hc : B (71 / 200) (9 / 25) c) : B (5041 / 40000) (81 / 625) (c^2) := bsq (sGlobal2_hz38 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal2_hz78 {c : ℝ} (hc : B (71 / 200) (9 / 25) c) : B (544 / 625) (34959 / 40000) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (sGlobal2_hz77 hc) (by norm_num) (by norm_num)

theorem sGlobal2_hz79 {c : ℝ} (hc : B (71 / 200) (9 / 25) c) : B (37318092127009923 / 40000000000000000) (2921457189379129 / 3125000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (sGlobal2_hz78 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal2_hz80 : B (39119999999999765769 / 1600000000000000) (3912000000000000489 / 160000000000000) ((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (149450625 : ℝ)) sGlobal2_hz10 (by norm_num) (by norm_num)

theorem sGlobal2_hz81 {c : ℝ} (hc : B (71 / 200) (9 / 25) c) : B (574249995016116599 / 1000000000000000000) (577021273824225917 / 1000000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (sGlobal2_hz79 hc) (sGlobal2_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal2_hz82 {c : ℝ} (hc : B (71 / 200) (9 / 25) c) : B (702020618907198338929 / 50000000000000000) (3527042536250581358543 / 250000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) := bmul sGlobal2_hz80 (sGlobal2_hz81 hc) (by norm_num) (by norm_num)

theorem sGlobal2_hz83 {c : ℝ} (hc : B (71 / 200) (9 / 25) c) : B (702020618907198338929 / 100000000000000000) (3527042536250581358543 / 500000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) / (2 : ℝ)) := bdiv (sGlobal2_hz82 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal2_hz84 {c : ℝ} (hc : B (71 / 200) (9 / 25) c) : B (702020618907198338929 / 100000000000000000) (3527042536250581358543 / 500000000000000000) (s3Cpa 12225 c) := by
    convert (sGlobal2_hz83 hc) using 1 <;>
      norm_num [s3Cpa, mA] <;> ring

theorem sGlobal2_hz85 {c : ℝ} (hc : B (71 / 200) (9 / 25) c) : B (296967941438618583 / 1000000000000000000) (148788592870734007 / 500000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (sGlobal2_hz79 hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal2_hz86 {c : ℝ} (hc : B (71 / 200) (9 / 25) c) : B (13656830816598299 / 62500000000000000) (27775049015445779 / 125000000000000000) (c * (kdot c)) := bmul (sGlobal2_hz38 hc) (sGlobal2_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal2_hz87 {c : ℝ} (hc : B (71 / 200) (9 / 25) c) : B (74767549315052351 / 1000000000000000000) (7906789267589523 / 100000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (sGlobal2_hz85 hc) (sGlobal2_hz86 hc) (by norm_num) (by norm_num)

theorem sGlobal2_hz88 {c : ℝ} (hc : B (71 / 200) (9 / 25) c) : B (1828066580753019036401 / 1000000000000000000) (120825623495352413447 / 62500000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) := bmul sGlobal2_hz80 (sGlobal2_hz87 hc) (by norm_num) (by norm_num)

theorem sGlobal2_hz89 {c : ℝ} (hc : B (71 / 200) (9 / 25) c) : B (4570166451882547591 / 5000000000000000) (120825623495352413447 / 125000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) / (2 : ℝ)) := bdiv (sGlobal2_hz88 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal2_hz90 {c : ℝ} (hc : B (71 / 200) (9 / 25) c) : B (4570166451882547591 / 5000000000000000) (120825623495352413447 / 125000000000000000) (s3Cpp 12225 c) := by
    convert (sGlobal2_hz89 hc) using 1 <;>
      norm_num [s3Cpp, mA] <;> ring

theorem sGlobal2_hz91 {c : ℝ} (hc : B (71 / 200) (9 / 25) c) : B (7135351299005721097691 / 1000000000000000000) (224038443201090660291 / 31250000000000000) ((s3Cpa 12225 c) + (s3r1 12225 46)) := badd (sGlobal2_hz84 hc) sGlobal2_hz33 (by norm_num) (by norm_num)

theorem sGlobal2_hz92 {c : ℝ} (hc : B (71 / 200) (9 / 25) c) : B (12921206824913153309 / 200000000000000000) (64912785706542226131 / 1000000000000000000) (((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) := bdiv (sGlobal2_hz91 hc) sGlobal2_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal2_hz93 {c : ℝ} (hc : B (71 / 200) (9 / 25) c) : B (64728717150059826957 / 1000000000000000000) (32517734366018143277 / 500000000000000000) ((((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) + (s3e0 12225 46)) := badd (sGlobal2_hz92 hc) sGlobal2_hz16 (by norm_num) (by norm_num)

theorem sGlobal2_hz94 {c : ℝ} (hc : B (71 / 200) (9 / 25) c) : B (64728717150059826957 / 1000000000000000000) (32517734366018143277 / 500000000000000000) (s3Lam 12225 46 c) := by
    convert (sGlobal2_hz93 hc) using 1 <;>
      norm_num [s3Lam] <;> ring

theorem sGlobal2_hz95 {c : ℝ} (hc : B (71 / 200) (9 / 25) c) : B (4953983484995006619 / 5000000000000000) (521684197292655791197 / 500000000000000000) ((s3Cpp 12225 c) + (s3rpp 12225 46)) := badd (sGlobal2_hz90 hc) sGlobal2_hz37 (by norm_num) (by norm_num)

theorem sGlobal2_hz96 {c : ℝ} (hc : B (71 / 200) (9 / 25) c) : B (4953983484995006619 / 10000000000000000) (70514210549598286981 / 100000000000000000) (if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) := bweaken (bfirst (sGlobal2_hz95 hc) (sGlobal2_hz76 hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem sGlobal2_hz97 {c : ℝ} (hc : B (71 / 200) (9 / 25) c) : B (837961364778489833371 / 200000000000000000) (4229612193195669513921 / 1000000000000000000) ((s3Lam 12225 46 c)^2) := bsq (sGlobal2_hz94 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal2_hz98 {c : ℝ} (hc : B (71 / 200) (9 / 25) c) : B (435380941622433 / 1600000000000000) (275337717912654431 / 1000000000000000000) ((s3c1 12225 46 c)^2) := bsq (sGlobal2_hz72 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal2_hz99 {c : ℝ} (hc : B (71 / 200) (9 / 25) c) : B (724662282087345569 / 1000000000000000000) (1164619058377567 / 1600000000000000) ((1 : ℝ) - ((s3c1 12225 46 c)^2)) := bsub (bpoint (1 : ℝ)) (sGlobal2_hz98 hc) (by norm_num) (by norm_num)

theorem sGlobal2_hz100 {c : ℝ} (hc : B (71 / 200) (9 / 25) c) : B (425635490204748307 / 500000000000000000) (853162886842822867 / 1000000000000000000) (√((1 : ℝ) - ((s3c1 12225 46 c)^2))) := bsqrt (sGlobal2_hz99 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal2_hz101 {c : ℝ} (hc : B (71 / 200) (9 / 25) c) : B (1337173329134327681 / 500000000000000000) (2680290257620872387 / 1000000000000000000) (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))) := bmul pi_mem (sGlobal2_hz100 hc) (by norm_num) (by norm_num)

theorem sGlobal2_hz102 {c : ℝ} (hc : B (71 / 200) (9 / 25) c) : B (62527658144181460683 / 40000000000000000) (790774857126016178363 / 500000000000000000) (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2))))) := bdiv (sGlobal2_hz97 hc) (sGlobal2_hz101 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal2_hz103 {c : ℝ} (hc : B (71 / 200) (9 / 25) c) : B (82343592084161487159 / 40000000000000000) (285836477468501903317 / 125000000000000000) ((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) := badd (sGlobal2_hz96 hc) (sGlobal2_hz102 hc) (by norm_num) (by norm_num)

theorem sGlobal2_hz104 : B (3762781186094069 / 250000000000000000) (376278118609407 / 25000000000000000) ((s3e0 12225 46)^2) := bsq sGlobal2_hz16 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal2_hz105 {c : ℝ} (hc : B (71 / 200) (9 / 25) c) : B (2058604853228781555251 / 1000000000000000000) (17864897428693434397 / 7812500000000000) (((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) := badd (sGlobal2_hz103 hc) sGlobal2_hz104 (by norm_num) (by norm_num)

theorem sGlobal2_hz106 {c : ℝ} (hc : B (71 / 200) (9 / 25) c) : B (1048550963340014412691 / 500000000000000000) (36331311630107560513 / 15625000000000000) ((((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) + (s3rs 12225 46 maskSlack)) := badd (sGlobal2_hz105 hc) sGlobal2_hz29 (by norm_num) (by norm_num)

theorem sGlobal2_hz107 {c : ℝ} (hc : B (71 / 200) (9 / 25) c) : B (1048550963340014412691 / 500000000000000000) (36331311630107560513 / 15625000000000000) (s3U 12225 46 maskSlack c) := by
    convert (sGlobal2_hz106 hc) using 1 <;>
      norm_num [s3U] <;> ring

theorem sGlobal2_hz108 {c : ℝ} (hc : B (71 / 200) (9 / 25) c) : B (418634941877008621691 / 500000000000000000) (111230197667540937747 / 125000000000000000) ((s3Cpp 12225 c) - (s3rpp 12225 46)) := bsub (sGlobal2_hz90 hc) sGlobal2_hz37 (by norm_num) (by norm_num)

theorem sGlobal2_hz109 {c : ℝ} (hc : B (71 / 200) (9 / 25) c) : B 0 0 (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ)) := bweaken (bmin (sGlobal2_hz108 hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem sGlobal2_hz110 {c : ℝ} (hc : B (71 / 200) (9 / 25) c) : B 0 0 ((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) := bmul (sGlobal2_hz76 hc) (sGlobal2_hz109 hc) (by norm_num) (by norm_num)

theorem sGlobal2_hz111 {c : ℝ} (hc : B (71 / 200) (9 / 25) c) : B (-376278118609407 / 25000000000000000) (-3762781186094069 / 250000000000000000) (((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) := bsub (sGlobal2_hz110 hc) sGlobal2_hz104 (by norm_num) (by norm_num)

theorem sGlobal2_hz112 {c : ℝ} (hc : B (71 / 200) (9 / 25) c) : B (-4814015572358580787 / 125000000000000000) (-38512124575991646407 / 1000000000000000000) ((((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) - (s3rs 12225 46 maskSlack)) := bsub (sGlobal2_hz111 hc) sGlobal2_hz29 (by norm_num) (by norm_num)

theorem sGlobal2_hz113 {c : ℝ} (hc : B (71 / 200) (9 / 25) c) : B (-4814015572358580787 / 125000000000000000) (-38512124575991646407 / 1000000000000000000) (s3L 12225 46 maskSlack c) := by
    convert (sGlobal2_hz112 hc) using 1 <;>
      norm_num [s3L] <;> ring

theorem sGlobal2_hz114 {c : ℝ} (hc : B (71 / 200) (9 / 25) c) : B 0 (36331311630107560513 / 15625000000000000) |(s3U 12225 46 maskSlack c)| := bweaken (babs (sGlobal2_hz107 hc)) (by norm_num) (by norm_num)

theorem sGlobal2_hz115 {c : ℝ} (hc : B (71 / 200) (9 / 25) c) : B 0 (4814015572358580787 / 125000000000000000) |(s3L 12225 46 maskSlack c)| := bweaken (babs (sGlobal2_hz113 hc)) (by norm_num) (by norm_num)

theorem sGlobal2_hz116 {c : ℝ} (hc : B (71 / 200) (9 / 25) c) : B 0 (36331311630107560513 / 15625000000000000) (max |(s3U 12225 46 maskSlack c)| |(s3L 12225 46 maskSlack c)|) := bweaken (bmax (sGlobal2_hz114 hc) (sGlobal2_hz115 hc)) (by norm_num) (by norm_num)

theorem sGlobal2_hz117 {c : ℝ} (hc : B (71 / 200) (9 / 25) c) : B 0 (36331311630107560513 / 15625000000000000) (s3nks 12225 46 maskSlack c) := by
    convert (sGlobal2_hz116 hc) using 1 <;>
      norm_num [s3nks] <;> ring

theorem sGlobal2 {c : ℝ} (hc : B (71 / 200) (9 / 25) c) :
    0 < s3am 12225 46 ∧ 0 ≤ s3dm 12225 46 c ∧
    s3dm 12225 46 c ^ 2 ≤ 2 * s3ap 12225 46 ^ 2 ∧ s3c1 12225 46 c < 1 ∧
    0 ≤ s3Cpa 12225 c - s3r1 12225 46 ∧
    s3e0 12225 46 ≤ (s3Cpa 12225 c - s3r1 12225 46) / s3ap 12225 46 ∧
    s3nks 12225 46 maskSlack c ≤ 12225 * (190201 / 1000000) := by

  refine ⟨lt_of_lt_of_le (by norm_num) sGlobal2_hz14.1,
    le_trans (by norm_num) (sGlobal2_hz64 hc).1, ?_,
    lt_of_le_of_lt (sGlobal2_hz72 hc).2 (by norm_num), ?_, ?_,
    le_trans (sGlobal2_hz117 hc).2 (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (sGlobal2_hz64 hc).1) (sGlobal2_hz64 hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) sGlobal2_hz9.1 2
    nlinarith only [h1, h2]
  · linarith only [(sGlobal2_hz84 hc).1, sGlobal2_hz33.2]
  · have hap : 0 < s3ap 12225 46 := lt_of_lt_of_le (by norm_num) sGlobal2_hz9.1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul sGlobal2_hz16.2 sGlobal2_hz9.2 (le_trans (by norm_num) sGlobal2_hz9.1) (by norm_num)
    linarith only [h, (sGlobal2_hz84 hc).1, sGlobal2_hz33.2]

end BstLean.Part255
