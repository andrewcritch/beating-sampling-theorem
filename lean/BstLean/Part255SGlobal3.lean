import BstLean.Part255Numeric52W
import BstLean.Part255Numeric10
namespace BstLean.Part255
open Real BstLean.Part130 BstLean.Part182 BstLean.Part197 BstLean.Part246
theorem sGlobal3_hz0 : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal3_hz1 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) ((√(23 : ℝ)) / (12225 : ℝ)) := bdiv sGlobal3_hz0 (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal3_hz2 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) maskSlack := by
    convert sGlobal3_hz1 using 1 <;>
      norm_num [maskSlack] <;> ring

theorem sGlobal3_hz3 : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal3_hz4 : B (6395294793910793 / 500000000000000000) (12790589587821587 / 1000000000000000000) (√((2 / 12225) : ℝ)) := bsqrt (bpoint ((2 / 12225) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal3_hz5 : B (7230130686979 / 62500000000000000) (23136418198333 / 200000000000000000) (√((2 / 149450625) : ℝ)) := bsqrt (bpoint ((2 / 149450625) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal3_hz6 : B (2211334438749598093 / 20000000000000000) (110566721937479904651 / 1000000000000000000) (√(12225 : ℝ)) := bsqrt (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal3_hz7 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))) := bmul sGlobal3_hz3 sGlobal3_hz4 (by norm_num) (by norm_num)

theorem sGlobal3_hz8 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) ((√(12225 : ℝ)) + ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := badd sGlobal3_hz6 sGlobal3_hz7 (by norm_num) (by norm_num)

theorem sGlobal3_hz9 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) (s3ap 12225 46) := by
    convert sGlobal3_hz8 using 1 <;>
      norm_num [s3ap, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal3_hz10 : B (163599182004089 / 1000000000000000000) (16359918200409 / 100000000000000000) ((2 : ℝ) / (12225 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal3_hz11 : B (1222499983640081799591 / 100000000000000000) (12224999836400817995911 / 1000000000000000000) ((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ))) := bsub (bpoint (12225 : ℝ)) sGlobal3_hz10 (by norm_num) (by norm_num)

theorem sGlobal3_hz12 : B (110566721197658827907 / 1000000000000000000) (27641680299414706977 / 250000000000000000) (√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) := bsqrt sGlobal3_hz11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal3_hz13 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) ((√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) - ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bsub sGlobal3_hz12 sGlobal3_hz7 (by norm_num) (by norm_num)

theorem sGlobal3_hz14 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) (s3am 12225 46) := by
    convert sGlobal3_hz13 using 1 <;>
      norm_num [s3am, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal3_hz15 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√((2 / 12225) : ℝ)) * (√(92 : ℝ))) := bmul sGlobal3_hz4 sGlobal3_hz3 (by norm_num) (by norm_num)

theorem sGlobal3_hz16 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) (s3e0 12225 46) := by
    convert sGlobal3_hz15 using 1 <;>
      norm_num [s3e0, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal3_hz17 : B (250196148528560847 / 500000000000000000) (100078459411424339 / 200000000000000000) (((1 / 2) : ℝ) + maskSlack) := badd (bpoint ((1 / 2) : ℝ)) sGlobal3_hz2 (by norm_num) (by norm_num)

theorem sGlobal3_hz18 : B (59827153232297998295487 / 800000000000000) (23930861292919199366019 / 320000000000000) ((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack)) := bmul (bpoint (149450625 : ℝ)) sGlobal3_hz17 (by norm_num) (by norm_num)

theorem sGlobal3_hz19 : B (1729554180017180009583 / 200000000000000000) (8647770900085900056557 / 1000000000000000000) (√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) := bsqrt sGlobal3_hz18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal3_hz20 : B (4328681281566262743499 / 500000000000000000) (8657362563132525495641 / 1000000000000000000) ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))) := badd sGlobal3_hz19 sGlobal3_hz3 (by norm_num) (by norm_num)

theorem sGlobal3_hz21 : B (110732771457999278473 / 1000000000000000000) (55366385728999643621 / 500000000000000000) ((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ)))) := bmul sGlobal3_hz4 sGlobal3_hz20 (by norm_num) (by norm_num)

theorem sGlobal3_hz22 : B (209099159 / 15625000000000000) (13382346177 / 1000000000000000000) ((2 : ℝ) / (149450625 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (149450625 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal3_hz23 : B (2452349334953899930479 / 200000000000000000) (12261746674769501594427 / 1000000000000000000) (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2) := bsq sGlobal3_hz21 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal3_hz24 : B (82045469362091 / 500000000000000000) (32818187747289 / 200000000000000000) (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2)) := bmul sGlobal3_hz22 sGlobal3_hz23 (by norm_num) (by norm_num)

theorem sGlobal3_hz25 : B (82045469362091 / 250000000000000000) (32818187747289 / 100000000000000000) ((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) := bmul (bpoint (2 : ℝ)) sGlobal3_hz24 (by norm_num) (by norm_num)

theorem sGlobal3_hz26 : B (117258080744995992792057 / 1000000000000000000) (58629040372497996396029 / 500000000000000000) (√(13749457500 : ℝ)) := bsqrt (bpoint (13749457500 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal3_hz27 : B (117304080744995992792057 / 1000000000000000000) (58652040372497996396029 / 500000000000000000) ((√(13749457500 : ℝ)) + (46 : ℝ)) := badd sGlobal3_hz26 (bpoint (46 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal3_hz28 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal3_hz25 sGlobal3_hz27 (by norm_num) (by norm_num)

theorem sGlobal3_hz29 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (s3rs 12225 46 maskSlack) := by
    convert sGlobal3_hz28 using 1 <;>
      norm_num [s3rs, s3pp, s3K, mA, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal3_hz30 : B (490797546012267 / 1000000000000000000) (49079754601227 / 100000000000000000) ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (3 : ℝ)) sGlobal3_hz10 (by norm_num) (by norm_num)

theorem sGlobal3_hz31 : B (490797546012267 / 500000000000000000) (49079754601227 / 50000000000000000) ((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal3_hz30 (by norm_num) (by norm_num)

theorem sGlobal3_hz32 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal3_hz31 sGlobal3_hz27 (by norm_num) (by norm_num)

theorem sGlobal3_hz33 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (s3r1 12225 46) := by
    convert sGlobal3_hz32 using 1 <;>
      norm_num [s3r1, mA] <;> ring

theorem sGlobal3_hz34 : B (163599182004089 / 500000000000000000) (16359918200409 / 50000000000000000) ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (2 : ℝ)) sGlobal3_hz10 (by norm_num) (by norm_num)

theorem sGlobal3_hz35 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal3_hz34 (by norm_num) (by norm_num)

theorem sGlobal3_hz36 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal3_hz35 sGlobal3_hz27 (by norm_num) (by norm_num)

theorem sGlobal3_hz37 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (s3rpp 12225 46) := by
    convert sGlobal3_hz36 using 1 <;>
      norm_num [s3rpp, mA] <;> ring

theorem sGlobal3_hz38 {c : ℝ} (hc : B (9 / 25) (73 / 200) c) : B (9 / 25) (73 / 200) c := hc

theorem sGlobal3_hz39 : B (77152913900796081 / 125000000000000000) (617223311454350643 / 1000000000000000000) (kdot ((9 / 25))) := by
    constructor
    · apply bkdot_lower (q := (13719886811400707 / 20000000000000000)) (a := (120252843347949879 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (685994340570035349 / 1000000000000000000)) (a := (601264216350220189 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal3_hz40 : B (81 / 625) (81 / 625) (((9 / 25) : ℝ)^2) := bsq (bpoint ((9 / 25) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal3_hz41 : B (544 / 625) (544 / 625) ((1 : ℝ) - (((9 / 25) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal3_hz40 (by norm_num) (by norm_num)

theorem sGlobal3_hz42 : B (37318092127009923 / 40000000000000000) (233238075793812019 / 250000000000000000) (√((1 : ℝ) - (((9 / 25) : ℝ)^2))) := bsqrt sGlobal3_hz41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal3_hz43 : B (296967941438618583 / 1000000000000000000) (37120992679827323 / 125000000000000000) ((√((1 : ℝ) - (((9 / 25) : ℝ)^2))) / Real.pi) := bdiv sGlobal3_hz42 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal3_hz44 : B (222200392034292713 / 1000000000000000000) (27775049015445779 / 125000000000000000) (((9 / 25) : ℝ) * (kdot ((9 / 25)))) := bmul (bpoint ((9 / 25) : ℝ)) sGlobal3_hz39 (by norm_num) (by norm_num)

theorem sGlobal3_hz45 : B (8112005210514239 / 15625000000000000) (32448020847636551 / 62500000000000000) (((√((1 : ℝ) - (((9 / 25) : ℝ)^2))) / Real.pi) + (((9 / 25) : ℝ) * (kdot ((9 / 25))))) := badd sGlobal3_hz43 sGlobal3_hz44 (by norm_num) (by norm_num)

theorem sGlobal3_hz46 : B (8112005210514239 / 15625000000000000) (32448020847636551 / 62500000000000000) (kappa ((9 / 25))) := by rw [kappa_eq]; exact sGlobal3_hz45

theorem sGlobal3_hz47 : B (618931014992546163 / 1000000000000000000) (309465507589790037 / 500000000000000000) (kdot ((73 / 200))) := by
    constructor
    · apply bkdot_lower (q := (682056790305224659 / 1000000000000000000)) (a := (598581761905168017 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (341028395152612329 / 500000000000000000)) (a := (299290880805687919 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal3_hz48 : B (5329 / 40000) (5329 / 40000) (((73 / 200) : ℝ)^2) := bsq (bpoint ((73 / 200) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal3_hz49 : B (34671 / 40000) (34671 / 40000) ((1 : ℝ) - (((73 / 200) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal3_hz48 (by norm_num) (by norm_num)

theorem sGlobal3_hz50 : B (465503759383315829 / 500000000000000000) (931007518766631659 / 1000000000000000000) (√((1 : ℝ) - (((73 / 200) : ℝ)^2))) := bsqrt sGlobal3_hz49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal3_hz51 : B (7408722433371497 / 25000000000000000) (148174448667429941 / 500000000000000000) ((√((1 : ℝ) - (((73 / 200) : ℝ)^2))) / Real.pi) := bdiv sGlobal3_hz50 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal3_hz52 : B (225909820472279349 / 1000000000000000000) (28238727567568341 / 125000000000000000) (((73 / 200) : ℝ) * (kdot ((73 / 200)))) := bmul (bpoint ((73 / 200) : ℝ)) sGlobal3_hz47 (by norm_num) (by norm_num)

theorem sGlobal3_hz53 : B (522258717807139229 / 1000000000000000000) (52225871787540661 / 100000000000000000) (((√((1 : ℝ) - (((73 / 200) : ℝ)^2))) / Real.pi) + (((73 / 200) : ℝ) * (kdot ((73 / 200))))) := badd sGlobal3_hz51 sGlobal3_hz52 (by norm_num) (by norm_num)

theorem sGlobal3_hz54 : B (522258717807139229 / 1000000000000000000) (52225871787540661 / 100000000000000000) (kappa ((73 / 200))) := by rw [kappa_eq]; exact sGlobal3_hz53

theorem sGlobal3_hz55 {c : ℝ} (hc : B (9 / 25) (73 / 200) c) : B (8112005210514239 / 15625000000000000) (52225871787540661 / 100000000000000000) (kappa c) := bkappa (sGlobal3_hz38 hc) (by norm_num) (by norm_num) sGlobal3_hz46.1 sGlobal3_hz54.2

theorem sGlobal3_hz56 : B 24450 24450 ((2 : ℝ) * (12225 : ℝ)) := bmul (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal3_hz57 {c : ℝ} (hc : B (9 / 25) (73 / 200) c) : B (47774128212459339 / 100000000000000000) (7512994789485761 / 15625000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (sGlobal3_hz55 hc) (by norm_num) (by norm_num)

theorem sGlobal3_hz58 {c : ℝ} (hc : B (9 / 25) (73 / 200) c) : B (23361548695892616771 / 2000000000000000) (3673854452058537129 / 312500000000000) (((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) := bmul sGlobal3_hz56 (sGlobal3_hz57 hc) (by norm_num) (by norm_num)

theorem sGlobal3_hz59 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (4 : ℝ)) sGlobal3_hz10 (by norm_num) (by norm_num)

theorem sGlobal3_hz60 {c : ℝ} (hc : B (9 / 25) (73 / 200) c) : B (584038684677479018457 / 50000000000000000) (2939083398047647699111 / 250000000000000000) ((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bsub (sGlobal3_hz58 hc) sGlobal3_hz59 (by norm_num) (by norm_num)

theorem sGlobal3_hz61 {c : ℝ} (hc : B (9 / 25) (73 / 200) c) : B (108077628089950143803 / 1000000000000000000) (10842662768983729117 / 100000000000000000) (√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) := bsqrt (sGlobal3_hz60 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal3_hz62 : B (30670756373515103 / 125000000000000000) (122683025494060423 / 500000000000000000) ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal3_hz7 (by norm_num) (by norm_num)

theorem sGlobal3_hz63 {c : ℝ} (hc : B (9 / 25) (73 / 200) c) : B (107832262038962022957 / 1000000000000000000) (54090630819424585173 / 500000000000000000) ((√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) - ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))))) := bsub (sGlobal3_hz61 hc) sGlobal3_hz62 (by norm_num) (by norm_num)

theorem sGlobal3_hz64 {c : ℝ} (hc : B (9 / 25) (73 / 200) c) : B (107832262038962022957 / 1000000000000000000) (54090630819424585173 / 500000000000000000) (s3dm 12225 46 c) := by
    convert (sGlobal3_hz63 hc) using 1 <;>
      norm_num [s3dm, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal3_hz65 : B (6126072185528622723889 / 500000000000000000) (2450428874211449090087 / 200000000000000000) ((s3ap 12225 46)^2) := bsq sGlobal3_hz9 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal3_hz66 : B (6126072185528622723889 / 250000000000000000) (2450428874211449090087 / 100000000000000000) ((2 : ℝ) * ((s3ap 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal3_hz65 (by norm_num) (by norm_num)

theorem sGlobal3_hz67 {c : ℝ} (hc : B (9 / 25) (73 / 200) c) : B (1453474592054921267077 / 125000000000000000) (11703185369773139081797 / 1000000000000000000) ((s3dm 12225 46 c)^2) := bsq (sGlobal3_hz64 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal3_hz68 {c : ℝ} (hc : B (9 / 25) (73 / 200) c) : B (12801103372341351813759 / 1000000000000000000) (6438246002837560382127 / 500000000000000000) (((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) := bsub sGlobal3_hz66 (sGlobal3_hz67 hc) (by norm_num) (by norm_num)

theorem sGlobal3_hz69 : B (1524735695971823534271 / 125000000000000000) (609894278388729413841 / 50000000000000000) ((s3am 12225 46)^2) := bsq sGlobal3_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal3_hz70 : B (1524735695971823534271 / 62500000000000000) (609894278388729413841 / 25000000000000000) ((2 : ℝ) * ((s3am 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal3_hz69 (by norm_num) (by norm_num)

theorem sGlobal3_hz71 {c : ℝ} (hc : B (9 / 25) (73 / 200) c) : B (65590790824028119 / 125000000000000000) (527816560260793589 / 1000000000000000000) ((((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) / ((2 : ℝ) * ((s3am 12225 46)^2))) := bdiv (sGlobal3_hz68 hc) sGlobal3_hz70 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal3_hz72 {c : ℝ} (hc : B (9 / 25) (73 / 200) c) : B (65590790824028119 / 125000000000000000) (527816560260793589 / 1000000000000000000) (s3c1 12225 46 c) := by
    convert (sGlobal3_hz71 hc) using 1 <;>
      norm_num [s3c1] <;> ring

theorem sGlobal3_hz73 {c : ℝ} (hc : B (9 / 25) (73 / 200) c) : B (77152913900796081 / 125000000000000000) (309465507589790037 / 500000000000000000) (kdot c) := bkdot (sGlobal3_hz38 hc) sGlobal3_hz39.1 sGlobal3_hz47.2

theorem sGlobal3_hz74 : B (675832341788927233 / 1000000000000000000) (337916170894468753 / 500000000000000000) (kdot ((65590790824028119 / 125000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (279155336147149703 / 500000000000000000)) (a := (50920136678365661 / 100000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (111662134458859881 / 200000000000000000)) (a := (254600683391820237 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal3_hz75 : B (676989149804114171 / 1000000000000000000) (84623643725515313 / 125000000000000000) (kdot ((527816560260793589 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (138982390700065581 / 250000000000000000)) (a := (63423032125324259 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (555929562800262323 / 1000000000000000000)) (a := (63423032125322623 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal3_hz76 {c : ℝ} (hc : B (9 / 25) (73 / 200) c) : B (675832341788927233 / 1000000000000000000) (84623643725515313 / 125000000000000000) (kdot (s3c1 12225 46 c)) := bkdot (sGlobal3_hz72 hc) sGlobal3_hz74.1 sGlobal3_hz75.2

theorem sGlobal3_hz77 {c : ℝ} (hc : B (9 / 25) (73 / 200) c) : B (81 / 625) (5329 / 40000) (c^2) := bsq (sGlobal3_hz38 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal3_hz78 {c : ℝ} (hc : B (9 / 25) (73 / 200) c) : B (34671 / 40000) (544 / 625) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (sGlobal3_hz77 hc) (by norm_num) (by norm_num)

theorem sGlobal3_hz79 {c : ℝ} (hc : B (9 / 25) (73 / 200) c) : B (465503759383315829 / 500000000000000000) (233238075793812019 / 250000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (sGlobal3_hz78 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal3_hz80 : B (39119999999999765769 / 1600000000000000) (3912000000000000489 / 160000000000000) ((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (149450625 : ℝ)) sGlobal3_hz10 (by norm_num) (by norm_num)

theorem sGlobal3_hz81 {c : ℝ} (hc : B (9 / 25) (73 / 200) c) : B (574639543491165791 / 1000000000000000000) (577433116118383659 / 1000000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (sGlobal3_hz79 hc) (sGlobal3_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal3_hz82 {c : ℝ} (hc : B (9 / 25) (73 / 200) c) : B (14049936838358919465953 / 1000000000000000000) (1411823968909448222733 / 100000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) := bmul sGlobal3_hz80 (sGlobal3_hz81 hc) (by norm_num) (by norm_num)

theorem sGlobal3_hz83 {c : ℝ} (hc : B (9 / 25) (73 / 200) c) : B (439060526198716233311 / 62500000000000000) (1411823968909448222733 / 200000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) / (2 : ℝ)) := bdiv (sGlobal3_hz82 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal3_hz84 {c : ℝ} (hc : B (9 / 25) (73 / 200) c) : B (439060526198716233311 / 62500000000000000) (1411823968909448222733 / 200000000000000000) (s3Cpa 12225 c) := by
    convert (sGlobal3_hz83 hc) using 1 <;>
      norm_num [s3Cpa, mA] <;> ring

theorem sGlobal3_hz85 {c : ℝ} (hc : B (9 / 25) (73 / 200) c) : B (7408722433371497 / 25000000000000000) (37120992679827323 / 125000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (sGlobal3_hz79 hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal3_hz86 {c : ℝ} (hc : B (9 / 25) (73 / 200) c) : B (222200392034292713 / 1000000000000000000) (28238727567568341 / 125000000000000000) (c * (kdot c)) := bmul (sGlobal3_hz38 hc) (sGlobal3_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal3_hz87 {c : ℝ} (hc : B (9 / 25) (73 / 200) c) : B (1100610574911143 / 15625000000000000) (74767549404325871 / 1000000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (sGlobal3_hz85 hc) (sGlobal3_hz86 hc) (by norm_num) (by norm_num)

theorem sGlobal3_hz88 {c : ℝ} (hc : B (9 / 25) (73 / 200) c) : B (344447085524189250903 / 200000000000000000) (1828066582935767774459 / 1000000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) := bmul sGlobal3_hz80 (sGlobal3_hz87 hc) (by norm_num) (by norm_num)

theorem sGlobal3_hz89 {c : ℝ} (hc : B (9 / 25) (73 / 200) c) : B (861117713810473127257 / 1000000000000000000) (91403329146788388723 / 100000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) / (2 : ℝ)) := bdiv (sGlobal3_hz88 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal3_hz90 {c : ℝ} (hc : B (9 / 25) (73 / 200) c) : B (861117713810473127257 / 1000000000000000000) (91403329146788388723 / 100000000000000000) (s3Cpp 12225 c) := by
    convert (sGlobal3_hz89 hc) using 1 <;>
      norm_num [s3Cpp, mA] <;> ring

theorem sGlobal3_hz91 {c : ℝ} (hc : B (9 / 25) (73 / 200) c) : B (7140113529113197441377 / 1000000000000000000) (7174264954480979525891 / 1000000000000000000) ((s3Cpa 12225 c) + (s3r1 12225 46)) := badd (sGlobal3_hz84 hc) sGlobal3_hz33 (by norm_num) (by norm_num)

theorem sGlobal3_hz92 {c : ℝ} (hc : B (9 / 25) (73 / 200) c) : B (64649153066849032039 / 1000000000000000000) (6495837234145166311 / 100000000000000000) (((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) := bdiv (sGlobal3_hz91 hc) sGlobal3_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal3_hz93 {c : ℝ} (hc : B (9 / 25) (73 / 200) c) : B (64771836092343092451 / 1000000000000000000) (65081055366945723533 / 1000000000000000000) ((((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) + (s3e0 12225 46)) := badd (sGlobal3_hz92 hc) sGlobal3_hz16 (by norm_num) (by norm_num)

theorem sGlobal3_hz94 {c : ℝ} (hc : B (9 / 25) (73 / 200) c) : B (64771836092343092451 / 1000000000000000000) (65081055366945723533 / 1000000000000000000) (s3Lam 12225 46 c) := by
    convert (sGlobal3_hz93 hc) using 1 <;>
      norm_num [s3Lam] <;> ring

theorem sGlobal3_hz95 {c : ℝ} (hc : B (9 / 25) (73 / 200) c) : B (937881120432964932857 / 1000000000000000000) (3870299601915531883 / 3906250000000000) ((s3Cpp 12225 c) + (s3rpp 12225 46)) := badd (sGlobal3_hz90 hc) sGlobal3_hz37 (by norm_num) (by norm_num)

theorem sGlobal3_hz96 {c : ℝ} (hc : B (9 / 25) (73 / 200) c) : B (117235140054120616607 / 250000000000000000) (670758614268935604859 / 1000000000000000000) (if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) := bweaken (bfirst (sGlobal3_hz95 hc) (sGlobal3_hz76 hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem sGlobal3_hz97 {c : ℝ} (hc : B (9 / 25) (73 / 200) c) : B (839078150154671857693 / 200000000000000000) (2117771883837727382591 / 500000000000000000) ((s3Lam 12225 46 c)^2) := bsq (sGlobal3_hz94 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal3_hz98 {c : ℝ} (hc : B (9 / 25) (73 / 200) c) : B (137668858909485161 / 500000000000000000) (278590321285535951 / 1000000000000000000) ((s3c1 12225 46 c)^2) := bsq (sGlobal3_hz72 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal3_hz99 {c : ℝ} (hc : B (9 / 25) (73 / 200) c) : B (721409678714464049 / 1000000000000000000) (362331141090514839 / 500000000000000000) ((1 : ℝ) - ((s3c1 12225 46 c)^2)) := bsub (bpoint (1 : ℝ)) (sGlobal3_hz98 hc) (by norm_num) (by norm_num)

theorem sGlobal3_hz100 {c : ℝ} (hc : B (9 / 25) (73 / 200) c) : B (424679196192391807 / 500000000000000000) (212817745116130659 / 250000000000000000) (√((1 : ℝ) - ((s3c1 12225 46 c)^2))) := bsqrt (sGlobal3_hz99 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal3_hz101 {c : ℝ} (hc : B (9 / 25) (73 / 200) c) : B (2668338085780873187 / 1000000000000000000) (2674346658441524709 / 1000000000000000000) (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))) := bmul pi_mem (sGlobal3_hz100 hc) (by norm_num) (by norm_num)

theorem sGlobal3_hz102 {c : ℝ} (hc : B (9 / 25) (73 / 200) c) : B (392188381555798650347 / 250000000000000000) (1587334000232563560471 / 1000000000000000000) (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2))))) := bdiv (sGlobal3_hz97 hc) (sGlobal3_hz101 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal3_hz103 {c : ℝ} (hc : B (9 / 25) (73 / 200) c) : B (254711760804959633477 / 125000000000000000) (225809261450149916533 / 100000000000000000) ((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) := badd (sGlobal3_hz96 hc) (sGlobal3_hz102 hc) (by norm_num) (by norm_num)

theorem sGlobal3_hz104 : B (3762781186094069 / 250000000000000000) (376278118609407 / 25000000000000000) ((s3e0 12225 46)^2) := bsq sGlobal3_hz16 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal3_hz105 {c : ℝ} (hc : B (9 / 25) (73 / 200) c) : B (509427284391105361023 / 250000000000000000) (225810766562624354161 / 100000000000000000) (((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) := badd (sGlobal3_hz103 hc) sGlobal3_hz104 (by norm_num) (by norm_num)

theorem sGlobal3_hz106 {c : ℝ} (hc : B (9 / 25) (73 / 200) c) : B (2076206211015668714223 / 1000000000000000000) (1148302369540183905813 / 500000000000000000) ((((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) + (s3rs 12225 46 maskSlack)) := badd (sGlobal3_hz105 hc) sGlobal3_hz29 (by norm_num) (by norm_num)

theorem sGlobal3_hz107 {c : ℝ} (hc : B (9 / 25) (73 / 200) c) : B (2076206211015668714223 / 1000000000000000000) (1148302369540183905813 / 500000000000000000) (s3U 12225 46 maskSlack c) := by
    convert (sGlobal3_hz106 hc) using 1 <;>
      norm_num [s3U] <;> ring

theorem sGlobal3_hz108 {c : ℝ} (hc : B (9 / 25) (73 / 200) c) : B (784354307187980852439 / 1000000000000000000) (83726988484539208163 / 100000000000000000) ((s3Cpp 12225 c) - (s3rpp 12225 46)) := bsub (sGlobal3_hz90 hc) sGlobal3_hz37 (by norm_num) (by norm_num)

theorem sGlobal3_hz109 {c : ℝ} (hc : B (9 / 25) (73 / 200) c) : B 0 0 (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ)) := bweaken (bmin (sGlobal3_hz108 hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem sGlobal3_hz110 {c : ℝ} (hc : B (9 / 25) (73 / 200) c) : B 0 0 ((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) := bmul (sGlobal3_hz76 hc) (sGlobal3_hz109 hc) (by norm_num) (by norm_num)

theorem sGlobal3_hz111 {c : ℝ} (hc : B (9 / 25) (73 / 200) c) : B (-376278118609407 / 25000000000000000) (-3762781186094069 / 250000000000000000) (((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) := bsub (sGlobal3_hz110 hc) sGlobal3_hz104 (by norm_num) (by norm_num)

theorem sGlobal3_hz112 {c : ℝ} (hc : B (9 / 25) (73 / 200) c) : B (-4814015572358580787 / 125000000000000000) (-38512124575991646407 / 1000000000000000000) ((((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) - (s3rs 12225 46 maskSlack)) := bsub (sGlobal3_hz111 hc) sGlobal3_hz29 (by norm_num) (by norm_num)

theorem sGlobal3_hz113 {c : ℝ} (hc : B (9 / 25) (73 / 200) c) : B (-4814015572358580787 / 125000000000000000) (-38512124575991646407 / 1000000000000000000) (s3L 12225 46 maskSlack c) := by
    convert (sGlobal3_hz112 hc) using 1 <;>
      norm_num [s3L] <;> ring

theorem sGlobal3_hz114 {c : ℝ} (hc : B (9 / 25) (73 / 200) c) : B 0 (1148302369540183905813 / 500000000000000000) |(s3U 12225 46 maskSlack c)| := bweaken (babs (sGlobal3_hz107 hc)) (by norm_num) (by norm_num)

theorem sGlobal3_hz115 {c : ℝ} (hc : B (9 / 25) (73 / 200) c) : B 0 (4814015572358580787 / 125000000000000000) |(s3L 12225 46 maskSlack c)| := bweaken (babs (sGlobal3_hz113 hc)) (by norm_num) (by norm_num)

theorem sGlobal3_hz116 {c : ℝ} (hc : B (9 / 25) (73 / 200) c) : B 0 (1148302369540183905813 / 500000000000000000) (max |(s3U 12225 46 maskSlack c)| |(s3L 12225 46 maskSlack c)|) := bweaken (bmax (sGlobal3_hz114 hc) (sGlobal3_hz115 hc)) (by norm_num) (by norm_num)

theorem sGlobal3_hz117 {c : ℝ} (hc : B (9 / 25) (73 / 200) c) : B 0 (1148302369540183905813 / 500000000000000000) (s3nks 12225 46 maskSlack c) := by
    convert (sGlobal3_hz116 hc) using 1 <;>
      norm_num [s3nks] <;> ring

theorem sGlobal3 {c : ℝ} (hc : B (9 / 25) (73 / 200) c) :
    0 < s3am 12225 46 ∧ 0 ≤ s3dm 12225 46 c ∧
    s3dm 12225 46 c ^ 2 ≤ 2 * s3ap 12225 46 ^ 2 ∧ s3c1 12225 46 c < 1 ∧
    0 ≤ s3Cpa 12225 c - s3r1 12225 46 ∧
    s3e0 12225 46 ≤ (s3Cpa 12225 c - s3r1 12225 46) / s3ap 12225 46 ∧
    s3nks 12225 46 maskSlack c ≤ 12225 * (93931 / 500000) := by

  refine ⟨lt_of_lt_of_le (by norm_num) sGlobal3_hz14.1,
    le_trans (by norm_num) (sGlobal3_hz64 hc).1, ?_,
    lt_of_le_of_lt (sGlobal3_hz72 hc).2 (by norm_num), ?_, ?_,
    le_trans (sGlobal3_hz117 hc).2 (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (sGlobal3_hz64 hc).1) (sGlobal3_hz64 hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) sGlobal3_hz9.1 2
    nlinarith only [h1, h2]
  · linarith only [(sGlobal3_hz84 hc).1, sGlobal3_hz33.2]
  · have hap : 0 < s3ap 12225 46 := lt_of_lt_of_le (by norm_num) sGlobal3_hz9.1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul sGlobal3_hz16.2 sGlobal3_hz9.2 (le_trans (by norm_num) sGlobal3_hz9.1) (by norm_num)
    linarith only [h, (sGlobal3_hz84 hc).1, sGlobal3_hz33.2]

end BstLean.Part255
