import BstLean.Part255SGlobal58
import BstLean.Part255Numeric10
namespace BstLean.Part255
open Real BstLean.Part130 BstLean.Part182 BstLean.Part197 BstLean.Part246
theorem sGlobal62_hz0 : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal62_hz1 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) ((√(23 : ℝ)) / (12225 : ℝ)) := bdiv sGlobal62_hz0 (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal62_hz2 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) maskSlack := by
    convert sGlobal62_hz1 using 1 <;>
      norm_num [maskSlack] <;> ring

theorem sGlobal62_hz3 : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal62_hz4 : B (6395294793910793 / 500000000000000000) (12790589587821587 / 1000000000000000000) (√((2 / 12225) : ℝ)) := bsqrt (bpoint ((2 / 12225) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal62_hz5 : B (7230130686979 / 62500000000000000) (23136418198333 / 200000000000000000) (√((2 / 149450625) : ℝ)) := bsqrt (bpoint ((2 / 149450625) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal62_hz6 : B (2211334438749598093 / 20000000000000000) (110566721937479904651 / 1000000000000000000) (√(12225 : ℝ)) := bsqrt (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal62_hz7 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))) := bmul sGlobal62_hz3 sGlobal62_hz4 (by norm_num) (by norm_num)

theorem sGlobal62_hz8 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) ((√(12225 : ℝ)) + ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := badd sGlobal62_hz6 sGlobal62_hz7 (by norm_num) (by norm_num)

theorem sGlobal62_hz9 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) (s3ap 12225 46) := by
    convert sGlobal62_hz8 using 1 <;>
      norm_num [s3ap, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal62_hz10 : B (163599182004089 / 1000000000000000000) (16359918200409 / 100000000000000000) ((2 : ℝ) / (12225 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal62_hz11 : B (1222499983640081799591 / 100000000000000000) (12224999836400817995911 / 1000000000000000000) ((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ))) := bsub (bpoint (12225 : ℝ)) sGlobal62_hz10 (by norm_num) (by norm_num)

theorem sGlobal62_hz12 : B (110566721197658827907 / 1000000000000000000) (27641680299414706977 / 250000000000000000) (√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) := bsqrt sGlobal62_hz11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal62_hz13 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) ((√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) - ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bsub sGlobal62_hz12 sGlobal62_hz7 (by norm_num) (by norm_num)

theorem sGlobal62_hz14 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) (s3am 12225 46) := by
    convert sGlobal62_hz13 using 1 <;>
      norm_num [s3am, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal62_hz15 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√((2 / 12225) : ℝ)) * (√(92 : ℝ))) := bmul sGlobal62_hz4 sGlobal62_hz3 (by norm_num) (by norm_num)

theorem sGlobal62_hz16 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) (s3e0 12225 46) := by
    convert sGlobal62_hz15 using 1 <;>
      norm_num [s3e0, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal62_hz17 : B (250196148528560847 / 500000000000000000) (100078459411424339 / 200000000000000000) (((1 / 2) : ℝ) + maskSlack) := badd (bpoint ((1 / 2) : ℝ)) sGlobal62_hz2 (by norm_num) (by norm_num)

theorem sGlobal62_hz18 : B (59827153232297998295487 / 800000000000000) (23930861292919199366019 / 320000000000000) ((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack)) := bmul (bpoint (149450625 : ℝ)) sGlobal62_hz17 (by norm_num) (by norm_num)

theorem sGlobal62_hz19 : B (1729554180017180009583 / 200000000000000000) (8647770900085900056557 / 1000000000000000000) (√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) := bsqrt sGlobal62_hz18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal62_hz20 : B (4328681281566262743499 / 500000000000000000) (8657362563132525495641 / 1000000000000000000) ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))) := badd sGlobal62_hz19 sGlobal62_hz3 (by norm_num) (by norm_num)

theorem sGlobal62_hz21 : B (110732771457999278473 / 1000000000000000000) (55366385728999643621 / 500000000000000000) ((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ)))) := bmul sGlobal62_hz4 sGlobal62_hz20 (by norm_num) (by norm_num)

theorem sGlobal62_hz22 : B (209099159 / 15625000000000000) (13382346177 / 1000000000000000000) ((2 : ℝ) / (149450625 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (149450625 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal62_hz23 : B (2452349334953899930479 / 200000000000000000) (12261746674769501594427 / 1000000000000000000) (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2) := bsq sGlobal62_hz21 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal62_hz24 : B (82045469362091 / 500000000000000000) (32818187747289 / 200000000000000000) (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2)) := bmul sGlobal62_hz22 sGlobal62_hz23 (by norm_num) (by norm_num)

theorem sGlobal62_hz25 : B (82045469362091 / 250000000000000000) (32818187747289 / 100000000000000000) ((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) := bmul (bpoint (2 : ℝ)) sGlobal62_hz24 (by norm_num) (by norm_num)

theorem sGlobal62_hz26 : B (117258080744995992792057 / 1000000000000000000) (58629040372497996396029 / 500000000000000000) (√(13749457500 : ℝ)) := bsqrt (bpoint (13749457500 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal62_hz27 : B (117304080744995992792057 / 1000000000000000000) (58652040372497996396029 / 500000000000000000) ((√(13749457500 : ℝ)) + (46 : ℝ)) := badd sGlobal62_hz26 (bpoint (46 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal62_hz28 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal62_hz25 sGlobal62_hz27 (by norm_num) (by norm_num)

theorem sGlobal62_hz29 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (s3rs 12225 46 maskSlack) := by
    convert sGlobal62_hz28 using 1 <;>
      norm_num [s3rs, s3pp, s3K, mA, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal62_hz30 : B (490797546012267 / 1000000000000000000) (49079754601227 / 100000000000000000) ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (3 : ℝ)) sGlobal62_hz10 (by norm_num) (by norm_num)

theorem sGlobal62_hz31 : B (490797546012267 / 500000000000000000) (49079754601227 / 50000000000000000) ((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal62_hz30 (by norm_num) (by norm_num)

theorem sGlobal62_hz32 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal62_hz31 sGlobal62_hz27 (by norm_num) (by norm_num)

theorem sGlobal62_hz33 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (s3r1 12225 46) := by
    convert sGlobal62_hz32 using 1 <;>
      norm_num [s3r1, mA] <;> ring

theorem sGlobal62_hz34 : B (163599182004089 / 500000000000000000) (16359918200409 / 50000000000000000) ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (2 : ℝ)) sGlobal62_hz10 (by norm_num) (by norm_num)

theorem sGlobal62_hz35 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal62_hz34 (by norm_num) (by norm_num)

theorem sGlobal62_hz36 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal62_hz35 sGlobal62_hz27 (by norm_num) (by norm_num)

theorem sGlobal62_hz37 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (s3rpp 12225 46) := by
    convert sGlobal62_hz36 using 1 <;>
      norm_num [s3rpp, mA] <;> ring

theorem sGlobal62_hz38 {c : ℝ} (hc : B (131 / 200) (33 / 50) c) : B (131 / 200) (33 / 50) c := hc

theorem sGlobal62_hz39 : B (363665694319129201 / 500000000000000000) (145466277727651681 / 200000000000000000) (kdot ((131 / 200))) := by
    constructor
    · apply bkdot_lower (q := (228286669837241359 / 500000000000000000)) (a := (107076713289822229 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (456573339674482717 / 1000000000000000000)) (a := (428306853159288913 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal62_hz40 : B (17161 / 40000) (17161 / 40000) (((131 / 200) : ℝ)^2) := bsq (bpoint ((131 / 200) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal62_hz41 : B (22839 / 40000) (22839 / 40000) ((1 : ℝ) - (((131 / 200) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal62_hz40 (by norm_num) (by norm_num)

theorem sGlobal62_hz42 : B (23613402411289653 / 31250000000000000) (755628877161268897 / 1000000000000000000) (√((1 : ℝ) - (((131 / 200) : ℝ)^2))) := bsqrt sGlobal62_hz41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal62_hz43 : B (60131035471597261 / 250000000000000000) (48104828377277809 / 200000000000000000) ((√((1 : ℝ) - (((131 / 200) : ℝ)^2))) / Real.pi) := bdiv sGlobal62_hz42 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal62_hz44 : B (476402059558059253 / 1000000000000000000) (59550257444757407 / 125000000000000000) (((131 / 200) : ℝ) * (kdot ((131 / 200)))) := bmul (bpoint ((131 / 200) : ℝ)) sGlobal62_hz39 (by norm_num) (by norm_num)

theorem sGlobal62_hz45 : B (716926201444448297 / 1000000000000000000) (716926201444448301 / 1000000000000000000) (((√((1 : ℝ) - (((131 / 200) : ℝ)^2))) / Real.pi) + (((131 / 200) : ℝ) * (kdot ((131 / 200))))) := badd sGlobal62_hz43 sGlobal62_hz44 (by norm_num) (by norm_num)

theorem sGlobal62_hz46 : B (716926201444448297 / 1000000000000000000) (716926201444448301 / 1000000000000000000) (kappa ((131 / 200))) := by rw [kappa_eq]; exact sGlobal62_hz45

theorem sGlobal62_hz47 : B (364721868865849627 / 500000000000000000) (729443737731699257 / 1000000000000000000) (kdot ((33 / 50))) := by
    constructor
    · apply bkdot_lower (q := (452569637855251769 / 1000000000000000000)) (a := (84997756592480699 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (56571204731906471 / 125000000000000000)) (a := (424988782962403493 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal62_hz48 : B (1089 / 2500) (1089 / 2500) (((33 / 50) : ℝ)^2) := bsq (bpoint ((33 / 50) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal62_hz49 : B (1411 / 2500) (1411 / 2500) ((1 : ℝ) - (((33 / 50) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal62_hz48 (by norm_num) (by norm_num)

theorem sGlobal62_hz50 : B (46954099927482371 / 62500000000000000) (751265598839717937 / 1000000000000000000) (√((1 : ℝ) - (((33 / 50) : ℝ)^2))) := bsqrt sGlobal62_hz49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal62_hz51 : B (239135267260467957 / 1000000000000000000) (119567633630233979 / 500000000000000000) ((√((1 : ℝ) - (((33 / 50) : ℝ)^2))) / Real.pi) := bdiv sGlobal62_hz50 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal62_hz52 : B (481432866902921507 / 1000000000000000000) (48143286690292151 / 100000000000000000) (((33 / 50) : ℝ) * (kdot ((33 / 50)))) := bmul (bpoint ((33 / 50) : ℝ)) sGlobal62_hz47 (by norm_num) (by norm_num)

theorem sGlobal62_hz53 : B (90071016770423683 / 125000000000000000) (180142033540847367 / 250000000000000000) (((√((1 : ℝ) - (((33 / 50) : ℝ)^2))) / Real.pi) + (((33 / 50) : ℝ) * (kdot ((33 / 50))))) := badd sGlobal62_hz51 sGlobal62_hz52 (by norm_num) (by norm_num)

theorem sGlobal62_hz54 : B (90071016770423683 / 125000000000000000) (180142033540847367 / 250000000000000000) (kappa ((33 / 50))) := by rw [kappa_eq]; exact sGlobal62_hz53

theorem sGlobal62_hz55 {c : ℝ} (hc : B (131 / 200) (33 / 50) c) : B (716926201444448297 / 1000000000000000000) (180142033540847367 / 250000000000000000) (kappa c) := bkappa (sGlobal62_hz38 hc) (by norm_num) (by norm_num) sGlobal62_hz46.1 sGlobal62_hz54.2

theorem sGlobal62_hz56 : B 24450 24450 ((2 : ℝ) * (12225 : ℝ)) := bmul (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal62_hz57 {c : ℝ} (hc : B (131 / 200) (33 / 50) c) : B (69857966459152633 / 250000000000000000) (283073798555551703 / 1000000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (sGlobal62_hz55 hc) (by norm_num) (by norm_num)

theorem sGlobal62_hz58 {c : ℝ} (hc : B (131 / 200) (33 / 50) c) : B (34160545598525637537 / 5000000000000000) (138423087493664782767 / 20000000000000000) (((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) := bmul sGlobal62_hz56 (sGlobal62_hz57 hc) (by norm_num) (by norm_num)

theorem sGlobal62_hz59 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (4 : ℝ)) sGlobal62_hz10 (by norm_num) (by norm_num)

theorem sGlobal62_hz60 {c : ℝ} (hc : B (131 / 200) (33 / 50) c) : B (42700677908177496819 / 6250000000000000) (3460576860143255560997 / 500000000000000000) ((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bsub (sGlobal62_hz58 hc) sGlobal62_hz59 (by norm_num) (by norm_num)

theorem sGlobal62_hz61 {c : ℝ} (hc : B (131 / 200) (33 / 50) c) : B (82656569402004578301 / 1000000000000000000) (83193471620593590433 / 1000000000000000000) (√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) := bsqrt (sGlobal62_hz60 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal62_hz62 : B (30670756373515103 / 125000000000000000) (122683025494060423 / 500000000000000000) ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal62_hz7 (by norm_num) (by norm_num)

theorem sGlobal62_hz63 {c : ℝ} (hc : B (131 / 200) (33 / 50) c) : B (16482240670203291491 / 200000000000000000) (82948105569605469609 / 1000000000000000000) ((√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) - ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))))) := bsub (sGlobal62_hz61 hc) sGlobal62_hz62 (by norm_num) (by norm_num)

theorem sGlobal62_hz64 {c : ℝ} (hc : B (131 / 200) (33 / 50) c) : B (16482240670203291491 / 200000000000000000) (82948105569605469609 / 1000000000000000000) (s3dm 12225 46 c) := by
    convert (sGlobal62_hz63 hc) using 1 <;>
      norm_num [s3dm, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal62_hz65 : B (6126072185528622723889 / 500000000000000000) (2450428874211449090087 / 200000000000000000) ((s3ap 12225 46)^2) := bsq sGlobal62_hz9 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal62_hz66 : B (6126072185528622723889 / 250000000000000000) (2450428874211449090087 / 100000000000000000) ((2 : ℝ) * ((s3ap 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal62_hz65 (by norm_num) (by norm_num)

theorem sGlobal62_hz67 {c : ℝ} (hc : B (131 / 200) (33 / 50) c) : B (3395803218881293093271 / 500000000000000000) (3440194108793206963927 / 500000000000000000) ((s3dm 12225 46 c)^2) := bsq (sGlobal62_hz64 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal62_hz68 {c : ℝ} (hc : B (131 / 200) (33 / 50) c) : B (8811950262264038483851 / 500000000000000000) (2214085288043988089291 / 125000000000000000) (((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) := bsub sGlobal62_hz66 (sGlobal62_hz67 hc) (by norm_num) (by norm_num)

theorem sGlobal62_hz69 : B (1524735695971823534271 / 125000000000000000) (609894278388729413841 / 50000000000000000) ((s3am 12225 46)^2) := bsq sGlobal62_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal62_hz70 : B (1524735695971823534271 / 62500000000000000) (609894278388729413841 / 25000000000000000) ((2 : ℝ) * ((s3am 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal62_hz69 (by norm_num) (by norm_num)

theorem sGlobal62_hz71 {c : ℝ} (hc : B (131 / 200) (33 / 50) c) : B (722416210031039993 / 1000000000000000000) (145211087658887173 / 200000000000000000) ((((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) / ((2 : ℝ) * ((s3am 12225 46)^2))) := bdiv (sGlobal62_hz68 hc) sGlobal62_hz70 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal62_hz72 {c : ℝ} (hc : B (131 / 200) (33 / 50) c) : B (722416210031039993 / 1000000000000000000) (145211087658887173 / 200000000000000000) (s3c1 12225 46 c) := by
    convert (sGlobal62_hz71 hc) using 1 <;>
      norm_num [s3c1] <;> ring

theorem sGlobal62_hz73 {c : ℝ} (hc : B (131 / 200) (33 / 50) c) : B (363665694319129201 / 500000000000000000) (729443737731699257 / 1000000000000000000) (kdot c) := bkdot (sGlobal62_hz38 hc) sGlobal62_hz39.1 sGlobal62_hz47.2

theorem sGlobal62_hz74 : B (756968495620397541 / 1000000000000000000) (756968495620397543 / 1000000000000000000) (kdot ((722416210031039993 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (100361699553870277 / 250000000000000000)) (a := (381752994374917373 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (401446798215481107 / 1000000000000000000)) (a := (381752994374917371 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal62_hz75 : B (47415527364001907 / 62500000000000000) (379324218912015257 / 500000000000000000) (kdot ((145211087658887173 / 200000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (398385911285121167 / 1000000000000000000)) (a := (189557073666111489 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (199192955642560583 / 500000000000000000)) (a := (92557164876031 / 244140625000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal62_hz76 {c : ℝ} (hc : B (131 / 200) (33 / 50) c) : B (756968495620397541 / 1000000000000000000) (379324218912015257 / 500000000000000000) (kdot (s3c1 12225 46 c)) := bkdot (sGlobal62_hz72 hc) sGlobal62_hz74.1 sGlobal62_hz75.2

theorem sGlobal62_hz77 {c : ℝ} (hc : B (131 / 200) (33 / 50) c) : B (17161 / 40000) (1089 / 2500) (c^2) := bsq (sGlobal62_hz38 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal62_hz78 {c : ℝ} (hc : B (131 / 200) (33 / 50) c) : B (1411 / 2500) (22839 / 40000) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (sGlobal62_hz77 hc) (by norm_num) (by norm_num)

theorem sGlobal62_hz79 {c : ℝ} (hc : B (131 / 200) (33 / 50) c) : B (46954099927482371 / 62500000000000000) (755628877161268897 / 1000000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (sGlobal62_hz78 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal62_hz80 : B (39119999999999765769 / 1600000000000000) (3912000000000000489 / 160000000000000) ((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (149450625 : ℝ)) sGlobal62_hz10 (by norm_num) (by norm_num)

theorem sGlobal62_hz81 {c : ℝ} (hc : B (131 / 200) (33 / 50) c) : B (34151190702515301 / 62500000000000000) (34449297030907689 / 62500000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (sGlobal62_hz79 hc) (sGlobal62_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal62_hz82 {c : ℝ} (hc : B (131 / 200) (33 / 50) c) : B (3339986450705976439631 / 250000000000000000) (13476564998491089621371 / 1000000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) := bmul sGlobal62_hz80 (sGlobal62_hz81 hc) (by norm_num) (by norm_num)

theorem sGlobal62_hz83 {c : ℝ} (hc : B (131 / 200) (33 / 50) c) : B (3339986450705976439631 / 500000000000000000) (3369141249622772405343 / 500000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) / (2 : ℝ)) := bdiv (sGlobal62_hz82 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal62_hz84 {c : ℝ} (hc : B (131 / 200) (33 / 50) c) : B (3339986450705976439631 / 500000000000000000) (3369141249622772405343 / 500000000000000000) (s3Cpa 12225 c) := by
    convert (sGlobal62_hz83 hc) using 1 <;>
      norm_num [s3Cpa, mA] <;> ring

theorem sGlobal62_hz85 {c : ℝ} (hc : B (131 / 200) (33 / 50) c) : B (239135267260467957 / 1000000000000000000) (48104828377277809 / 200000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (sGlobal62_hz79 hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal62_hz86 {c : ℝ} (hc : B (131 / 200) (33 / 50) c) : B (476402059558059253 / 1000000000000000000) (48143286690292151 / 100000000000000000) (c * (kdot c)) := bmul (sGlobal62_hz38 hc) (sGlobal62_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal62_hz87 {c : ℝ} (hc : B (131 / 200) (33 / 50) c) : B (-242297599642453553 / 1000000000000000000) (-3685592463619847 / 15625000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (sGlobal62_hz85 hc) (sGlobal62_hz86 hc) (by norm_num) (by norm_num)

theorem sGlobal62_hz88 {c : ℝ} (hc : B (131 / 200) (33 / 50) c) : B (-5924176311257990111373 / 1000000000000000000) (-5767215087072302054399 / 1000000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) := bmul sGlobal62_hz80 (sGlobal62_hz87 hc) (by norm_num) (by norm_num)

theorem sGlobal62_hz89 {c : ℝ} (hc : B (131 / 200) (33 / 50) c) : B (-2962088155628995055687 / 1000000000000000000) (-2883607543536151027199 / 1000000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) / (2 : ℝ)) := bdiv (sGlobal62_hz88 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal62_hz90 {c : ℝ} (hc : B (131 / 200) (33 / 50) c) : B (-2962088155628995055687 / 1000000000000000000) (-2883607543536151027199 / 1000000000000000000) (s3Cpp 12225 c) := by
    convert (sGlobal62_hz89 hc) using 1 <;>
      norm_num [s3Cpp, mA] <;> ring

theorem sGlobal62_hz91 {c : ℝ} (hc : B (131 / 200) (33 / 50) c) : B (6795118011345690587663 / 1000000000000000000) (53542403196713150179 / 7812500000000000) ((s3Cpa 12225 c) + (s3r1 12225 46)) := badd (sGlobal62_hz84 hc) sGlobal62_hz33 (by norm_num) (by norm_num)

theorem sGlobal62_hz92 {c : ℝ} (hc : B (131 / 200) (33 / 50) c) : B (61525439705067443891 / 1000000000000000000) (62053395752298324801 / 1000000000000000000) (((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) := bdiv (sGlobal62_hz91 hc) sGlobal62_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal62_hz93 {c : ℝ} (hc : B (131 / 200) (33 / 50) c) : B (61648122730561504303 / 1000000000000000000) (7772009847224048153 / 125000000000000000) ((((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) + (s3e0 12225 46)) := badd (sGlobal62_hz92 hc) sGlobal62_hz16 (by norm_num) (by norm_num)

theorem sGlobal62_hz94 {c : ℝ} (hc : B (131 / 200) (33 / 50) c) : B (61648122730561504303 / 1000000000000000000) (7772009847224048153 / 125000000000000000) (s3Lam 12225 46 c) := by
    convert (sGlobal62_hz93 hc) using 1 <;>
      norm_num [s3Lam] <;> ring

theorem sGlobal62_hz95 {c : ℝ} (hc : B (131 / 200) (33 / 50) c) : B (-2885324749006503250087 / 1000000000000000000) (-2806844136913658752381 / 1000000000000000000) ((s3Cpp 12225 c) + (s3rpp 12225 46)) := badd (sGlobal62_hz90 hc) sGlobal62_hz37 (by norm_num) (by norm_num)

theorem sGlobal62_hz96 {c : ℝ} (hc : B (131 / 200) (33 / 50) c) : B (-437789422689759325899 / 200000000000000000) (-140342206845682937619 / 100000000000000000) (if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) := bweaken (bfirst (sGlobal62_hz95 hc) (sGlobal62_hz76 hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem sGlobal62_hz97 {c : ℝ} (hc : B (131 / 200) (33 / 50) c) : B (3800491036202374025269 / 1000000000000000000) (966466193045561156987 / 250000000000000000) ((s3Lam 12225 46 c)^2) := bsq (sGlobal62_hz94 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal62_hz98 {c : ℝ} (hc : B (131 / 200) (33 / 50) c) : B (65235647564451461 / 125000000000000000) (263578249738462683 / 500000000000000000) ((s3c1 12225 46 c)^2) := bsq (sGlobal62_hz72 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal62_hz99 {c : ℝ} (hc : B (131 / 200) (33 / 50) c) : B (236421750261537317 / 500000000000000000) (59764352435548539 / 125000000000000000) ((1 : ℝ) - ((s3c1 12225 46 c)^2)) := bsub (bpoint (1 : ℝ)) (sGlobal62_hz98 hc) (by norm_num) (by norm_num)

theorem sGlobal62_hz100 {c : ℝ} (hc : B (131 / 200) (33 / 50) c) : B (687636168713568057 / 1000000000000000000) (345729236355702319 / 500000000000000000) (√((1 : ℝ) - ((s3c1 12225 46 c)^2))) := bsqrt (sGlobal62_hz99 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal62_hz101 {c : ℝ} (hc : B (131 / 200) (33 / 50) c) : B (270034091996647129 / 125000000000000000) (543070214533141833 / 250000000000000000) (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))) := bmul pi_mem (sGlobal62_hz100 hc) (by norm_num) (by norm_num)

theorem sGlobal62_hz102 {c : ℝ} (hc : B (131 / 200) (33 / 50) c) : B (437384860016388618551 / 250000000000000000) (447381562962780111823 / 250000000000000000) (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2))))) := bdiv (sGlobal62_hz97 hc) (sGlobal62_hz101 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal62_hz103 {c : ℝ} (hc : B (131 / 200) (33 / 50) c) : B (-439407673383242155291 / 1000000000000000000) (193052091697145535551 / 500000000000000000) ((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) := badd (sGlobal62_hz96 hc) (sGlobal62_hz102 hc) (by norm_num) (by norm_num)

theorem sGlobal62_hz104 : B (3762781186094069 / 250000000000000000) (376278118609407 / 25000000000000000) ((s3e0 12225 46)^2) := bsq sGlobal62_hz16 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal62_hz105 {c : ℝ} (hc : B (131 / 200) (33 / 50) c) : B (-87878524451699555803 / 200000000000000000) (193059617259517723691 / 500000000000000000) (((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) := badd (sGlobal62_hz103 hc) sGlobal62_hz104 (by norm_num) (by norm_num)

theorem sGlobal62_hz106 {c : ℝ} (hc : B (131 / 200) (33 / 50) c) : B (-100223887201812627221 / 250000000000000000) (212308153986579858699 / 500000000000000000) ((((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) + (s3rs 12225 46 maskSlack)) := badd (sGlobal62_hz105 hc) sGlobal62_hz29 (by norm_num) (by norm_num)

theorem sGlobal62_hz107 {c : ℝ} (hc : B (131 / 200) (33 / 50) c) : B (-100223887201812627221 / 250000000000000000) (212308153986579858699 / 500000000000000000) (s3U 12225 46 maskSlack c) := by
    convert (sGlobal62_hz106 hc) using 1 <;>
      norm_num [s3U] <;> ring

theorem sGlobal62_hz108 {c : ℝ} (hc : B (131 / 200) (33 / 50) c) : B (-607770312450297466101 / 200000000000000000) (-2960370950158642832799 / 1000000000000000000) ((s3Cpp 12225 c) - (s3rpp 12225 46)) := bsub (sGlobal62_hz90 hc) sGlobal62_hz37 (by norm_num) (by norm_num)

theorem sGlobal62_hz109 {c : ℝ} (hc : B (131 / 200) (33 / 50) c) : B (-607770312450297466101 / 200000000000000000) (-2960370950158642832799 / 1000000000000000000) (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ)) := bweaken (bmin (sGlobal62_hz108 hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem sGlobal62_hz110 {c : ℝ} (hc : B (131 / 200) (33 / 50) c) : B (-92216799619248219161 / 40000000000000000) (-280113443077489341789 / 125000000000000000) ((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) := bmul (sGlobal62_hz76 hc) (sGlobal62_hz109 hc) (by norm_num) (by norm_num)

theorem sGlobal62_hz111 {c : ℝ} (hc : B (131 / 200) (33 / 50) c) : B (-461087008321189971061 / 200000000000000000) (-560230648936164777647 / 250000000000000000) (((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) := bsub (sGlobal62_hz110 hc) sGlobal62_hz104 (by norm_num) (by norm_num)

theorem sGlobal62_hz112 {c : ℝ} (hc : B (131 / 200) (33 / 50) c) : B (-2343932115060074125321 / 1000000000000000000) (-2279419669195906380719 / 1000000000000000000) ((((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) - (s3rs 12225 46 maskSlack)) := bsub (sGlobal62_hz111 hc) sGlobal62_hz29 (by norm_num) (by norm_num)

theorem sGlobal62_hz113 {c : ℝ} (hc : B (131 / 200) (33 / 50) c) : B (-2343932115060074125321 / 1000000000000000000) (-2279419669195906380719 / 1000000000000000000) (s3L 12225 46 maskSlack c) := by
    convert (sGlobal62_hz112 hc) using 1 <;>
      norm_num [s3L] <;> ring

theorem sGlobal62_hz114 {c : ℝ} (hc : B (131 / 200) (33 / 50) c) : B 0 (212308153986579858699 / 500000000000000000) |(s3U 12225 46 maskSlack c)| := bweaken (babs (sGlobal62_hz107 hc)) (by norm_num) (by norm_num)

theorem sGlobal62_hz115 {c : ℝ} (hc : B (131 / 200) (33 / 50) c) : B 0 (2343932115060074125321 / 1000000000000000000) |(s3L 12225 46 maskSlack c)| := bweaken (babs (sGlobal62_hz113 hc)) (by norm_num) (by norm_num)

theorem sGlobal62_hz116 {c : ℝ} (hc : B (131 / 200) (33 / 50) c) : B 0 (2343932115060074125321 / 1000000000000000000) (max |(s3U 12225 46 maskSlack c)| |(s3L 12225 46 maskSlack c)|) := bweaken (bmax (sGlobal62_hz114 hc) (sGlobal62_hz115 hc)) (by norm_num) (by norm_num)

theorem sGlobal62_hz117 {c : ℝ} (hc : B (131 / 200) (33 / 50) c) : B 0 (2343932115060074125321 / 1000000000000000000) (s3nks 12225 46 maskSlack c) := by
    convert (sGlobal62_hz116 hc) using 1 <;>
      norm_num [s3nks] <;> ring

theorem sGlobal62 {c : ℝ} (hc : B (131 / 200) (33 / 50) c) :
    0 < s3am 12225 46 ∧ 0 ≤ s3dm 12225 46 c ∧
    s3dm 12225 46 c ^ 2 ≤ 2 * s3ap 12225 46 ^ 2 ∧ s3c1 12225 46 c < 1 ∧
    0 ≤ s3Cpa 12225 c - s3r1 12225 46 ∧
    s3e0 12225 46 ≤ (s3Cpa 12225 c - s3r1 12225 46) / s3ap 12225 46 ∧
    s3nks 12225 46 maskSlack c ≤ 12225 * (191733 / 1000000) := by

  refine ⟨lt_of_lt_of_le (by norm_num) sGlobal62_hz14.1,
    le_trans (by norm_num) (sGlobal62_hz64 hc).1, ?_,
    lt_of_le_of_lt (sGlobal62_hz72 hc).2 (by norm_num), ?_, ?_,
    le_trans (sGlobal62_hz117 hc).2 (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (sGlobal62_hz64 hc).1) (sGlobal62_hz64 hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) sGlobal62_hz9.1 2
    nlinarith only [h1, h2]
  · linarith only [(sGlobal62_hz84 hc).1, sGlobal62_hz33.2]
  · have hap : 0 < s3ap 12225 46 := lt_of_lt_of_le (by norm_num) sGlobal62_hz9.1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul sGlobal62_hz16.2 sGlobal62_hz9.2 (le_trans (by norm_num) sGlobal62_hz9.1) (by norm_num)
    linarith only [h, (sGlobal62_hz84 hc).1, sGlobal62_hz33.2]

end BstLean.Part255
