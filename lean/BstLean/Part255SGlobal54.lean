import BstLean.Part255SGlobal50
import BstLean.Part255Numeric10
namespace BstLean.Part255
open Real BstLean.Part130 BstLean.Part182 BstLean.Part197 BstLean.Part246
theorem sGlobal54_hz0 : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal54_hz1 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) ((√(23 : ℝ)) / (12225 : ℝ)) := bdiv sGlobal54_hz0 (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal54_hz2 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) maskSlack := by
    convert sGlobal54_hz1 using 1 <;>
      norm_num [maskSlack] <;> ring

theorem sGlobal54_hz3 : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal54_hz4 : B (6395294793910793 / 500000000000000000) (12790589587821587 / 1000000000000000000) (√((2 / 12225) : ℝ)) := bsqrt (bpoint ((2 / 12225) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal54_hz5 : B (7230130686979 / 62500000000000000) (23136418198333 / 200000000000000000) (√((2 / 149450625) : ℝ)) := bsqrt (bpoint ((2 / 149450625) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal54_hz6 : B (2211334438749598093 / 20000000000000000) (110566721937479904651 / 1000000000000000000) (√(12225 : ℝ)) := bsqrt (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal54_hz7 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))) := bmul sGlobal54_hz3 sGlobal54_hz4 (by norm_num) (by norm_num)

theorem sGlobal54_hz8 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) ((√(12225 : ℝ)) + ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := badd sGlobal54_hz6 sGlobal54_hz7 (by norm_num) (by norm_num)

theorem sGlobal54_hz9 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) (s3ap 12225 46) := by
    convert sGlobal54_hz8 using 1 <;>
      norm_num [s3ap, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal54_hz10 : B (163599182004089 / 1000000000000000000) (16359918200409 / 100000000000000000) ((2 : ℝ) / (12225 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal54_hz11 : B (1222499983640081799591 / 100000000000000000) (12224999836400817995911 / 1000000000000000000) ((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ))) := bsub (bpoint (12225 : ℝ)) sGlobal54_hz10 (by norm_num) (by norm_num)

theorem sGlobal54_hz12 : B (110566721197658827907 / 1000000000000000000) (27641680299414706977 / 250000000000000000) (√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) := bsqrt sGlobal54_hz11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal54_hz13 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) ((√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) - ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bsub sGlobal54_hz12 sGlobal54_hz7 (by norm_num) (by norm_num)

theorem sGlobal54_hz14 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) (s3am 12225 46) := by
    convert sGlobal54_hz13 using 1 <;>
      norm_num [s3am, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal54_hz15 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√((2 / 12225) : ℝ)) * (√(92 : ℝ))) := bmul sGlobal54_hz4 sGlobal54_hz3 (by norm_num) (by norm_num)

theorem sGlobal54_hz16 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) (s3e0 12225 46) := by
    convert sGlobal54_hz15 using 1 <;>
      norm_num [s3e0, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal54_hz17 : B (250196148528560847 / 500000000000000000) (100078459411424339 / 200000000000000000) (((1 / 2) : ℝ) + maskSlack) := badd (bpoint ((1 / 2) : ℝ)) sGlobal54_hz2 (by norm_num) (by norm_num)

theorem sGlobal54_hz18 : B (59827153232297998295487 / 800000000000000) (23930861292919199366019 / 320000000000000) ((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack)) := bmul (bpoint (149450625 : ℝ)) sGlobal54_hz17 (by norm_num) (by norm_num)

theorem sGlobal54_hz19 : B (1729554180017180009583 / 200000000000000000) (8647770900085900056557 / 1000000000000000000) (√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) := bsqrt sGlobal54_hz18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal54_hz20 : B (4328681281566262743499 / 500000000000000000) (8657362563132525495641 / 1000000000000000000) ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))) := badd sGlobal54_hz19 sGlobal54_hz3 (by norm_num) (by norm_num)

theorem sGlobal54_hz21 : B (110732771457999278473 / 1000000000000000000) (55366385728999643621 / 500000000000000000) ((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ)))) := bmul sGlobal54_hz4 sGlobal54_hz20 (by norm_num) (by norm_num)

theorem sGlobal54_hz22 : B (209099159 / 15625000000000000) (13382346177 / 1000000000000000000) ((2 : ℝ) / (149450625 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (149450625 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal54_hz23 : B (2452349334953899930479 / 200000000000000000) (12261746674769501594427 / 1000000000000000000) (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2) := bsq sGlobal54_hz21 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal54_hz24 : B (82045469362091 / 500000000000000000) (32818187747289 / 200000000000000000) (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2)) := bmul sGlobal54_hz22 sGlobal54_hz23 (by norm_num) (by norm_num)

theorem sGlobal54_hz25 : B (82045469362091 / 250000000000000000) (32818187747289 / 100000000000000000) ((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) := bmul (bpoint (2 : ℝ)) sGlobal54_hz24 (by norm_num) (by norm_num)

theorem sGlobal54_hz26 : B (117258080744995992792057 / 1000000000000000000) (58629040372497996396029 / 500000000000000000) (√(13749457500 : ℝ)) := bsqrt (bpoint (13749457500 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal54_hz27 : B (117304080744995992792057 / 1000000000000000000) (58652040372497996396029 / 500000000000000000) ((√(13749457500 : ℝ)) + (46 : ℝ)) := badd sGlobal54_hz26 (bpoint (46 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal54_hz28 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal54_hz25 sGlobal54_hz27 (by norm_num) (by norm_num)

theorem sGlobal54_hz29 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (s3rs 12225 46 maskSlack) := by
    convert sGlobal54_hz28 using 1 <;>
      norm_num [s3rs, s3pp, s3K, mA, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal54_hz30 : B (490797546012267 / 1000000000000000000) (49079754601227 / 100000000000000000) ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (3 : ℝ)) sGlobal54_hz10 (by norm_num) (by norm_num)

theorem sGlobal54_hz31 : B (490797546012267 / 500000000000000000) (49079754601227 / 50000000000000000) ((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal54_hz30 (by norm_num) (by norm_num)

theorem sGlobal54_hz32 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal54_hz31 sGlobal54_hz27 (by norm_num) (by norm_num)

theorem sGlobal54_hz33 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (s3r1 12225 46) := by
    convert sGlobal54_hz32 using 1 <;>
      norm_num [s3r1, mA] <;> ring

theorem sGlobal54_hz34 : B (163599182004089 / 500000000000000000) (16359918200409 / 50000000000000000) ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (2 : ℝ)) sGlobal54_hz10 (by norm_num) (by norm_num)

theorem sGlobal54_hz35 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal54_hz34 (by norm_num) (by norm_num)

theorem sGlobal54_hz36 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal54_hz35 sGlobal54_hz27 (by norm_num) (by norm_num)

theorem sGlobal54_hz37 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (s3rpp 12225 46) := by
    convert sGlobal54_hz36 using 1 <;>
      norm_num [s3rpp, mA] <;> ring

theorem sGlobal54_hz38 {c : ℝ} (hc : B (123 / 200) (31 / 50) c) : B (123 / 200) (31 / 50) c := hc

theorem sGlobal54_hz39 : B (710844001606924669 / 1000000000000000000) (355422000803462343 / 500000000000000000) (kdot ((123 / 200))) := by
    constructor
    · apply bkdot_lower (q := (244126039618501659 / 500000000000000000)) (a := (227102590073276879 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (488252079237003317 / 1000000000000000000)) (a := (227102590073276867 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal54_hz40 : B (15129 / 40000) (15129 / 40000) (((123 / 200) : ℝ)^2) := bsq (bpoint ((123 / 200) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal54_hz41 : B (24871 / 40000) (24871 / 40000) ((1 : ℝ) - (((123 / 200) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal54_hz40 (by norm_num) (by norm_num)

theorem sGlobal54_hz42 : B (788527107967760357 / 1000000000000000000) (394263553983880179 / 500000000000000000) (√((1 : ℝ) - (((123 / 200) : ℝ)^2))) := bsqrt sGlobal54_hz41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal54_hz43 : B (250995973990051417 / 1000000000000000000) (125497986995025709 / 500000000000000000) ((√((1 : ℝ) - (((123 / 200) : ℝ)^2))) / Real.pi) := bdiv sGlobal54_hz42 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal54_hz44 : B (437169060988258671 / 1000000000000000000) (218584530494129341 / 500000000000000000) (((123 / 200) : ℝ) * (kdot ((123 / 200)))) := bmul (bpoint ((123 / 200) : ℝ)) sGlobal54_hz39 (by norm_num) (by norm_num)

theorem sGlobal54_hz45 : B (86020629372288761 / 125000000000000000) (6881650349783101 / 10000000000000000) (((√((1 : ℝ) - (((123 / 200) : ℝ)^2))) / Real.pi) + (((123 / 200) : ℝ) * (kdot ((123 / 200))))) := badd sGlobal54_hz43 sGlobal54_hz44 (by norm_num) (by norm_num)

theorem sGlobal54_hz46 : B (86020629372288761 / 125000000000000000) (6881650349783101 / 10000000000000000) (kappa ((123 / 200))) := by rw [kappa_eq]; exact sGlobal54_hz45

theorem sGlobal54_hz47 : B (11138553339727929 / 15625000000000000) (712867413742587469 / 1000000000000000000) (kdot ((31 / 50))) := by
    constructor
    · apply bkdot_lower (q := (484322104837852617 / 1000000000000000000)) (a := (90205362359252487 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (60540263104731577 / 125000000000000000)) (a := (451026811796262417 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal54_hz48 : B (961 / 2500) (961 / 2500) (((31 / 50) : ℝ)^2) := bsq (bpoint ((31 / 50) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal54_hz49 : B (1539 / 2500) (1539 / 2500) ((1 : ℝ) - (((31 / 50) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal54_hz48 (by norm_num) (by norm_num)

theorem sGlobal54_hz50 : B (784601809837321239 / 1000000000000000000) (19615045245933031 / 25000000000000000) (√((1 : ℝ) - (((31 / 50) : ℝ)^2))) := bsqrt sGlobal54_hz49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal54_hz51 : B (49949302557782779 / 200000000000000000) (31218314098614237 / 125000000000000000) ((√((1 : ℝ) - (((31 / 50) : ℝ)^2))) / Real.pi) := bdiv sGlobal54_hz50 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal54_hz52 : B (220988898260202111 / 500000000000000000) (441977796520404231 / 1000000000000000000) (((31 / 50) : ℝ) * (kdot ((31 / 50)))) := bmul (bpoint ((31 / 50) : ℝ)) sGlobal54_hz47 (by norm_num) (by norm_num)

theorem sGlobal54_hz53 : B (691724309309318117 / 1000000000000000000) (691724309309318127 / 1000000000000000000) (((√((1 : ℝ) - (((31 / 50) : ℝ)^2))) / Real.pi) + (((31 / 50) : ℝ) * (kdot ((31 / 50))))) := badd sGlobal54_hz51 sGlobal54_hz52 (by norm_num) (by norm_num)

theorem sGlobal54_hz54 : B (691724309309318117 / 1000000000000000000) (691724309309318127 / 1000000000000000000) (kappa ((31 / 50))) := by rw [kappa_eq]; exact sGlobal54_hz53

theorem sGlobal54_hz55 {c : ℝ} (hc : B (123 / 200) (31 / 50) c) : B (86020629372288761 / 125000000000000000) (691724309309318127 / 1000000000000000000) (kappa c) := bkappa (sGlobal54_hz38 hc) (by norm_num) (by norm_num) sGlobal54_hz46.1 sGlobal54_hz54.2

theorem sGlobal54_hz56 : B 24450 24450 ((2 : ℝ) * (12225 : ℝ)) := bmul (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal54_hz57 {c : ℝ} (hc : B (123 / 200) (31 / 50) c) : B (308275690690681873 / 1000000000000000000) (38979370627711239 / 125000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (sGlobal54_hz55 hc) (by norm_num) (by norm_num)

theorem sGlobal54_hz58 {c : ℝ} (hc : B (123 / 200) (31 / 50) c) : B (150746812747743435897 / 20000000000000000) (19060912236950795871 / 2500000000000000) (((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) := bmul sGlobal54_hz56 (sGlobal54_hz57 hc) (by norm_num) (by norm_num)

theorem sGlobal54_hz59 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (4 : ℝ)) sGlobal54_hz10 (by norm_num) (by norm_num)

theorem sGlobal54_hz60 {c : ℝ} (hc : B (123 / 200) (31 / 50) c) : B (753733998299044377849 / 100000000000000000) (1906091060095897583011 / 250000000000000000) ((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bsub (sGlobal54_hz58 hc) sGlobal54_hz59 (by norm_num) (by norm_num)

theorem sGlobal54_hz61 {c : ℝ} (hc : B (123 / 200) (31 / 50) c) : B (86817855208421520751 / 1000000000000000000) (21829401389501600251 / 250000000000000000) (√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) := bsqrt (sGlobal54_hz60 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal54_hz62 : B (30670756373515103 / 125000000000000000) (122683025494060423 / 500000000000000000) ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal54_hz7 (by norm_num) (by norm_num)

theorem sGlobal54_hz63 {c : ℝ} (hc : B (123 / 200) (31 / 50) c) : B (17314497831486679981 / 200000000000000000) (4353611975350914009 / 50000000000000000) ((√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) - ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))))) := bsub (sGlobal54_hz61 hc) sGlobal54_hz62 (by norm_num) (by norm_num)

theorem sGlobal54_hz64 {c : ℝ} (hc : B (123 / 200) (31 / 50) c) : B (17314497831486679981 / 200000000000000000) (4353611975350914009 / 50000000000000000) (s3dm 12225 46 c) := by
    convert (sGlobal54_hz63 hc) using 1 <;>
      norm_num [s3dm, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal54_hz65 : B (6126072185528622723889 / 500000000000000000) (2450428874211449090087 / 200000000000000000) ((s3ap 12225 46)^2) := bsq sGlobal54_hz9 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal54_hz66 : B (6126072185528622723889 / 250000000000000000) (2450428874211449090087 / 100000000000000000) ((2 : ℝ) * ((s3ap 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal54_hz65 (by norm_num) (by norm_num)

theorem sGlobal54_hz67 {c : ℝ} (hc : B (123 / 200) (31 / 50) c) : B (7494795878913923587801 / 1000000000000000000) (473848430797972187217 / 62500000000000000) ((s3dm 12225 46 c)^2) := bsq (sGlobal54_hz64 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal54_hz68 {c : ℝ} (hc : B (123 / 200) (31 / 50) c) : B (4230678462336733975021 / 250000000000000000) (17009492863200567313069 / 1000000000000000000) (((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) := bsub sGlobal54_hz66 (sGlobal54_hz67 hc) (by norm_num) (by norm_num)

theorem sGlobal54_hz69 : B (1524735695971823534271 / 125000000000000000) (609894278388729413841 / 50000000000000000) ((s3am 12225 46)^2) := bsq sGlobal54_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal54_hz70 : B (1524735695971823534271 / 62500000000000000) (609894278388729413841 / 25000000000000000) ((2 : ℝ) * ((s3am 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal54_hz69 (by norm_num) (by norm_num)

theorem sGlobal54_hz71 {c : ℝ} (hc : B (123 / 200) (31 / 50) c) : B (173418517448372373 / 250000000000000000) (697231203256148447 / 1000000000000000000) ((((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) / ((2 : ℝ) * ((s3am 12225 46)^2))) := bdiv (sGlobal54_hz68 hc) sGlobal54_hz70 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal54_hz72 {c : ℝ} (hc : B (123 / 200) (31 / 50) c) : B (173418517448372373 / 250000000000000000) (697231203256148447 / 1000000000000000000) (s3c1 12225 46 c) := by
    convert (sGlobal54_hz71 hc) using 1 <;>
      norm_num [s3c1] <;> ring

theorem sGlobal54_hz73 {c : ℝ} (hc : B (123 / 200) (31 / 50) c) : B (710844001606924669 / 1000000000000000000) (712867413742587469 / 1000000000000000000) (kdot c) := bkdot (sGlobal54_hz38 hc) sGlobal54_hz39.1 sGlobal54_hz47.2

theorem sGlobal54_hz74 : B (93001146985502201 / 125000000000000000) (74400917588401761 / 100000000000000000) (kdot ((173418517448372373 / 250000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (425281960424079897 / 1000000000000000000)) (a := (402109446214583579 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (53160245053009987 / 125000000000000000)) (a := (402109446214583577 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal54_hz75 : B (23299528299846893 / 31250000000000000) (372792452797550289 / 500000000000000000) (kdot ((697231203256148447 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (211181105000268197 / 500000000000000000)) (a := (39963429577239287 / 100000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (422362210000536393 / 1000000000000000000)) (a := (99908573943098217 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal54_hz76 {c : ℝ} (hc : B (123 / 200) (31 / 50) c) : B (93001146985502201 / 125000000000000000) (372792452797550289 / 500000000000000000) (kdot (s3c1 12225 46 c)) := bkdot (sGlobal54_hz72 hc) sGlobal54_hz74.1 sGlobal54_hz75.2

theorem sGlobal54_hz77 {c : ℝ} (hc : B (123 / 200) (31 / 50) c) : B (15129 / 40000) (961 / 2500) (c^2) := bsq (sGlobal54_hz38 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal54_hz78 {c : ℝ} (hc : B (123 / 200) (31 / 50) c) : B (1539 / 2500) (24871 / 40000) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (sGlobal54_hz77 hc) (by norm_num) (by norm_num)

theorem sGlobal54_hz79 {c : ℝ} (hc : B (123 / 200) (31 / 50) c) : B (784601809837321239 / 1000000000000000000) (394263553983880179 / 500000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (sGlobal54_hz78 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal54_hz80 : B (39119999999999765769 / 1600000000000000) (3912000000000000489 / 160000000000000) ((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (149450625 : ℝ)) sGlobal54_hz10 (by norm_num) (by norm_num)

theorem sGlobal54_hz81 {c : ℝ} (hc : B (123 / 200) (31 / 50) c) : B (278864745086398391 / 500000000000000000) (140528820030724841 / 250000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (sGlobal54_hz79 hc) (sGlobal54_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal54_hz82 {c : ℝ} (hc : B (123 / 200) (31 / 50) c) : B (13636486034724799671439 / 1000000000000000000) (2748743719800978233553 / 200000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) := bmul sGlobal54_hz80 (sGlobal54_hz81 hc) (by norm_num) (by norm_num)

theorem sGlobal54_hz83 {c : ℝ} (hc : B (123 / 200) (31 / 50) c) : B (6818243017362399835719 / 1000000000000000000) (6871859299502445583883 / 1000000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) / (2 : ℝ)) := bdiv (sGlobal54_hz82 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal54_hz84 {c : ℝ} (hc : B (123 / 200) (31 / 50) c) : B (6818243017362399835719 / 1000000000000000000) (6871859299502445583883 / 1000000000000000000) (s3Cpa 12225 c) := by
    convert (sGlobal54_hz83 hc) using 1 <;>
      norm_num [s3Cpa, mA] <;> ring

theorem sGlobal54_hz85 {c : ℝ} (hc : B (123 / 200) (31 / 50) c) : B (49949302557782779 / 200000000000000000) (125497986995025709 / 500000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (sGlobal54_hz79 hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal54_hz86 {c : ℝ} (hc : B (123 / 200) (31 / 50) c) : B (437169060988258671 / 1000000000000000000) (441977796520404231 / 1000000000000000000) (c * (kdot c)) := bmul (sGlobal54_hz38 hc) (sGlobal54_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal54_hz87 {c : ℝ} (hc : B (123 / 200) (31 / 50) c) : B (-6007227616609073 / 31250000000000000) (-186173086998207253 / 1000000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (sGlobal54_hz85 hc) (sGlobal54_hz86 hc) (by norm_num) (by norm_num)

theorem sGlobal54_hz88 {c : ℝ} (hc : B (123 / 200) (31 / 50) c) : B (-4700054887234939302707 / 1000000000000000000) (-4551931977106140081157 / 1000000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) := bmul sGlobal54_hz80 (sGlobal54_hz87 hc) (by norm_num) (by norm_num)

theorem sGlobal54_hz89 {c : ℝ} (hc : B (123 / 200) (31 / 50) c) : B (-1175013721808734825677 / 500000000000000000) (-1137982994276535020289 / 500000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) / (2 : ℝ)) := bdiv (sGlobal54_hz88 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal54_hz90 {c : ℝ} (hc : B (123 / 200) (31 / 50) c) : B (-1175013721808734825677 / 500000000000000000) (-1137982994276535020289 / 500000000000000000) (s3Cpp 12225 c) := by
    convert (sGlobal54_hz89 hc) using 1 <;>
      norm_num [s3Cpp, mA] <;> ring

theorem sGlobal54_hz91 {c : ℝ} (hc : B (123 / 200) (31 / 50) c) : B (173334703182403438603 / 25000000000000000) (6987004409436183996109 / 1000000000000000000) ((s3Cpa 12225 c) + (s3r1 12225 46)) := badd (sGlobal54_hz84 hc) sGlobal54_hz33 (by norm_num) (by norm_num)

theorem sGlobal54_hz92 {c : ℝ} (hc : B (123 / 200) (31 / 50) c) : B (6277738701013524429 / 100000000000000000) (63262848090944940497 / 1000000000000000000) (((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) := bdiv (sGlobal54_hz91 hc) sGlobal54_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal54_hz93 {c : ℝ} (hc : B (123 / 200) (31 / 50) c) : B (31450035017814652351 / 500000000000000000) (1584638277910975023 / 25000000000000000) ((((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) + (s3e0 12225 46)) := badd (sGlobal54_hz92 hc) sGlobal54_hz16 (by norm_num) (by norm_num)

theorem sGlobal54_hz94 {c : ℝ} (hc : B (123 / 200) (31 / 50) c) : B (31450035017814652351 / 500000000000000000) (1584638277910975023 / 25000000000000000) (s3Lam 12225 46 c) := by
    convert (sGlobal54_hz93 hc) using 1 <;>
      norm_num [s3Lam] <;> ring

theorem sGlobal54_hz95 {c : ℝ} (hc : B (123 / 200) (31 / 50) c) : B (-1136632018497488922877 / 500000000000000000) (-3436254034266527759 / 1562500000000000) ((s3Cpp 12225 c) + (s3rpp 12225 46)) := badd (sGlobal54_hz90 hc) sGlobal54_hz37 (by norm_num) (by norm_num)

theorem sGlobal54_hz96 {c : ℝ} (hc : B (123 / 200) (31 / 50) c) : B (-847455676207818892483 / 500000000000000000) (-3436254034266527759 / 3125000000000000) (if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) := bweaken (bfirst (sGlobal54_hz95 hc) (sGlobal54_hz76 hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem sGlobal54_hz97 {c : ℝ} (hc : B (123 / 200) (31 / 50) c) : B (3956418810487071520883 / 1000000000000000000) (2008862777456528409203 / 500000000000000000) ((s3Lam 12225 46 c)^2) := bsq (sGlobal54_hz94 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal54_hz98 {c : ℝ} (hc : B (123 / 200) (31 / 50) c) : B (48118371510386293 / 100000000000000000) (486131350794016589 / 1000000000000000000) ((s3c1 12225 46 c)^2) := bsq (sGlobal54_hz72 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal54_hz99 {c : ℝ} (hc : B (123 / 200) (31 / 50) c) : B (513868649205983411 / 1000000000000000000) (51881628489613707 / 100000000000000000) ((1 : ℝ) - ((s3c1 12225 46 c)^2)) := bsub (bpoint (1 : ℝ)) (sGlobal54_hz98 hc) (by norm_num) (by norm_num)

theorem sGlobal54_hz100 {c : ℝ} (hc : B (123 / 200) (31 / 50) c) : B (358423160944568219 / 500000000000000000) (720289028721205131 / 1000000000000000000) (√((1 : ℝ) - ((s3c1 12225 46 c)^2))) := bsqrt (sGlobal54_hz99 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal54_hz101 {c : ℝ} (hc : B (123 / 200) (31 / 50) c) : B (2252039138599775227 / 1000000000000000000) (282856840136483203 / 125000000000000000) (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))) := bmul pi_mem (sGlobal54_hz100 hc) (by norm_num) (by norm_num)

theorem sGlobal54_hz102 {c : ℝ} (hc : B (123 / 200) (31 / 50) c) : B (349683854965115269827 / 200000000000000000) (223004869567404163841 / 125000000000000000) (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2))))) := bdiv (sGlobal54_hz97 hc) (sGlobal54_hz101 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal54_hz103 {c : ℝ} (hc : B (123 / 200) (31 / 50) c) : B (53507922409938564169 / 1000000000000000000) (85554708196743053481 / 125000000000000000) ((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) := badd (sGlobal54_hz96 hc) (sGlobal54_hz102 hc) (by norm_num) (by norm_num)

theorem sGlobal54_hz104 : B (3762781186094069 / 250000000000000000) (376278118609407 / 25000000000000000) ((s3e0 12225 46)^2) := bsq sGlobal54_hz16 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal54_hz105 {c : ℝ} (hc : B (123 / 200) (31 / 50) c) : B (10704594706936588089 / 200000000000000000) (21389147396834025129 / 31250000000000000) (((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) := badd (sGlobal54_hz103 hc) sGlobal54_hz104 (by norm_num) (by norm_num)

theorem sGlobal54_hz106 {c : ℝ} (hc : B (123 / 200) (31 / 50) c) : B (5751252936620638161 / 62500000000000000) (22592180942275408567 / 31250000000000000) ((((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) + (s3rs 12225 46 maskSlack)) := badd (sGlobal54_hz105 hc) sGlobal54_hz29 (by norm_num) (by norm_num)

theorem sGlobal54_hz107 {c : ℝ} (hc : B (123 / 200) (31 / 50) c) : B (5751252936620638161 / 62500000000000000) (22592180942275408567 / 31250000000000000) (s3U 12225 46 maskSlack c) := by
    convert (sGlobal54_hz106 hc) using 1 <;>
      norm_num [s3U] <;> ring

theorem sGlobal54_hz108 {c : ℝ} (hc : B (123 / 200) (31 / 50) c) : B (-606697712559990481543 / 250000000000000000) (-1176364697587780923089 / 500000000000000000) ((s3Cpp 12225 c) - (s3rpp 12225 46)) := bsub (sGlobal54_hz90 hc) sGlobal54_hz37 (by norm_num) (by norm_num)

theorem sGlobal54_hz109 {c : ℝ} (hc : B (123 / 200) (31 / 50) c) : B (-606697712559990481543 / 250000000000000000) (-1176364697587780923089 / 500000000000000000) (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ)) := bweaken (bmin (sGlobal54_hz108 hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem sGlobal54_hz110 {c : ℝ} (hc : B (123 / 200) (31 / 50) c) : B (-226172328371901984699 / 125000000000000000) (-175045225838267296153 / 100000000000000000) ((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) := bmul (sGlobal54_hz76 hc) (sGlobal54_hz109 hc) (by norm_num) (by norm_num)

theorem sGlobal54_hz111 {c : ℝ} (hc : B (123 / 200) (31 / 50) c) : B (-113087104881247515867 / 62500000000000000) (-875233654753708668903 / 500000000000000000) (((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) := bsub (sGlobal54_hz110 hc) sGlobal54_hz104 (by norm_num) (by norm_num)

theorem sGlobal54_hz112 {c : ℝ} (hc : B (123 / 200) (31 / 50) c) : B (-115493171972130282743 / 62500000000000000) (-1788964382958664607937 / 1000000000000000000) ((((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) - (s3rs 12225 46 maskSlack)) := bsub (sGlobal54_hz111 hc) sGlobal54_hz29 (by norm_num) (by norm_num)

theorem sGlobal54_hz113 {c : ℝ} (hc : B (123 / 200) (31 / 50) c) : B (-115493171972130282743 / 62500000000000000) (-1788964382958664607937 / 1000000000000000000) (s3L 12225 46 maskSlack c) := by
    convert (sGlobal54_hz112 hc) using 1 <;>
      norm_num [s3L] <;> ring

theorem sGlobal54_hz114 {c : ℝ} (hc : B (123 / 200) (31 / 50) c) : B 0 (22592180942275408567 / 31250000000000000) |(s3U 12225 46 maskSlack c)| := bweaken (babs (sGlobal54_hz107 hc)) (by norm_num) (by norm_num)

theorem sGlobal54_hz115 {c : ℝ} (hc : B (123 / 200) (31 / 50) c) : B 0 (115493171972130282743 / 62500000000000000) |(s3L 12225 46 maskSlack c)| := bweaken (babs (sGlobal54_hz113 hc)) (by norm_num) (by norm_num)

theorem sGlobal54_hz116 {c : ℝ} (hc : B (123 / 200) (31 / 50) c) : B 0 (115493171972130282743 / 62500000000000000) (max |(s3U 12225 46 maskSlack c)| |(s3L 12225 46 maskSlack c)|) := bweaken (bmax (sGlobal54_hz114 hc) (sGlobal54_hz115 hc)) (by norm_num) (by norm_num)

theorem sGlobal54_hz117 {c : ℝ} (hc : B (123 / 200) (31 / 50) c) : B 0 (115493171972130282743 / 62500000000000000) (s3nks 12225 46 maskSlack c) := by
    convert (sGlobal54_hz116 hc) using 1 <;>
      norm_num [s3nks] <;> ring

theorem sGlobal54 {c : ℝ} (hc : B (123 / 200) (31 / 50) c) :
    0 < s3am 12225 46 ∧ 0 ≤ s3dm 12225 46 c ∧
    s3dm 12225 46 c ^ 2 ≤ 2 * s3ap 12225 46 ^ 2 ∧ s3c1 12225 46 c < 1 ∧
    0 ≤ s3Cpa 12225 c - s3r1 12225 46 ∧
    s3e0 12225 46 ≤ (s3Cpa 12225 c - s3r1 12225 46) / s3ap 12225 46 ∧
    s3nks 12225 46 maskSlack c ≤ 12225 * (151157 / 1000000) := by

  refine ⟨lt_of_lt_of_le (by norm_num) sGlobal54_hz14.1,
    le_trans (by norm_num) (sGlobal54_hz64 hc).1, ?_,
    lt_of_le_of_lt (sGlobal54_hz72 hc).2 (by norm_num), ?_, ?_,
    le_trans (sGlobal54_hz117 hc).2 (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (sGlobal54_hz64 hc).1) (sGlobal54_hz64 hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) sGlobal54_hz9.1 2
    nlinarith only [h1, h2]
  · linarith only [(sGlobal54_hz84 hc).1, sGlobal54_hz33.2]
  · have hap : 0 < s3ap 12225 46 := lt_of_lt_of_le (by norm_num) sGlobal54_hz9.1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul sGlobal54_hz16.2 sGlobal54_hz9.2 (le_trans (by norm_num) sGlobal54_hz9.1) (by norm_num)
    linarith only [h, (sGlobal54_hz84 hc).1, sGlobal54_hz33.2]

end BstLean.Part255
