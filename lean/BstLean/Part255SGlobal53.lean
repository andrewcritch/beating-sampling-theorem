import BstLean.Part255SGlobal49
import BstLean.Part255Numeric10
namespace BstLean.Part255
open Real BstLean.Part130 BstLean.Part182 BstLean.Part197 BstLean.Part246
theorem sGlobal53_hz0 : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal53_hz1 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) ((√(23 : ℝ)) / (12225 : ℝ)) := bdiv sGlobal53_hz0 (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal53_hz2 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) maskSlack := by
    convert sGlobal53_hz1 using 1 <;>
      norm_num [maskSlack] <;> ring

theorem sGlobal53_hz3 : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal53_hz4 : B (6395294793910793 / 500000000000000000) (12790589587821587 / 1000000000000000000) (√((2 / 12225) : ℝ)) := bsqrt (bpoint ((2 / 12225) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal53_hz5 : B (7230130686979 / 62500000000000000) (23136418198333 / 200000000000000000) (√((2 / 149450625) : ℝ)) := bsqrt (bpoint ((2 / 149450625) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal53_hz6 : B (2211334438749598093 / 20000000000000000) (110566721937479904651 / 1000000000000000000) (√(12225 : ℝ)) := bsqrt (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal53_hz7 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))) := bmul sGlobal53_hz3 sGlobal53_hz4 (by norm_num) (by norm_num)

theorem sGlobal53_hz8 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) ((√(12225 : ℝ)) + ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := badd sGlobal53_hz6 sGlobal53_hz7 (by norm_num) (by norm_num)

theorem sGlobal53_hz9 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) (s3ap 12225 46) := by
    convert sGlobal53_hz8 using 1 <;>
      norm_num [s3ap, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal53_hz10 : B (163599182004089 / 1000000000000000000) (16359918200409 / 100000000000000000) ((2 : ℝ) / (12225 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal53_hz11 : B (1222499983640081799591 / 100000000000000000) (12224999836400817995911 / 1000000000000000000) ((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ))) := bsub (bpoint (12225 : ℝ)) sGlobal53_hz10 (by norm_num) (by norm_num)

theorem sGlobal53_hz12 : B (110566721197658827907 / 1000000000000000000) (27641680299414706977 / 250000000000000000) (√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) := bsqrt sGlobal53_hz11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal53_hz13 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) ((√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) - ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bsub sGlobal53_hz12 sGlobal53_hz7 (by norm_num) (by norm_num)

theorem sGlobal53_hz14 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) (s3am 12225 46) := by
    convert sGlobal53_hz13 using 1 <;>
      norm_num [s3am, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal53_hz15 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√((2 / 12225) : ℝ)) * (√(92 : ℝ))) := bmul sGlobal53_hz4 sGlobal53_hz3 (by norm_num) (by norm_num)

theorem sGlobal53_hz16 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) (s3e0 12225 46) := by
    convert sGlobal53_hz15 using 1 <;>
      norm_num [s3e0, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal53_hz17 : B (250196148528560847 / 500000000000000000) (100078459411424339 / 200000000000000000) (((1 / 2) : ℝ) + maskSlack) := badd (bpoint ((1 / 2) : ℝ)) sGlobal53_hz2 (by norm_num) (by norm_num)

theorem sGlobal53_hz18 : B (59827153232297998295487 / 800000000000000) (23930861292919199366019 / 320000000000000) ((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack)) := bmul (bpoint (149450625 : ℝ)) sGlobal53_hz17 (by norm_num) (by norm_num)

theorem sGlobal53_hz19 : B (1729554180017180009583 / 200000000000000000) (8647770900085900056557 / 1000000000000000000) (√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) := bsqrt sGlobal53_hz18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal53_hz20 : B (4328681281566262743499 / 500000000000000000) (8657362563132525495641 / 1000000000000000000) ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))) := badd sGlobal53_hz19 sGlobal53_hz3 (by norm_num) (by norm_num)

theorem sGlobal53_hz21 : B (110732771457999278473 / 1000000000000000000) (55366385728999643621 / 500000000000000000) ((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ)))) := bmul sGlobal53_hz4 sGlobal53_hz20 (by norm_num) (by norm_num)

theorem sGlobal53_hz22 : B (209099159 / 15625000000000000) (13382346177 / 1000000000000000000) ((2 : ℝ) / (149450625 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (149450625 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal53_hz23 : B (2452349334953899930479 / 200000000000000000) (12261746674769501594427 / 1000000000000000000) (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2) := bsq sGlobal53_hz21 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal53_hz24 : B (82045469362091 / 500000000000000000) (32818187747289 / 200000000000000000) (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2)) := bmul sGlobal53_hz22 sGlobal53_hz23 (by norm_num) (by norm_num)

theorem sGlobal53_hz25 : B (82045469362091 / 250000000000000000) (32818187747289 / 100000000000000000) ((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) := bmul (bpoint (2 : ℝ)) sGlobal53_hz24 (by norm_num) (by norm_num)

theorem sGlobal53_hz26 : B (117258080744995992792057 / 1000000000000000000) (58629040372497996396029 / 500000000000000000) (√(13749457500 : ℝ)) := bsqrt (bpoint (13749457500 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal53_hz27 : B (117304080744995992792057 / 1000000000000000000) (58652040372497996396029 / 500000000000000000) ((√(13749457500 : ℝ)) + (46 : ℝ)) := badd sGlobal53_hz26 (bpoint (46 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal53_hz28 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal53_hz25 sGlobal53_hz27 (by norm_num) (by norm_num)

theorem sGlobal53_hz29 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (s3rs 12225 46 maskSlack) := by
    convert sGlobal53_hz28 using 1 <;>
      norm_num [s3rs, s3pp, s3K, mA, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal53_hz30 : B (490797546012267 / 1000000000000000000) (49079754601227 / 100000000000000000) ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (3 : ℝ)) sGlobal53_hz10 (by norm_num) (by norm_num)

theorem sGlobal53_hz31 : B (490797546012267 / 500000000000000000) (49079754601227 / 50000000000000000) ((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal53_hz30 (by norm_num) (by norm_num)

theorem sGlobal53_hz32 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal53_hz31 sGlobal53_hz27 (by norm_num) (by norm_num)

theorem sGlobal53_hz33 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (s3r1 12225 46) := by
    convert sGlobal53_hz32 using 1 <;>
      norm_num [s3r1, mA] <;> ring

theorem sGlobal53_hz34 : B (163599182004089 / 500000000000000000) (16359918200409 / 50000000000000000) ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (2 : ℝ)) sGlobal53_hz10 (by norm_num) (by norm_num)

theorem sGlobal53_hz35 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal53_hz34 (by norm_num) (by norm_num)

theorem sGlobal53_hz36 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal53_hz35 sGlobal53_hz27 (by norm_num) (by norm_num)

theorem sGlobal53_hz37 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (s3rpp 12225 46) := by
    convert sGlobal53_hz36 using 1 <;>
      norm_num [s3rpp, mA] <;> ring

theorem sGlobal53_hz38 {c : ℝ} (hc : B (61 / 100) (123 / 200) c) : B (61 / 100) (123 / 200) c := hc

theorem sGlobal53_hz39 : B (28353222881079303 / 40000000000000000) (708830572026982599 / 1000000000000000000) (kdot ((61 / 100))) := by
    constructor
    · apply bkdot_lower (q := (492174790948013201 / 1000000000000000000)) (a := (457367867934986991 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (1230436977370033 / 2500000000000000)) (a := (114341966983746739 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal53_hz40 : B (3721 / 10000) (3721 / 10000) (((61 / 100) : ℝ)^2) := bsq (bpoint ((61 / 100) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal53_hz41 : B (6279 / 10000) (6279 / 10000) ((1 : ℝ) - (((61 / 100) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal53_hz40 (by norm_num) (by norm_num)

theorem sGlobal53_hz42 : B (792401413426301253 / 1000000000000000000) (396200706713150627 / 500000000000000000) (√((1 : ℝ) - (((61 / 100) : ℝ)^2))) := bsqrt sGlobal53_hz41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal53_hz43 : B (252229203719600809 / 1000000000000000000) (25222920371960081 / 100000000000000000) ((√((1 : ℝ) - (((61 / 100) : ℝ)^2))) / Real.pi) := bdiv sGlobal53_hz42 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal53_hz44 : B (43238664893645937 / 100000000000000000) (216193324468229693 / 500000000000000000) (((61 / 100) : ℝ) * (kdot ((61 / 100)))) := bmul (bpoint ((61 / 100) : ℝ)) sGlobal53_hz39 (by norm_num) (by norm_num)

theorem sGlobal53_hz45 : B (684615852656060179 / 1000000000000000000) (171153963164015049 / 250000000000000000) (((√((1 : ℝ) - (((61 / 100) : ℝ)^2))) / Real.pi) + (((61 / 100) : ℝ) * (kdot ((61 / 100))))) := badd sGlobal53_hz43 sGlobal53_hz44 (by norm_num) (by norm_num)

theorem sGlobal53_hz46 : B (684615852656060179 / 1000000000000000000) (171153963164015049 / 250000000000000000) (kappa ((61 / 100))) := by rw [kappa_eq]; exact sGlobal53_hz45

theorem sGlobal53_hz47 : B (710844001606924669 / 1000000000000000000) (355422000803462343 / 500000000000000000) (kdot ((123 / 200))) := by
    constructor
    · apply bkdot_lower (q := (244126039618501659 / 500000000000000000)) (a := (227102590073276879 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (488252079237003317 / 1000000000000000000)) (a := (227102590073276867 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal53_hz48 : B (15129 / 40000) (15129 / 40000) (((123 / 200) : ℝ)^2) := bsq (bpoint ((123 / 200) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal53_hz49 : B (24871 / 40000) (24871 / 40000) ((1 : ℝ) - (((123 / 200) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal53_hz48 (by norm_num) (by norm_num)

theorem sGlobal53_hz50 : B (788527107967760357 / 1000000000000000000) (394263553983880179 / 500000000000000000) (√((1 : ℝ) - (((123 / 200) : ℝ)^2))) := bsqrt sGlobal53_hz49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal53_hz51 : B (250995973990051417 / 1000000000000000000) (125497986995025709 / 500000000000000000) ((√((1 : ℝ) - (((123 / 200) : ℝ)^2))) / Real.pi) := bdiv sGlobal53_hz50 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal53_hz52 : B (437169060988258671 / 1000000000000000000) (218584530494129341 / 500000000000000000) (((123 / 200) : ℝ) * (kdot ((123 / 200)))) := bmul (bpoint ((123 / 200) : ℝ)) sGlobal53_hz47 (by norm_num) (by norm_num)

theorem sGlobal53_hz53 : B (86020629372288761 / 125000000000000000) (6881650349783101 / 10000000000000000) (((√((1 : ℝ) - (((123 / 200) : ℝ)^2))) / Real.pi) + (((123 / 200) : ℝ) * (kdot ((123 / 200))))) := badd sGlobal53_hz51 sGlobal53_hz52 (by norm_num) (by norm_num)

theorem sGlobal53_hz54 : B (86020629372288761 / 125000000000000000) (6881650349783101 / 10000000000000000) (kappa ((123 / 200))) := by rw [kappa_eq]; exact sGlobal53_hz53

theorem sGlobal53_hz55 {c : ℝ} (hc : B (61 / 100) (123 / 200) c) : B (684615852656060179 / 1000000000000000000) (6881650349783101 / 10000000000000000) (kappa c) := bkappa (sGlobal53_hz38 hc) (by norm_num) (by norm_num) sGlobal53_hz46.1 sGlobal53_hz54.2

theorem sGlobal53_hz56 : B 24450 24450 ((2 : ℝ) * (12225 : ℝ)) := bmul (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal53_hz57 {c : ℝ} (hc : B (61 / 100) (123 / 200) c) : B (3118349650216899 / 10000000000000000) (315384147343939821 / 1000000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (sGlobal53_hz55 hc) (by norm_num) (by norm_num)

theorem sGlobal53_hz58 {c : ℝ} (hc : B (61 / 100) (123 / 200) c) : B (1524872978956063611 / 200000000000000) (154222848051186572469 / 20000000000000000) (((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) := bmul sGlobal53_hz56 (sGlobal53_hz57 hc) (by norm_num) (by norm_num)

theorem sGlobal53_hz59 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (4 : ℝ)) sGlobal53_hz10 (by norm_num) (by norm_num)

theorem sGlobal53_hz60 {c : ℝ} (hc : B (61 / 100) (123 / 200) c) : B (95304553004794875483 / 12500000000000000) (3855570874081300303547 / 500000000000000000) ((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bsub (sGlobal53_hz58 hc) sGlobal53_hz59 (by norm_num) (by norm_num)

theorem sGlobal53_hz61 {c : ℝ} (hc : B (61 / 100) (123 / 200) c) : B (87317605558006399323 / 1000000000000000000) (5488319182933893343 / 62500000000000000) (√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) := bsqrt (sGlobal53_hz60 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal53_hz62 : B (30670756373515103 / 125000000000000000) (122683025494060423 / 500000000000000000) ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal53_hz7 (by norm_num) (by norm_num)

theorem sGlobal53_hz63 {c : ℝ} (hc : B (61 / 100) (123 / 200) c) : B (87072239507018278477 / 1000000000000000000) (10945967609494271583 / 125000000000000000) ((√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) - ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))))) := bsub (sGlobal53_hz61 hc) sGlobal53_hz62 (by norm_num) (by norm_num)

theorem sGlobal53_hz64 {c : ℝ} (hc : B (61 / 100) (123 / 200) c) : B (87072239507018278477 / 1000000000000000000) (10945967609494271583 / 125000000000000000) (s3dm 12225 46 c) := by
    convert (sGlobal53_hz63 hc) using 1 <;>
      norm_num [s3dm, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal53_hz65 : B (6126072185528622723889 / 500000000000000000) (2450428874211449090087 / 200000000000000000) ((s3ap 12225 46)^2) := bsq sGlobal53_hz9 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal53_hz66 : B (6126072185528622723889 / 250000000000000000) (2450428874211449090087 / 100000000000000000) ((2 : ℝ) * ((s3ap 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal53_hz65 (by norm_num) (by norm_num)

theorem sGlobal53_hz67 {c : ℝ} (hc : B (61 / 100) (123 / 200) c) : B (7581574892767554698903 / 1000000000000000000) (7668109242118255254809 / 1000000000000000000) ((s3dm 12225 46 c)^2) := bsq (sGlobal53_hz64 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal53_hz68 {c : ℝ} (hc : B (61 / 100) (123 / 200) c) : B (16836179499996235640747 / 1000000000000000000) (16922713849346936201967 / 1000000000000000000) (((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) := bsub sGlobal53_hz66 (sGlobal53_hz67 hc) (by norm_num) (by norm_num)

theorem sGlobal53_hz69 : B (1524735695971823534271 / 125000000000000000) (609894278388729413841 / 50000000000000000) ((s3am 12225 46)^2) := bsq sGlobal53_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal53_hz70 : B (1524735695971823534271 / 62500000000000000) (609894278388729413841 / 25000000000000000) ((2 : ℝ) * ((s3am 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal53_hz69 (by norm_num) (by norm_num)

theorem sGlobal53_hz71 {c : ℝ} (hc : B (61 / 100) (123 / 200) c) : B (69012696530271963 / 100000000000000000) (138734813958697901 / 200000000000000000) ((((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) / ((2 : ℝ) * ((s3am 12225 46)^2))) := bdiv (sGlobal53_hz68 hc) sGlobal53_hz70 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal53_hz72 {c : ℝ} (hc : B (61 / 100) (123 / 200) c) : B (69012696530271963 / 100000000000000000) (138734813958697901 / 200000000000000000) (s3c1 12225 46 c) := by
    convert (sGlobal53_hz71 hc) using 1 <;>
      norm_num [s3c1] <;> ring

theorem sGlobal53_hz73 {c : ℝ} (hc : B (61 / 100) (123 / 200) c) : B (28353222881079303 / 40000000000000000) (355422000803462343 / 500000000000000000) (kdot c) := bkdot (sGlobal53_hz38 hc) sGlobal53_hz39.1 sGlobal53_hz47.2

theorem sGlobal53_hz74 : B (742445333953168281 / 1000000000000000000) (185611333488292071 / 250000000000000000) (kdot ((69012696530271963 / 100000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (214092883568251591 / 500000000000000000)) (a := (20228296168762477 / 50000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (428185767136503181 / 1000000000000000000)) (a := (202282961687624769 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal53_hz75 : B (372004587942008807 / 500000000000000000) (46500573492751101 / 62500000000000000) (kdot ((138734813958697901 / 200000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (212640980212039943 / 500000000000000000)) (a := (40210944621458357 / 100000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (85056392084815977 / 200000000000000000)) (a := (25131840388411473 / 62500000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal53_hz76 {c : ℝ} (hc : B (61 / 100) (123 / 200) c) : B (742445333953168281 / 1000000000000000000) (46500573492751101 / 62500000000000000) (kdot (s3c1 12225 46 c)) := bkdot (sGlobal53_hz72 hc) sGlobal53_hz74.1 sGlobal53_hz75.2

theorem sGlobal53_hz77 {c : ℝ} (hc : B (61 / 100) (123 / 200) c) : B (3721 / 10000) (15129 / 40000) (c^2) := bsq (sGlobal53_hz38 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal53_hz78 {c : ℝ} (hc : B (61 / 100) (123 / 200) c) : B (24871 / 40000) (6279 / 10000) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (sGlobal53_hz77 hc) (by norm_num) (by norm_num)

theorem sGlobal53_hz79 {c : ℝ} (hc : B (61 / 100) (123 / 200) c) : B (788527107967760357 / 1000000000000000000) (396200706713150627 / 500000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (sGlobal53_hz78 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal53_hz80 : B (39119999999999765769 / 1600000000000000) (3912000000000000489 / 160000000000000) ((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (149450625 : ℝ)) sGlobal53_hz10 (by norm_num) (by norm_num)

theorem sGlobal53_hz81 {c : ℝ} (hc : B (61 / 100) (123 / 200) c) : B (558932120999569823 / 1000000000000000000) (281636895799467541 / 500000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (sGlobal53_hz79 hc) (sGlobal53_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal53_hz82 {c : ℝ} (hc : B (61 / 100) (123 / 200) c) : B (13665890358439400347831 / 1000000000000000000) (6886022102296982238203 / 500000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) := bmul sGlobal53_hz80 (sGlobal53_hz81 hc) (by norm_num) (by norm_num)

theorem sGlobal53_hz83 {c : ℝ} (hc : B (61 / 100) (123 / 200) c) : B (1366589035843940034783 / 200000000000000000) (6886022102296982238203 / 1000000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) / (2 : ℝ)) := bdiv (sGlobal53_hz82 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal53_hz84 {c : ℝ} (hc : B (61 / 100) (123 / 200) c) : B (1366589035843940034783 / 200000000000000000) (6886022102296982238203 / 1000000000000000000) (s3Cpa 12225 c) := by
    convert (sGlobal53_hz83 hc) using 1 <;>
      norm_num [s3Cpa, mA] <;> ring

theorem sGlobal53_hz85 {c : ℝ} (hc : B (61 / 100) (123 / 200) c) : B (250995973990051417 / 1000000000000000000) (25222920371960081 / 100000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (sGlobal53_hz79 hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal53_hz86 {c : ℝ} (hc : B (61 / 100) (123 / 200) c) : B (43238664893645937 / 100000000000000000) (218584530494129341 / 500000000000000000) (c * (kdot c)) := bmul (sGlobal53_hz38 hc) (sGlobal53_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal53_hz87 {c : ℝ} (hc : B (61 / 100) (123 / 200) c) : B (-37234617399641453 / 200000000000000000) (-562992016302683 / 3125000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (sGlobal53_hz85 hc) (sGlobal53_hz86 hc) (by norm_num) (by norm_num)

theorem sGlobal53_hz88 {c : ℝ} (hc : B (61 / 100) (123 / 200) c) : B (-2275965988553084099121 / 500000000000000000) (-4404849535552165417963 / 1000000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) := bmul sGlobal53_hz80 (sGlobal53_hz87 hc) (by norm_num) (by norm_num)

theorem sGlobal53_hz89 {c : ℝ} (hc : B (61 / 100) (123 / 200) c) : B (-2275965988553084099121 / 1000000000000000000) (-2202424767776082708981 / 1000000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) / (2 : ℝ)) := bdiv (sGlobal53_hz88 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal53_hz90 {c : ℝ} (hc : B (61 / 100) (123 / 200) c) : B (-2275965988553084099121 / 1000000000000000000) (-2202424767776082708981 / 1000000000000000000) (s3Cpp 12225 c) := by
    convert (sGlobal53_hz89 hc) using 1 <;>
      norm_num [s3Cpp, mA] <;> ring

theorem sGlobal53_hz91 {c : ℝ} (hc : B (61 / 100) (123 / 200) c) : B (1737022572288359470579 / 250000000000000000) (7001167212230720650429 / 1000000000000000000) ((s3Cpa 12225 c) + (s3r1 12225 46)) := badd (sGlobal53_hz84 hc) sGlobal53_hz33 (by norm_num) (by norm_num)

theorem sGlobal53_hz92 {c : ℝ} (hc : B (61 / 100) (123 / 200) c) : B (31455252832762531289 / 500000000000000000) (63391083195609069921 / 1000000000000000000) (((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) := bdiv (sGlobal53_hz91 hc) sGlobal53_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal53_hz93 {c : ℝ} (hc : B (61 / 100) (123 / 200) c) : B (6303318869101912299 / 100000000000000000) (7939220777637891293 / 125000000000000000) ((((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) + (s3e0 12225 46)) := badd (sGlobal53_hz92 hc) sGlobal53_hz16 (by norm_num) (by norm_num)

theorem sGlobal53_hz94 {c : ℝ} (hc : B (61 / 100) (123 / 200) c) : B (6303318869101912299 / 100000000000000000) (7939220777637891293 / 125000000000000000) (s3Lam 12225 46 c) := by
    convert (sGlobal53_hz93 hc) using 1 <;>
      norm_num [s3Lam] <;> ring

theorem sGlobal53_hz95 {c : ℝ} (hc : B (61 / 100) (123 / 200) c) : B (-2199202581930592293521 / 1000000000000000000) (-2125661361153590434163 / 1000000000000000000) ((s3Cpp 12225 c) + (s3rpp 12225 46)) := badd (sGlobal53_hz90 hc) sGlobal53_hz37 (by norm_num) (by norm_num)

theorem sGlobal53_hz96 {c : ℝ} (hc : B (61 / 100) (123 / 200) c) : B (-204528362573022962893 / 125000000000000000) (-1062830680576795217081 / 1000000000000000000) (if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) := bweaken (bfirst (sGlobal53_hz95 hc) (sGlobal53_hz76 hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem sGlobal53_hz97 {c : ℝ} (hc : B (61 / 100) (123 / 200) c) : B (794636575311524211911 / 200000000000000000) (100849962489723525349 / 25000000000000000) ((s3Lam 12225 46 c)^2) := bsq (sGlobal53_hz94 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal53_hz98 {c : ℝ} (hc : B (61 / 100) (123 / 200) c) : B (7441800441217831 / 15625000000000000) (481183715103862949 / 1000000000000000000) ((s3c1 12225 46 c)^2) := bsq (sGlobal53_hz72 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal53_hz99 {c : ℝ} (hc : B (61 / 100) (123 / 200) c) : B (518816284896137051 / 1000000000000000000) (8183199558782169 / 15625000000000000) ((1 : ℝ) - ((s3c1 12225 46 c)^2)) := bsub (bpoint (1 : ℝ)) (sGlobal53_hz98 hc) (by norm_num) (by norm_num)

theorem sGlobal53_hz100 {c : ℝ} (hc : B (61 / 100) (123 / 200) c) : B (720289028721205117 / 1000000000000000000) (7236883111962351 / 10000000000000000) (√((1 : ℝ) - ((s3c1 12225 46 c)^2))) := bsqrt (sGlobal53_hz99 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal53_hz101 {c : ℝ} (hc : B (61 / 100) (123 / 200) c) : B (2262854721091865579 / 1000000000000000000) (454706776388579261 / 200000000000000000) (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))) := bmul pi_mem (sGlobal53_hz100 hc) (by norm_num) (by norm_num)

theorem sGlobal53_hz102 {c : ℝ} (hc : B (61 / 100) (123 / 200) c) : B (1747580235383276486531 / 1000000000000000000) (356540653006876966569 / 200000000000000000) (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2))))) := bdiv (sGlobal53_hz97 hc) (sGlobal53_hz101 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal53_hz103 {c : ℝ} (hc : B (61 / 100) (123 / 200) c) : B (111353334799092783387 / 1000000000000000000) (179968146114397403941 / 250000000000000000) ((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) := badd (sGlobal53_hz96 hc) (sGlobal53_hz102 hc) (by norm_num) (by norm_num)

theorem sGlobal53_hz104 : B (3762781186094069 / 250000000000000000) (376278118609407 / 25000000000000000) ((s3e0 12225 46)^2) := bsq sGlobal53_hz16 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal53_hz105 {c : ℝ} (hc : B (61 / 100) (123 / 200) c) : B (111368385923837159663 / 1000000000000000000) (179971908895583498011 / 250000000000000000) (((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) := badd (sGlobal53_hz103 hc) sGlobal53_hz104 (by norm_num) (by norm_num)

theorem sGlobal53_hz106 {c : ℝ} (hc : B (61 / 100) (123 / 200) c) : B (74932729687542214897 / 500000000000000000) (37919235451822913103 / 50000000000000000) ((((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) + (s3rs 12225 46 maskSlack)) := badd (sGlobal53_hz105 hc) sGlobal53_hz29 (by norm_num) (by norm_num)

theorem sGlobal53_hz107 {c : ℝ} (hc : B (61 / 100) (123 / 200) c) : B (74932729687542214897 / 500000000000000000) (37919235451822913103 / 50000000000000000) (s3U 12225 46 maskSlack c) := by
    convert (sGlobal53_hz106 hc) using 1 <;>
      norm_num [s3U] <;> ring

theorem sGlobal53_hz108 {c : ℝ} (hc : B (61 / 100) (123 / 200) c) : B (-2352729395175576373939 / 1000000000000000000) (-2279188174398574514581 / 1000000000000000000) ((s3Cpp 12225 c) - (s3rpp 12225 46)) := bsub (sGlobal53_hz90 hc) sGlobal53_hz37 (by norm_num) (by norm_num)

theorem sGlobal53_hz109 {c : ℝ} (hc : B (61 / 100) (123 / 200) c) : B (-2352729395175576373939 / 1000000000000000000) (-2279188174398574514581 / 1000000000000000000) (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ)) := bweaken (bmin (sGlobal53_hz108 hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem sGlobal53_hz110 {c : ℝ} (hc : B (61 / 100) (123 / 200) c) : B (-1750452258382683789141 / 1000000000000000000) (-169217262528346160447 / 100000000000000000) ((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) := bmul (sGlobal53_hz76 hc) (sGlobal53_hz109 hc) (by norm_num) (by norm_num)

theorem sGlobal53_hz111 {c : ℝ} (hc : B (61 / 100) (123 / 200) c) : B (-1750467309507428165421 / 1000000000000000000) (-846093838204102990373 / 500000000000000000) (((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) := bsub (sGlobal53_hz110 hc) sGlobal53_hz104 (by norm_num) (by norm_num)

theorem sGlobal53_hz112 {c : ℝ} (hc : B (61 / 100) (123 / 200) c) : B (-1788964382961552435437 / 1000000000000000000) (-1730684749859453250877 / 1000000000000000000) ((((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) - (s3rs 12225 46 maskSlack)) := bsub (sGlobal53_hz111 hc) sGlobal53_hz29 (by norm_num) (by norm_num)

theorem sGlobal53_hz113 {c : ℝ} (hc : B (61 / 100) (123 / 200) c) : B (-1788964382961552435437 / 1000000000000000000) (-1730684749859453250877 / 1000000000000000000) (s3L 12225 46 maskSlack c) := by
    convert (sGlobal53_hz112 hc) using 1 <;>
      norm_num [s3L] <;> ring

theorem sGlobal53_hz114 {c : ℝ} (hc : B (61 / 100) (123 / 200) c) : B 0 (37919235451822913103 / 50000000000000000) |(s3U 12225 46 maskSlack c)| := bweaken (babs (sGlobal53_hz107 hc)) (by norm_num) (by norm_num)

theorem sGlobal53_hz115 {c : ℝ} (hc : B (61 / 100) (123 / 200) c) : B 0 (1788964382961552435437 / 1000000000000000000) |(s3L 12225 46 maskSlack c)| := bweaken (babs (sGlobal53_hz113 hc)) (by norm_num) (by norm_num)

theorem sGlobal53_hz116 {c : ℝ} (hc : B (61 / 100) (123 / 200) c) : B 0 (1788964382961552435437 / 1000000000000000000) (max |(s3U 12225 46 maskSlack c)| |(s3L 12225 46 maskSlack c)|) := bweaken (bmax (sGlobal53_hz114 hc) (sGlobal53_hz115 hc)) (by norm_num) (by norm_num)

theorem sGlobal53_hz117 {c : ℝ} (hc : B (61 / 100) (123 / 200) c) : B 0 (1788964382961552435437 / 1000000000000000000) (s3nks 12225 46 maskSlack c) := by
    convert (sGlobal53_hz116 hc) using 1 <;>
      norm_num [s3nks] <;> ring

theorem sGlobal53 {c : ℝ} (hc : B (61 / 100) (123 / 200) c) :
    0 < s3am 12225 46 ∧ 0 ≤ s3dm 12225 46 c ∧
    s3dm 12225 46 c ^ 2 ≤ 2 * s3ap 12225 46 ^ 2 ∧ s3c1 12225 46 c < 1 ∧
    0 ≤ s3Cpa 12225 c - s3r1 12225 46 ∧
    s3e0 12225 46 ≤ (s3Cpa 12225 c - s3r1 12225 46) / s3ap 12225 46 ∧
    s3nks 12225 46 maskSlack c ≤ 12225 * (146337 / 1000000) := by

  refine ⟨lt_of_lt_of_le (by norm_num) sGlobal53_hz14.1,
    le_trans (by norm_num) (sGlobal53_hz64 hc).1, ?_,
    lt_of_le_of_lt (sGlobal53_hz72 hc).2 (by norm_num), ?_, ?_,
    le_trans (sGlobal53_hz117 hc).2 (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (sGlobal53_hz64 hc).1) (sGlobal53_hz64 hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) sGlobal53_hz9.1 2
    nlinarith only [h1, h2]
  · linarith only [(sGlobal53_hz84 hc).1, sGlobal53_hz33.2]
  · have hap : 0 < s3ap 12225 46 := lt_of_lt_of_le (by norm_num) sGlobal53_hz9.1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul sGlobal53_hz16.2 sGlobal53_hz9.2 (le_trans (by norm_num) sGlobal53_hz9.1) (by norm_num)
    linarith only [h, (sGlobal53_hz84 hc).1, sGlobal53_hz33.2]

end BstLean.Part255
