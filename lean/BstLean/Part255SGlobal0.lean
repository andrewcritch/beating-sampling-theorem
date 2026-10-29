import BstLean.Part255Numeric51C
import BstLean.Part255Numeric10
namespace BstLean.Part255
open Real BstLean.Part130 BstLean.Part182 BstLean.Part197 BstLean.Part246
theorem sGlobal0_hz0 : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal0_hz1 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) ((√(23 : ℝ)) / (12225 : ℝ)) := bdiv sGlobal0_hz0 (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal0_hz2 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) maskSlack := by
    convert sGlobal0_hz1 using 1 <;>
      norm_num [maskSlack] <;> ring

theorem sGlobal0_hz3 : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal0_hz4 : B (6395294793910793 / 500000000000000000) (12790589587821587 / 1000000000000000000) (√((2 / 12225) : ℝ)) := bsqrt (bpoint ((2 / 12225) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal0_hz5 : B (7230130686979 / 62500000000000000) (23136418198333 / 200000000000000000) (√((2 / 149450625) : ℝ)) := bsqrt (bpoint ((2 / 149450625) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal0_hz6 : B (2211334438749598093 / 20000000000000000) (110566721937479904651 / 1000000000000000000) (√(12225 : ℝ)) := bsqrt (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal0_hz7 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))) := bmul sGlobal0_hz3 sGlobal0_hz4 (by norm_num) (by norm_num)

theorem sGlobal0_hz8 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) ((√(12225 : ℝ)) + ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := badd sGlobal0_hz6 sGlobal0_hz7 (by norm_num) (by norm_num)

theorem sGlobal0_hz9 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) (s3ap 12225 46) := by
    convert sGlobal0_hz8 using 1 <;>
      norm_num [s3ap, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal0_hz10 : B (163599182004089 / 1000000000000000000) (16359918200409 / 100000000000000000) ((2 : ℝ) / (12225 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal0_hz11 : B (1222499983640081799591 / 100000000000000000) (12224999836400817995911 / 1000000000000000000) ((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ))) := bsub (bpoint (12225 : ℝ)) sGlobal0_hz10 (by norm_num) (by norm_num)

theorem sGlobal0_hz12 : B (110566721197658827907 / 1000000000000000000) (27641680299414706977 / 250000000000000000) (√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) := bsqrt sGlobal0_hz11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal0_hz13 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) ((√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) - ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bsub sGlobal0_hz12 sGlobal0_hz7 (by norm_num) (by norm_num)

theorem sGlobal0_hz14 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) (s3am 12225 46) := by
    convert sGlobal0_hz13 using 1 <;>
      norm_num [s3am, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal0_hz15 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√((2 / 12225) : ℝ)) * (√(92 : ℝ))) := bmul sGlobal0_hz4 sGlobal0_hz3 (by norm_num) (by norm_num)

theorem sGlobal0_hz16 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) (s3e0 12225 46) := by
    convert sGlobal0_hz15 using 1 <;>
      norm_num [s3e0, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal0_hz17 : B (250196148528560847 / 500000000000000000) (100078459411424339 / 200000000000000000) (((1 / 2) : ℝ) + maskSlack) := badd (bpoint ((1 / 2) : ℝ)) sGlobal0_hz2 (by norm_num) (by norm_num)

theorem sGlobal0_hz18 : B (59827153232297998295487 / 800000000000000) (23930861292919199366019 / 320000000000000) ((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack)) := bmul (bpoint (149450625 : ℝ)) sGlobal0_hz17 (by norm_num) (by norm_num)

theorem sGlobal0_hz19 : B (1729554180017180009583 / 200000000000000000) (8647770900085900056557 / 1000000000000000000) (√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) := bsqrt sGlobal0_hz18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal0_hz20 : B (4328681281566262743499 / 500000000000000000) (8657362563132525495641 / 1000000000000000000) ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))) := badd sGlobal0_hz19 sGlobal0_hz3 (by norm_num) (by norm_num)

theorem sGlobal0_hz21 : B (110732771457999278473 / 1000000000000000000) (55366385728999643621 / 500000000000000000) ((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ)))) := bmul sGlobal0_hz4 sGlobal0_hz20 (by norm_num) (by norm_num)

theorem sGlobal0_hz22 : B (209099159 / 15625000000000000) (13382346177 / 1000000000000000000) ((2 : ℝ) / (149450625 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (149450625 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal0_hz23 : B (2452349334953899930479 / 200000000000000000) (12261746674769501594427 / 1000000000000000000) (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2) := bsq sGlobal0_hz21 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal0_hz24 : B (82045469362091 / 500000000000000000) (32818187747289 / 200000000000000000) (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2)) := bmul sGlobal0_hz22 sGlobal0_hz23 (by norm_num) (by norm_num)

theorem sGlobal0_hz25 : B (82045469362091 / 250000000000000000) (32818187747289 / 100000000000000000) ((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) := bmul (bpoint (2 : ℝ)) sGlobal0_hz24 (by norm_num) (by norm_num)

theorem sGlobal0_hz26 : B (117258080744995992792057 / 1000000000000000000) (58629040372497996396029 / 500000000000000000) (√(13749457500 : ℝ)) := bsqrt (bpoint (13749457500 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal0_hz27 : B (117304080744995992792057 / 1000000000000000000) (58652040372497996396029 / 500000000000000000) ((√(13749457500 : ℝ)) + (46 : ℝ)) := badd sGlobal0_hz26 (bpoint (46 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal0_hz28 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal0_hz25 sGlobal0_hz27 (by norm_num) (by norm_num)

theorem sGlobal0_hz29 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (s3rs 12225 46 maskSlack) := by
    convert sGlobal0_hz28 using 1 <;>
      norm_num [s3rs, s3pp, s3K, mA, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal0_hz30 : B (490797546012267 / 1000000000000000000) (49079754601227 / 100000000000000000) ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (3 : ℝ)) sGlobal0_hz10 (by norm_num) (by norm_num)

theorem sGlobal0_hz31 : B (490797546012267 / 500000000000000000) (49079754601227 / 50000000000000000) ((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal0_hz30 (by norm_num) (by norm_num)

theorem sGlobal0_hz32 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal0_hz31 sGlobal0_hz27 (by norm_num) (by norm_num)

theorem sGlobal0_hz33 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (s3r1 12225 46) := by
    convert sGlobal0_hz32 using 1 <;>
      norm_num [s3r1, mA] <;> ring

theorem sGlobal0_hz34 : B (163599182004089 / 500000000000000000) (16359918200409 / 50000000000000000) ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (2 : ℝ)) sGlobal0_hz10 (by norm_num) (by norm_num)

theorem sGlobal0_hz35 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal0_hz34 (by norm_num) (by norm_num)

theorem sGlobal0_hz36 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal0_hz35 sGlobal0_hz27 (by norm_num) (by norm_num)

theorem sGlobal0_hz37 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (s3rpp 12225 46) := by
    convert sGlobal0_hz36 using 1 <;>
      norm_num [s3rpp, mA] <;> ring

theorem sGlobal0_hz38 {c : ℝ} (hc : B (69 / 200) (7 / 20) c) : B (69 / 200) (7 / 20) c := hc

theorem sGlobal0_hz39 : B (19128783984447171 / 31250000000000000) (612121088076333303 / 1000000000000000000) (kdot ((69 / 200))) := by
    constructor
    · apply bkdot_lower (q := (697845862338986089 / 1000000000000000000)) (a := (609278770992571401 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (87230732792373261 / 125000000000000000)) (a := (152319692522724219 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal0_hz40 : B (4761 / 40000) (4761 / 40000) (((69 / 200) : ℝ)^2) := bsq (bpoint ((69 / 200) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal0_hz41 : B (35239 / 40000) (35239 / 40000) ((1 : ℝ) - (((69 / 200) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal0_hz40 (by norm_num) (by norm_num)

theorem sGlobal0_hz42 : B (938602684845936289 / 1000000000000000000) (93860268484593629 / 100000000000000000) (√((1 : ℝ) - (((69 / 200) : ℝ)^2))) := bsqrt sGlobal0_hz41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal0_hz43 : B (11950660551404413 / 40000000000000000) (149383256892555163 / 500000000000000000) ((√((1 : ℝ) - (((69 / 200) : ℝ)^2))) / Real.pi) := bdiv sGlobal0_hz42 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal0_hz44 : B (211181775188296767 / 1000000000000000000) (21118177538633499 / 100000000000000000) (((69 / 200) : ℝ) * (kdot ((69 / 200)))) := bmul (bpoint ((69 / 200) : ℝ)) sGlobal0_hz39 (by norm_num) (by norm_num)

theorem sGlobal0_hz45 : B (127487072243351773 / 250000000000000000) (127487072292861329 / 250000000000000000) (((√((1 : ℝ) - (((69 / 200) : ℝ)^2))) / Real.pi) + (((69 / 200) : ℝ) * (kdot ((69 / 200))))) := badd sGlobal0_hz43 sGlobal0_hz44 (by norm_num) (by norm_num)

theorem sGlobal0_hz46 : B (127487072243351773 / 250000000000000000) (127487072292861329 / 250000000000000000) (kappa ((69 / 200))) := by rw [kappa_eq]; exact sGlobal0_hz45

theorem sGlobal0_hz47 : B (24552736689413483 / 40000000000000000) (122763683533952243 / 200000000000000000) (kdot ((7 / 20))) := by
    constructor
    · apply bkdot_lower (q := (2710502603471527 / 3906250000000000)) (a := (606612611682571879 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (693888666488710911 / 1000000000000000000)) (a := (606612611000180037 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal0_hz48 : B (49 / 400) (49 / 400) (((7 / 20) : ℝ)^2) := bsq (bpoint ((7 / 20) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal0_hz49 : B (351 / 400) (351 / 400) ((1 : ℝ) - (((7 / 20) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal0_hz48 (by norm_num) (by norm_num)

theorem sGlobal0_hz50 : B (93674969975975973 / 100000000000000000) (936749699759759731 / 1000000000000000000) (√((1 : ℝ) - (((7 / 20) : ℝ)^2))) := bsqrt sGlobal0_hz49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal0_hz51 : B (298176690313229203 / 1000000000000000000) (74544172578307301 / 250000000000000000) ((√((1 : ℝ) - (((7 / 20) : ℝ)^2))) / Real.pi) := bdiv sGlobal0_hz50 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal0_hz52 : B (26854555754045997 / 125000000000000000) (107418223092208213 / 500000000000000000) (((7 / 20) : ℝ) * (kdot ((7 / 20)))) := bmul (bpoint ((7 / 20) : ℝ)) sGlobal0_hz47 (by norm_num) (by norm_num)

theorem sGlobal0_hz53 : B (513013136345597179 / 1000000000000000000) (51301313649764563 / 100000000000000000) (((√((1 : ℝ) - (((7 / 20) : ℝ)^2))) / Real.pi) + (((7 / 20) : ℝ) * (kdot ((7 / 20))))) := badd sGlobal0_hz51 sGlobal0_hz52 (by norm_num) (by norm_num)

theorem sGlobal0_hz54 : B (513013136345597179 / 1000000000000000000) (51301313649764563 / 100000000000000000) (kappa ((7 / 20))) := by rw [kappa_eq]; exact sGlobal0_hz53

theorem sGlobal0_hz55 {c : ℝ} (hc : B (69 / 200) (7 / 20) c) : B (127487072243351773 / 250000000000000000) (51301313649764563 / 100000000000000000) (kappa c) := bkappa (sGlobal0_hz38 hc) (by norm_num) (by norm_num) sGlobal0_hz46.1 sGlobal0_hz54.2

theorem sGlobal0_hz56 : B 24450 24450 ((2 : ℝ) * (12225 : ℝ)) := bmul (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal0_hz57 {c : ℝ} (hc : B (69 / 200) (7 / 20) c) : B (48698686350235437 / 100000000000000000) (122512927756648227 / 250000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (sGlobal0_hz55 hc) (by norm_num) (by norm_num)

theorem sGlobal0_hz58 {c : ℝ} (hc : B (69 / 200) (7 / 20) c) : B (23813657625265128693 / 2000000000000000) (59908821673000983003 / 5000000000000000) (((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) := bmul sGlobal0_hz56 (sGlobal0_hz57 hc) (by norm_num) (by norm_num)

theorem sGlobal0_hz59 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (4 : ℝ)) sGlobal0_hz10 (by norm_num) (by norm_num)

theorem sGlobal0_hz60 {c : ℝ} (hc : B (69 / 200) (7 / 20) c) : B (595341407911791816507 / 50000000000000000) (2995440920050867146061 / 250000000000000000) ((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bsub (sGlobal0_hz58 hc) sGlobal0_hz59 (by norm_num) (by norm_num)

theorem sGlobal0_hz61 {c : ℝ} (hc : B (69 / 200) (7 / 20) c) : B (27279603367529737063 / 250000000000000000) (21892248564460863607 / 200000000000000000) (√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) := bsqrt (sGlobal0_hz60 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal0_hz62 : B (30670756373515103 / 125000000000000000) (122683025494060423 / 500000000000000000) ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal0_hz7 (by norm_num) (by norm_num)

theorem sGlobal0_hz63 {c : ℝ} (hc : B (69 / 200) (7 / 20) c) : B (54436523709565413703 / 500000000000000000) (109215876771316197211 / 1000000000000000000) ((√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) - ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))))) := bsub (sGlobal0_hz61 hc) sGlobal0_hz62 (by norm_num) (by norm_num)

theorem sGlobal0_hz64 {c : ℝ} (hc : B (69 / 200) (7 / 20) c) : B (54436523709565413703 / 500000000000000000) (109215876771316197211 / 1000000000000000000) (s3dm 12225 46 c) := by
    convert (sGlobal0_hz63 hc) using 1 <;>
      norm_num [s3dm, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal0_hz65 : B (6126072185528622723889 / 500000000000000000) (2450428874211449090087 / 200000000000000000) ((s3ap 12225 46)^2) := bsq sGlobal0_hz9 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal0_hz66 : B (6126072185528622723889 / 250000000000000000) (2450428874211449090087 / 100000000000000000) ((2 : ℝ) * ((s3ap 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal0_hz65 (by norm_num) (by norm_num)

theorem sGlobal0_hz67 {c : ℝ} (hc : B (69 / 200) (7 / 20) c) : B (2370668090865661943663 / 200000000000000000) (2385621547785464979541 / 200000000000000000) ((s3dm 12225 46 c)^2) := bsq (sGlobal0_hz64 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal0_hz68 {c : ℝ} (hc : B (69 / 200) (7 / 20) c) : B (12576181003187165997851 / 1000000000000000000) (2530189657557236236511 / 200000000000000000) (((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) := bsub sGlobal0_hz66 (sGlobal0_hz67 hc) (by norm_num) (by norm_num)

theorem sGlobal0_hz69 : B (1524735695971823534271 / 125000000000000000) (609894278388729413841 / 50000000000000000) ((s3am 12225 46)^2) := bsq sGlobal0_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal0_hz70 : B (1524735695971823534271 / 62500000000000000) (609894278388729413841 / 25000000000000000) ((2 : ℝ) * ((s3am 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal0_hz69 (by norm_num) (by norm_num)

theorem sGlobal0_hz71 {c : ℝ} (hc : B (69 / 200) (7 / 20) c) : B (515506598799876873 / 1000000000000000000) (259285681471068489 / 500000000000000000) ((((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) / ((2 : ℝ) * ((s3am 12225 46)^2))) := bdiv (sGlobal0_hz68 hc) sGlobal0_hz70 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal0_hz72 {c : ℝ} (hc : B (69 / 200) (7 / 20) c) : B (515506598799876873 / 1000000000000000000) (259285681471068489 / 500000000000000000) (s3c1 12225 46 c) := by
    convert (sGlobal0_hz71 hc) using 1 <;>
      norm_num [s3c1] <;> ring

theorem sGlobal0_hz73 {c : ℝ} (hc : B (69 / 200) (7 / 20) c) : B (19128783984447171 / 31250000000000000) (122763683533952243 / 200000000000000000) (kdot c) := bkdot (sGlobal0_hz38 hc) sGlobal0_hz39.1 sGlobal0_hz47.2

theorem sGlobal0_hz74 : B (336198118800021757 / 500000000000000000) (672396237600062597 / 1000000000000000000) (kdot ((515506598799876873 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (4523295956577369 / 8000000000000000)) (a := (514598786622039713 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (141352998643042781 / 250000000000000000)) (a := (514598786622009739 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal0_hz75 : B (168383986179869559 / 250000000000000000) (336767972359746891 / 500000000000000000) (kdot ((259285681471068489 / 500000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (28152590386960869 / 50000000000000000)) (a := (25640426943260483 / 50000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (563051807739217379 / 1000000000000000000)) (a := (512808538865185241 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal0_hz76 {c : ℝ} (hc : B (69 / 200) (7 / 20) c) : B (336198118800021757 / 500000000000000000) (336767972359746891 / 500000000000000000) (kdot (s3c1 12225 46 c)) := bkdot (sGlobal0_hz72 hc) sGlobal0_hz74.1 sGlobal0_hz75.2

theorem sGlobal0_hz77 {c : ℝ} (hc : B (69 / 200) (7 / 20) c) : B (4761 / 40000) (49 / 400) (c^2) := bsq (sGlobal0_hz38 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal0_hz78 {c : ℝ} (hc : B (69 / 200) (7 / 20) c) : B (351 / 400) (35239 / 40000) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (sGlobal0_hz77 hc) (by norm_num) (by norm_num)

theorem sGlobal0_hz79 {c : ℝ} (hc : B (69 / 200) (7 / 20) c) : B (93674969975975973 / 100000000000000000) (93860268484593629 / 100000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (sGlobal0_hz78 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal0_hz80 : B (39119999999999765769 / 1600000000000000) (3912000000000000489 / 160000000000000) ((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (149450625 : ℝ)) sGlobal0_hz10 (by norm_num) (by norm_num)

theorem sGlobal0_hz81 {c : ℝ} (hc : B (69 / 200) (7 / 20) c) : B (573404244934406011 / 1000000000000000000) (288065807416361089 / 500000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (sGlobal0_hz79 hc) (sGlobal0_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal0_hz82 {c : ℝ} (hc : B (69 / 200) (7 / 20) c) : B (14019733788646143025793 / 1000000000000000000) (14086417982660059012903 / 1000000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) := bmul sGlobal0_hz80 (sGlobal0_hz81 hc) (by norm_num) (by norm_num)

theorem sGlobal0_hz83 {c : ℝ} (hc : B (69 / 200) (7 / 20) c) : B (109529170223797992389 / 15625000000000000) (1760802247832507376613 / 250000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) / (2 : ℝ)) := bdiv (sGlobal0_hz82 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal0_hz84 {c : ℝ} (hc : B (69 / 200) (7 / 20) c) : B (109529170223797992389 / 15625000000000000) (1760802247832507376613 / 250000000000000000) (s3Cpa 12225 c) := by
    convert (sGlobal0_hz83 hc) using 1 <;>
      norm_num [s3Cpa, mA] <;> ring

theorem sGlobal0_hz85 {c : ℝ} (hc : B (69 / 200) (7 / 20) c) : B (298176690313229203 / 1000000000000000000) (149383256892555163 / 500000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (sGlobal0_hz79 hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal0_hz86 {c : ℝ} (hc : B (69 / 200) (7 / 20) c) : B (211181775188296767 / 1000000000000000000) (107418223092208213 / 500000000000000000) (c * (kdot c)) := bmul (sGlobal0_hz38 hc) (sGlobal0_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal0_hz87 {c : ℝ} (hc : B (69 / 200) (7 / 20) c) : B (83340244128812777 / 1000000000000000000) (87584738596813559 / 1000000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (sGlobal0_hz85 hc) (sGlobal0_hz86 hc) (by norm_num) (by norm_num)

theorem sGlobal0_hz88 {c : ℝ} (hc : B (69 / 200) (7 / 20) c) : B (2037668968949460197107 / 1000000000000000000) (2141446858692091785231 / 1000000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) := bmul sGlobal0_hz80 (sGlobal0_hz87 hc) (by norm_num) (by norm_num)

theorem sGlobal0_hz89 {c : ℝ} (hc : B (69 / 200) (7 / 20) c) : B (1018834484474730098553 / 1000000000000000000) (133840428668255736577 / 125000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) / (2 : ℝ)) := bdiv (sGlobal0_hz88 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal0_hz90 {c : ℝ} (hc : B (69 / 200) (7 / 20) c) : B (1018834484474730098553 / 1000000000000000000) (133840428668255736577 / 125000000000000000) (s3Cpp 12225 c) := by
    convert (sGlobal0_hz89 hc) using 1 <;>
      norm_num [s3Cpp, mA] <;> ring

theorem sGlobal0_hz91 {c : ℝ} (hc : B (69 / 200) (7 / 20) c) : B (7125012004256809221297 / 1000000000000000000) (3579177050631883959339 / 500000000000000000) ((s3Cpa 12225 c) + (s3r1 12225 46)) := badd (sGlobal0_hz84 hc) sGlobal0_hz33 (by norm_num) (by norm_num)

theorem sGlobal0_hz92 {c : ℝ} (hc : B (69 / 200) (7 / 20) c) : B (32256209217694683079 / 500000000000000000) (32407154880125930153 / 500000000000000000) (((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) := bdiv (sGlobal0_hz91 hc) sGlobal0_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal0_hz93 {c : ℝ} (hc : B (69 / 200) (7 / 20) c) : B (6463510146088342657 / 100000000000000000) (64936992785745920729 / 1000000000000000000) ((((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) + (s3e0 12225 46)) := badd (sGlobal0_hz92 hc) sGlobal0_hz16 (by norm_num) (by norm_num)

theorem sGlobal0_hz94 {c : ℝ} (hc : B (69 / 200) (7 / 20) c) : B (6463510146088342657 / 100000000000000000) (64936992785745920729 / 1000000000000000000) (s3Lam 12225 46 c) := by
    convert (sGlobal0_hz93 hc) using 1 <;>
      norm_num [s3Lam] <;> ring

theorem sGlobal0_hz95 {c : ℝ} (hc : B (69 / 200) (7 / 20) c) : B (1095597891097221904153 / 1000000000000000000) (573743417984269083717 / 500000000000000000) ((s3Cpp 12225 c) + (s3rpp 12225 46)) := badd (sGlobal0_hz90 hc) sGlobal0_hz37 (by norm_num) (by norm_num)

theorem sGlobal0_hz96 {c : ℝ} (hc : B (69 / 200) (7 / 20) c) : B (136949736387152738019 / 250000000000000000) (772873630117252152309 / 1000000000000000000) (if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) := bweaken (bfirst (sGlobal0_hz95 hc) (sGlobal0_hz76 hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem sGlobal0_hz97 {c : ℝ} (hc : B (69 / 200) (7 / 20) c) : B (4177696340858694863569 / 1000000000000000000) (4216813032056017754221 / 1000000000000000000) ((s3Lam 12225 46 c)^2) := bsq (sGlobal0_hz94 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal0_hz98 {c : ℝ} (hc : B (69 / 200) (7 / 20) c) : B (53149410681243443 / 200000000000000000) (268916258463665557 / 1000000000000000000) ((s3c1 12225 46 c)^2) := bsq (sGlobal0_hz72 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal0_hz99 {c : ℝ} (hc : B (69 / 200) (7 / 20) c) : B (731083741536334443 / 1000000000000000000) (146850589318756557 / 200000000000000000) ((1 : ℝ) - ((s3c1 12225 46 c)^2)) := bsub (bpoint (1 : ℝ)) (sGlobal0_hz98 hc) (by norm_num) (by norm_num)

theorem sGlobal0_hz100 {c : ℝ} (hc : B (69 / 200) (7 / 20) c) : B (171006870217115481 / 200000000000000000) (428442804407362753 / 500000000000000000) (√((1 : ℝ) - ((s3c1 12225 46 c)^2))) := bsqrt (sGlobal0_hz99 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal0_hz101 {c : ℝ} (hc : B (69 / 200) (7 / 20) c) : B (671542408984341507 / 250000000000000000) (2691985533619159027 / 1000000000000000000) (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))) := bmul pi_mem (sGlobal0_hz100 hc) (by norm_num) (by norm_num)

theorem sGlobal0_hz102 {c : ℝ} (hc : B (69 / 200) (7 / 20) c) : B (1551901482636170263393 / 1000000000000000000) (1569823802503269028209 / 1000000000000000000) (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2))))) := bdiv (sGlobal0_hz97 hc) (sGlobal0_hz101 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal0_hz103 {c : ℝ} (hc : B (69 / 200) (7 / 20) c) : B (2099700428184781215469 / 1000000000000000000) (1171348716310260590259 / 500000000000000000) ((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) := badd (sGlobal0_hz96 hc) (sGlobal0_hz102 hc) (by norm_num) (by norm_num)

theorem sGlobal0_hz104 : B (3762781186094069 / 250000000000000000) (376278118609407 / 25000000000000000) ((s3e0 12225 46)^2) := bsq sGlobal0_hz16 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal0_hz105 {c : ℝ} (hc : B (69 / 200) (7 / 20) c) : B (419943095861905118349 / 200000000000000000) (1171356241872632778399 / 500000000000000000) (((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) := badd (sGlobal0_hz103 hc) sGlobal0_hz104 (by norm_num) (by norm_num)

theorem sGlobal0_hz106 {c : ℝ} (hc : B (69 / 200) (7 / 20) c) : B (534553138190193215469 / 250000000000000000) (1190604778599694913407 / 500000000000000000) ((((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) + (s3rs 12225 46 maskSlack)) := badd (sGlobal0_hz105 hc) sGlobal0_hz29 (by norm_num) (by norm_num)

theorem sGlobal0_hz107 {c : ℝ} (hc : B (69 / 200) (7 / 20) c) : B (534553138190193215469 / 250000000000000000) (1190604778599694913407 / 500000000000000000) (s3U 12225 46 maskSlack c) := by
    convert (sGlobal0_hz106 hc) using 1 <;>
      norm_num [s3U] <;> ring

theorem sGlobal0_hz108 {c : ℝ} (hc : B (69 / 200) (7 / 20) c) : B (188414215570447564747 / 200000000000000000) (124245002840444260877 / 125000000000000000) ((s3Cpp 12225 c) - (s3rpp 12225 46)) := bsub (sGlobal0_hz90 hc) sGlobal0_hz37 (by norm_num) (by norm_num)

theorem sGlobal0_hz109 {c : ℝ} (hc : B (69 / 200) (7 / 20) c) : B 0 0 (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ)) := bweaken (bmin (sGlobal0_hz108 hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem sGlobal0_hz110 {c : ℝ} (hc : B (69 / 200) (7 / 20) c) : B 0 0 ((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) := bmul (sGlobal0_hz76 hc) (sGlobal0_hz109 hc) (by norm_num) (by norm_num)

theorem sGlobal0_hz111 {c : ℝ} (hc : B (69 / 200) (7 / 20) c) : B (-376278118609407 / 25000000000000000) (-3762781186094069 / 250000000000000000) (((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) := bsub (sGlobal0_hz110 hc) sGlobal0_hz104 (by norm_num) (by norm_num)

theorem sGlobal0_hz112 {c : ℝ} (hc : B (69 / 200) (7 / 20) c) : B (-4814015572358580787 / 125000000000000000) (-38512124575991646407 / 1000000000000000000) ((((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) - (s3rs 12225 46 maskSlack)) := bsub (sGlobal0_hz111 hc) sGlobal0_hz29 (by norm_num) (by norm_num)

theorem sGlobal0_hz113 {c : ℝ} (hc : B (69 / 200) (7 / 20) c) : B (-4814015572358580787 / 125000000000000000) (-38512124575991646407 / 1000000000000000000) (s3L 12225 46 maskSlack c) := by
    convert (sGlobal0_hz112 hc) using 1 <;>
      norm_num [s3L] <;> ring

theorem sGlobal0_hz114 {c : ℝ} (hc : B (69 / 200) (7 / 20) c) : B 0 (1190604778599694913407 / 500000000000000000) |(s3U 12225 46 maskSlack c)| := bweaken (babs (sGlobal0_hz107 hc)) (by norm_num) (by norm_num)

theorem sGlobal0_hz115 {c : ℝ} (hc : B (69 / 200) (7 / 20) c) : B 0 (4814015572358580787 / 125000000000000000) |(s3L 12225 46 maskSlack c)| := bweaken (babs (sGlobal0_hz113 hc)) (by norm_num) (by norm_num)

theorem sGlobal0_hz116 {c : ℝ} (hc : B (69 / 200) (7 / 20) c) : B 0 (1190604778599694913407 / 500000000000000000) (max |(s3U 12225 46 maskSlack c)| |(s3L 12225 46 maskSlack c)|) := bweaken (bmax (sGlobal0_hz114 hc) (sGlobal0_hz115 hc)) (by norm_num) (by norm_num)

theorem sGlobal0_hz117 {c : ℝ} (hc : B (69 / 200) (7 / 20) c) : B 0 (1190604778599694913407 / 500000000000000000) (s3nks 12225 46 maskSlack c) := by
    convert (sGlobal0_hz116 hc) using 1 <;>
      norm_num [s3nks] <;> ring

theorem sGlobal0 {c : ℝ} (hc : B (69 / 200) (7 / 20) c) :
    0 < s3am 12225 46 ∧ 0 ≤ s3dm 12225 46 c ∧
    s3dm 12225 46 c ^ 2 ≤ 2 * s3ap 12225 46 ^ 2 ∧ s3c1 12225 46 c < 1 ∧
    0 ≤ s3Cpa 12225 c - s3r1 12225 46 ∧
    s3e0 12225 46 ≤ (s3Cpa 12225 c - s3r1 12225 46) / s3ap 12225 46 ∧
    s3nks 12225 46 maskSlack c ≤ 12225 * (97391 / 500000) := by

  refine ⟨lt_of_lt_of_le (by norm_num) sGlobal0_hz14.1,
    le_trans (by norm_num) (sGlobal0_hz64 hc).1, ?_,
    lt_of_le_of_lt (sGlobal0_hz72 hc).2 (by norm_num), ?_, ?_,
    le_trans (sGlobal0_hz117 hc).2 (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (sGlobal0_hz64 hc).1) (sGlobal0_hz64 hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) sGlobal0_hz9.1 2
    nlinarith only [h1, h2]
  · linarith only [(sGlobal0_hz84 hc).1, sGlobal0_hz33.2]
  · have hap : 0 < s3ap 12225 46 := lt_of_lt_of_le (by norm_num) sGlobal0_hz9.1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul sGlobal0_hz16.2 sGlobal0_hz9.2 (le_trans (by norm_num) sGlobal0_hz9.1) (by norm_num)
    linarith only [h, (sGlobal0_hz84 hc).1, sGlobal0_hz33.2]

end BstLean.Part255
