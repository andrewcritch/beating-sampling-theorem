import BstLean.Part255SGlobal62
import BstLean.Part255Numeric10
namespace BstLean.Part255
open Real BstLean.Part130 BstLean.Part182 BstLean.Part197 BstLean.Part246
theorem sGlobal66_hz0 : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal66_hz1 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) ((√(23 : ℝ)) / (12225 : ℝ)) := bdiv sGlobal66_hz0 (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal66_hz2 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) maskSlack := by
    convert sGlobal66_hz1 using 1 <;>
      norm_num [maskSlack] <;> ring

theorem sGlobal66_hz3 : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal66_hz4 : B (6395294793910793 / 500000000000000000) (12790589587821587 / 1000000000000000000) (√((2 / 12225) : ℝ)) := bsqrt (bpoint ((2 / 12225) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal66_hz5 : B (7230130686979 / 62500000000000000) (23136418198333 / 200000000000000000) (√((2 / 149450625) : ℝ)) := bsqrt (bpoint ((2 / 149450625) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal66_hz6 : B (2211334438749598093 / 20000000000000000) (110566721937479904651 / 1000000000000000000) (√(12225 : ℝ)) := bsqrt (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal66_hz7 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))) := bmul sGlobal66_hz3 sGlobal66_hz4 (by norm_num) (by norm_num)

theorem sGlobal66_hz8 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) ((√(12225 : ℝ)) + ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := badd sGlobal66_hz6 sGlobal66_hz7 (by norm_num) (by norm_num)

theorem sGlobal66_hz9 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) (s3ap 12225 46) := by
    convert sGlobal66_hz8 using 1 <;>
      norm_num [s3ap, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal66_hz10 : B (163599182004089 / 1000000000000000000) (16359918200409 / 100000000000000000) ((2 : ℝ) / (12225 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal66_hz11 : B (1222499983640081799591 / 100000000000000000) (12224999836400817995911 / 1000000000000000000) ((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ))) := bsub (bpoint (12225 : ℝ)) sGlobal66_hz10 (by norm_num) (by norm_num)

theorem sGlobal66_hz12 : B (110566721197658827907 / 1000000000000000000) (27641680299414706977 / 250000000000000000) (√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) := bsqrt sGlobal66_hz11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal66_hz13 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) ((√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) - ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bsub sGlobal66_hz12 sGlobal66_hz7 (by norm_num) (by norm_num)

theorem sGlobal66_hz14 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) (s3am 12225 46) := by
    convert sGlobal66_hz13 using 1 <;>
      norm_num [s3am, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal66_hz15 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√((2 / 12225) : ℝ)) * (√(92 : ℝ))) := bmul sGlobal66_hz4 sGlobal66_hz3 (by norm_num) (by norm_num)

theorem sGlobal66_hz16 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) (s3e0 12225 46) := by
    convert sGlobal66_hz15 using 1 <;>
      norm_num [s3e0, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal66_hz17 : B (250196148528560847 / 500000000000000000) (100078459411424339 / 200000000000000000) (((1 / 2) : ℝ) + maskSlack) := badd (bpoint ((1 / 2) : ℝ)) sGlobal66_hz2 (by norm_num) (by norm_num)

theorem sGlobal66_hz18 : B (59827153232297998295487 / 800000000000000) (23930861292919199366019 / 320000000000000) ((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack)) := bmul (bpoint (149450625 : ℝ)) sGlobal66_hz17 (by norm_num) (by norm_num)

theorem sGlobal66_hz19 : B (1729554180017180009583 / 200000000000000000) (8647770900085900056557 / 1000000000000000000) (√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) := bsqrt sGlobal66_hz18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal66_hz20 : B (4328681281566262743499 / 500000000000000000) (8657362563132525495641 / 1000000000000000000) ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))) := badd sGlobal66_hz19 sGlobal66_hz3 (by norm_num) (by norm_num)

theorem sGlobal66_hz21 : B (110732771457999278473 / 1000000000000000000) (55366385728999643621 / 500000000000000000) ((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ)))) := bmul sGlobal66_hz4 sGlobal66_hz20 (by norm_num) (by norm_num)

theorem sGlobal66_hz22 : B (209099159 / 15625000000000000) (13382346177 / 1000000000000000000) ((2 : ℝ) / (149450625 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (149450625 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal66_hz23 : B (2452349334953899930479 / 200000000000000000) (12261746674769501594427 / 1000000000000000000) (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2) := bsq sGlobal66_hz21 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal66_hz24 : B (82045469362091 / 500000000000000000) (32818187747289 / 200000000000000000) (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2)) := bmul sGlobal66_hz22 sGlobal66_hz23 (by norm_num) (by norm_num)

theorem sGlobal66_hz25 : B (82045469362091 / 250000000000000000) (32818187747289 / 100000000000000000) ((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) := bmul (bpoint (2 : ℝ)) sGlobal66_hz24 (by norm_num) (by norm_num)

theorem sGlobal66_hz26 : B (117258080744995992792057 / 1000000000000000000) (58629040372497996396029 / 500000000000000000) (√(13749457500 : ℝ)) := bsqrt (bpoint (13749457500 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal66_hz27 : B (117304080744995992792057 / 1000000000000000000) (58652040372497996396029 / 500000000000000000) ((√(13749457500 : ℝ)) + (46 : ℝ)) := badd sGlobal66_hz26 (bpoint (46 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal66_hz28 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal66_hz25 sGlobal66_hz27 (by norm_num) (by norm_num)

theorem sGlobal66_hz29 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (s3rs 12225 46 maskSlack) := by
    convert sGlobal66_hz28 using 1 <;>
      norm_num [s3rs, s3pp, s3K, mA, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal66_hz30 : B (490797546012267 / 1000000000000000000) (49079754601227 / 100000000000000000) ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (3 : ℝ)) sGlobal66_hz10 (by norm_num) (by norm_num)

theorem sGlobal66_hz31 : B (490797546012267 / 500000000000000000) (49079754601227 / 50000000000000000) ((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal66_hz30 (by norm_num) (by norm_num)

theorem sGlobal66_hz32 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal66_hz31 sGlobal66_hz27 (by norm_num) (by norm_num)

theorem sGlobal66_hz33 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (s3r1 12225 46) := by
    convert sGlobal66_hz32 using 1 <;>
      norm_num [s3r1, mA] <;> ring

theorem sGlobal66_hz34 : B (163599182004089 / 500000000000000000) (16359918200409 / 50000000000000000) ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (2 : ℝ)) sGlobal66_hz10 (by norm_num) (by norm_num)

theorem sGlobal66_hz35 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal66_hz34 (by norm_num) (by norm_num)

theorem sGlobal66_hz36 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal66_hz35 sGlobal66_hz27 (by norm_num) (by norm_num)

theorem sGlobal66_hz37 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (s3rpp 12225 46) := by
    convert sGlobal66_hz36 using 1 <;>
      norm_num [s3rpp, mA] <;> ring

theorem sGlobal66_hz38 {c : ℝ} (hc : B (27 / 40) (17 / 25) c) : B (27 / 40) (17 / 25) c := hc

theorem sGlobal66_hz39 : B (147171278004889929 / 200000000000000000) (735856390024449647 / 1000000000000000000) (kdot ((27 / 40))) := by
    constructor
    · apply bkdot_lower (q := (440488195921603167 / 1000000000000000000)) (a := (41491581229593831 / 100000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (220244097960801583 / 500000000000000000)) (a := (103728953073984577 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal66_hz40 : B (729 / 1600) (729 / 1600) (((27 / 40) : ℝ)^2) := bsq (bpoint ((27 / 40) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal66_hz41 : B (871 / 1600) (871 / 1600) ((1 : ℝ) - (((27 / 40) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal66_hz40 (by norm_num) (by norm_num)

theorem sGlobal66_hz42 : B (92227216021085663 / 125000000000000000) (147563545633737061 / 200000000000000000) (√((1 : ℝ) - (((27 / 40) : ℝ)^2))) := bsqrt sGlobal66_hz41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal66_hz43 : B (234854677077757223 / 1000000000000000000) (29356834634719653 / 125000000000000000) ((√((1 : ℝ) - (((27 / 40) : ℝ)^2))) / Real.pi) := bdiv sGlobal66_hz42 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal66_hz44 : B (49670306326650351 / 100000000000000000) (62087882908312939 / 125000000000000000) (((27 / 40) : ℝ) * (kdot ((27 / 40)))) := bmul (bpoint ((27 / 40) : ℝ)) sGlobal66_hz39 (by norm_num) (by norm_num)

theorem sGlobal66_hz45 : B (731557740344260733 / 1000000000000000000) (5715294846439537 / 7812500000000000) (((√((1 : ℝ) - (((27 / 40) : ℝ)^2))) / Real.pi) + (((27 / 40) : ℝ) * (kdot ((27 / 40))))) := badd sGlobal66_hz43 sGlobal66_hz44 (by norm_num) (by norm_num)

theorem sGlobal66_hz46 : B (731557740344260733 / 1000000000000000000) (5715294846439537 / 7812500000000000) (kappa ((27 / 40))) := by rw [kappa_eq]; exact sGlobal66_hz45

theorem sGlobal66_hz47 : B (147604047826218153 / 200000000000000000) (738020239131090767 / 1000000000000000000) (kdot ((17 / 25))) := by
    constructor
    · apply bkdot_lower (q := (436435780471984763 / 1000000000000000000)) (a := (20575842303374401 / 50000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (218217890235992381 / 500000000000000000)) (a := (205758423033744009 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal66_hz48 : B (289 / 625) (289 / 625) (((17 / 25) : ℝ)^2) := bsq (bpoint ((17 / 25) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal66_hz49 : B (336 / 625) (336 / 625) ((1 : ℝ) - (((17 / 25) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal66_hz48 (by norm_num) (by norm_num)

theorem sGlobal66_hz50 : B (733212111192934401 / 1000000000000000000) (366606055596467201 / 500000000000000000) (√((1 : ℝ) - (((17 / 25) : ℝ)^2))) := bsqrt sGlobal66_hz49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal66_hz51 : B (233388663662399819 / 1000000000000000000) (11669433183119991 / 50000000000000000) ((√((1 : ℝ) - (((17 / 25) : ℝ)^2))) / Real.pi) := bdiv sGlobal66_hz50 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal66_hz52 : B (12546344065228543 / 25000000000000000) (250926881304570861 / 500000000000000000) (((17 / 25) : ℝ) * (kdot ((17 / 25)))) := bmul (bpoint ((17 / 25) : ℝ)) sGlobal66_hz47 (by norm_num) (by norm_num)

theorem sGlobal66_hz53 : B (735242426271541539 / 1000000000000000000) (367621213135770771 / 500000000000000000) (((√((1 : ℝ) - (((17 / 25) : ℝ)^2))) / Real.pi) + (((17 / 25) : ℝ) * (kdot ((17 / 25))))) := badd sGlobal66_hz51 sGlobal66_hz52 (by norm_num) (by norm_num)

theorem sGlobal66_hz54 : B (735242426271541539 / 1000000000000000000) (367621213135770771 / 500000000000000000) (kappa ((17 / 25))) := by rw [kappa_eq]; exact sGlobal66_hz53

theorem sGlobal66_hz55 {c : ℝ} (hc : B (27 / 40) (17 / 25) c) : B (731557740344260733 / 1000000000000000000) (367621213135770771 / 500000000000000000) (kappa c) := bkappa (sGlobal66_hz38 hc) (by norm_num) (by norm_num) sGlobal66_hz46.1 sGlobal66_hz54.2

theorem sGlobal66_hz56 : B 24450 24450 ((2 : ℝ) * (12225 : ℝ)) := bmul (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal66_hz57 {c : ℝ} (hc : B (27 / 40) (17 / 25) c) : B (132378786864229229 / 500000000000000000) (268442259655739267 / 1000000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (sGlobal66_hz55 hc) (by norm_num) (by norm_num)

theorem sGlobal66_hz58 {c : ℝ} (hc : B (27 / 40) (17 / 25) c) : B (64733226776608092981 / 10000000000000000) (131268264971656501563 / 20000000000000000) (((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) := bmul sGlobal66_hz56 (sGlobal66_hz57 hc) (by norm_num) (by norm_num)

theorem sGlobal66_hz59 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (4 : ℝ)) sGlobal66_hz10 (by norm_num) (by norm_num)

theorem sGlobal66_hz60 {c : ℝ} (hc : B (27 / 40) (17 / 25) c) : B (323666101163204064087 / 50000000000000000) (3281706297093048530897 / 500000000000000000) ((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bsub (sGlobal66_hz58 hc) sGlobal66_hz59 (by norm_num) (by norm_num)

theorem sGlobal66_hz61 {c : ℝ} (hc : B (27 / 40) (17 / 25) c) : B (80456957581455199353 / 1000000000000000000) (81014891187892717319 / 1000000000000000000) (√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) := bsqrt (sGlobal66_hz60 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal66_hz62 : B (30670756373515103 / 125000000000000000) (122683025494060423 / 500000000000000000) ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal66_hz7 (by norm_num) (by norm_num)

theorem sGlobal66_hz63 {c : ℝ} (hc : B (27 / 40) (17 / 25) c) : B (80211591530467078507 / 1000000000000000000) (16153905027380919299 / 200000000000000000) ((√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) - ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))))) := bsub (sGlobal66_hz61 hc) sGlobal66_hz62 (by norm_num) (by norm_num)

theorem sGlobal66_hz64 {c : ℝ} (hc : B (27 / 40) (17 / 25) c) : B (80211591530467078507 / 1000000000000000000) (16153905027380919299 / 200000000000000000) (s3dm 12225 46 c) := by
    convert (sGlobal66_hz63 hc) using 1 <;>
      norm_num [s3dm, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal66_hz65 : B (6126072185528622723889 / 500000000000000000) (2450428874211449090087 / 200000000000000000) ((s3ap 12225 46)^2) := bsq sGlobal66_hz9 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal66_hz66 : B (6126072185528622723889 / 250000000000000000) (2450428874211449090087 / 100000000000000000) ((2 : ℝ) * ((s3ap 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal66_hz65 (by norm_num) (by norm_num)

theorem sGlobal66_hz67 {c : ℝ} (hc : B (27 / 40) (17 / 25) c) : B (1608474853962624490433 / 250000000000000000) (6523716190841063477179 / 1000000000000000000) ((s3dm 12225 46 c)^2) := bsq (sGlobal66_hz64 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal66_hz68 {c : ℝ} (hc : B (27 / 40) (17 / 25) c) : B (17980572551273427418377 / 1000000000000000000) (9035194663131996469569 / 500000000000000000) (((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) := bsub sGlobal66_hz66 (sGlobal66_hz67 hc) (by norm_num) (by norm_num)

theorem sGlobal66_hz69 : B (1524735695971823534271 / 125000000000000000) (609894278388729413841 / 50000000000000000) ((s3am 12225 46)^2) := bsq sGlobal66_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal66_hz70 : B (1524735695971823534271 / 62500000000000000) (609894278388729413841 / 25000000000000000) ((2 : ℝ) * ((s3am 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal66_hz69 (by norm_num) (by norm_num)

theorem sGlobal66_hz71 {c : ℝ} (hc : B (27 / 40) (17 / 25) c) : B (737036449939161321 / 1000000000000000000) (740718103390143479 / 1000000000000000000) ((((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) / ((2 : ℝ) * ((s3am 12225 46)^2))) := bdiv (sGlobal66_hz68 hc) sGlobal66_hz70 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal66_hz72 {c : ℝ} (hc : B (27 / 40) (17 / 25) c) : B (737036449939161321 / 1000000000000000000) (740718103390143479 / 1000000000000000000) (s3c1 12225 46 c) := by
    convert (sGlobal66_hz71 hc) using 1 <;>
      norm_num [s3c1] <;> ring

theorem sGlobal66_hz73 {c : ℝ} (hc : B (27 / 40) (17 / 25) c) : B (147171278004889929 / 200000000000000000) (738020239131090767 / 1000000000000000000) (kdot c) := bkdot (sGlobal66_hz38 hc) sGlobal66_hz39.1 sGlobal66_hz47.2

theorem sGlobal66_hz74 : B (190943853781915871 / 250000000000000000) (763775415127663487 / 1000000000000000000) (kdot ((737036449939161321 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (194541972759236807 / 500000000000000000)) (a := (371060710216115501 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (389083945518473613 / 1000000000000000000)) (a := (371060710216115499 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal66_hz75 : B (153102914372752013 / 200000000000000000) (191378642965940017 / 250000000000000000) (kdot ((740718103390143479 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (3015170704055251 / 7812500000000000)) (a := (36832884920333439 / 100000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (385941850119072127 / 1000000000000000000)) (a := (92082212300833597 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal66_hz76 {c : ℝ} (hc : B (27 / 40) (17 / 25) c) : B (190943853781915871 / 250000000000000000) (191378642965940017 / 250000000000000000) (kdot (s3c1 12225 46 c)) := bkdot (sGlobal66_hz72 hc) sGlobal66_hz74.1 sGlobal66_hz75.2

theorem sGlobal66_hz77 {c : ℝ} (hc : B (27 / 40) (17 / 25) c) : B (729 / 1600) (289 / 625) (c^2) := bsq (sGlobal66_hz38 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal66_hz78 {c : ℝ} (hc : B (27 / 40) (17 / 25) c) : B (336 / 625) (871 / 1600) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (sGlobal66_hz77 hc) (by norm_num) (by norm_num)

theorem sGlobal66_hz79 {c : ℝ} (hc : B (27 / 40) (17 / 25) c) : B (733212111192934401 / 1000000000000000000) (147563545633737061 / 200000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (sGlobal66_hz78 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal66_hz80 : B (39119999999999765769 / 1600000000000000) (3912000000000000489 / 160000000000000) ((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (149450625 : ℝ)) sGlobal66_hz10 (by norm_num) (by norm_num)

theorem sGlobal66_hz81 {c : ℝ} (hc : B (27 / 40) (17 / 25) c) : B (539538817264638077 / 1000000000000000000) (272262208089105627 / 500000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (sGlobal66_hz79 hc) (sGlobal66_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal66_hz82 {c : ℝ} (hc : B (27 / 40) (17 / 25) c) : B (6595862041060160998601 / 500000000000000000) (13313621975557266824503 / 1000000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) := bmul sGlobal66_hz80 (sGlobal66_hz81 hc) (by norm_num) (by norm_num)

theorem sGlobal66_hz83 {c : ℝ} (hc : B (27 / 40) (17 / 25) c) : B (6595862041060160998601 / 1000000000000000000) (1664202746944658353063 / 250000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) / (2 : ℝ)) := bdiv (sGlobal66_hz82 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal66_hz84 {c : ℝ} (hc : B (27 / 40) (17 / 25) c) : B (6595862041060160998601 / 1000000000000000000) (1664202746944658353063 / 250000000000000000) (s3Cpa 12225 c) := by
    convert (sGlobal66_hz83 hc) using 1 <;>
      norm_num [s3Cpa, mA] <;> ring

theorem sGlobal66_hz85 {c : ℝ} (hc : B (27 / 40) (17 / 25) c) : B (233388663662399819 / 1000000000000000000) (29356834634719653 / 125000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (sGlobal66_hz79 hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal66_hz86 {c : ℝ} (hc : B (27 / 40) (17 / 25) c) : B (49670306326650351 / 100000000000000000) (250926881304570861 / 500000000000000000) (c * (kdot c)) := bmul (sGlobal66_hz38 hc) (sGlobal66_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal66_hz87 {c : ℝ} (hc : B (27 / 40) (17 / 25) c) : B (-268465098946741903 / 1000000000000000000) (-130924193094373143 / 500000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (sGlobal66_hz85 hc) (sGlobal66_hz86 hc) (by norm_num) (by norm_num)

theorem sGlobal66_hz88 {c : ℝ} (hc : B (27 / 40) (17 / 25) c) : B (-6563971669247840348847 / 1000000000000000000) (-6402193042314808359569 / 1000000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) := bmul sGlobal66_hz80 (sGlobal66_hz87 hc) (by norm_num) (by norm_num)

theorem sGlobal66_hz89 {c : ℝ} (hc : B (27 / 40) (17 / 25) c) : B (-410248229327990021803 / 125000000000000000) (-400137065144675522473 / 125000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) / (2 : ℝ)) := bdiv (sGlobal66_hz88 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal66_hz90 {c : ℝ} (hc : B (27 / 40) (17 / 25) c) : B (-410248229327990021803 / 125000000000000000) (-400137065144675522473 / 125000000000000000) (s3Cpp 12225 c) := by
    convert (sGlobal66_hz89 hc) using 1 <;>
      norm_num [s3Cpp, mA] <;> ring

theorem sGlobal66_hz91 {c : ℝ} (hc : B (27 / 40) (17 / 25) c) : B (3355503575496949353501 / 500000000000000000) (3385978048856185912239 / 500000000000000000) ((s3Cpa 12225 c) + (s3r1 12225 46)) := badd (sGlobal66_hz84 hc) sGlobal66_hz33 (by norm_num) (by norm_num)

theorem sGlobal66_hz92 {c : ℝ} (hc : B (27 / 40) (17 / 25) c) : B (60763869757573525137 / 1000000000000000000) (61315723417826904873 / 1000000000000000000) (((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) := bdiv (sGlobal66_hz91 hc) sGlobal66_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal66_hz93 {c : ℝ} (hc : B (27 / 40) (17 / 25) c) : B (60886552783067585549 / 1000000000000000000) (3839900402707560331 / 62500000000000000) ((((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) + (s3e0 12225 46)) := badd (sGlobal66_hz92 hc) sGlobal66_hz16 (by norm_num) (by norm_num)

theorem sGlobal66_hz94 {c : ℝ} (hc : B (27 / 40) (17 / 25) c) : B (60886552783067585549 / 1000000000000000000) (3839900402707560331 / 62500000000000000) (s3Lam 12225 46 c) := by
    convert (sGlobal66_hz93 hc) using 1 <;>
      norm_num [s3Lam] <;> ring

theorem sGlobal66_hz95 {c : ℝ} (hc : B (27 / 40) (17 / 25) c) : B (-400652803500178546103 / 125000000000000000) (-1562166557267455952483 / 500000000000000000) ((s3Cpp 12225 c) + (s3rpp 12225 46)) := badd (sGlobal66_hz90 hc) sGlobal66_hz37 (by norm_num) (by norm_num)

theorem sGlobal66_hz96 {c : ℝ} (hc : B (27 / 40) (17 / 25) c) : B (-1226822237349817483757 / 500000000000000000) (-1562166557267455952483 / 1000000000000000000) (if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) := bweaken (bfirst (sGlobal66_hz95 hc) (sGlobal66_hz76 hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem sGlobal66_hz97 {c : ℝ} (hc : B (27 / 40) (17 / 25) c) : B (1853586154902637573641 / 500000000000000000) (3774677786294703104869 / 1000000000000000000) ((s3Lam 12225 46 c)^2) := bsq (sGlobal66_hz94 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal66_hz98 {c : ℝ} (hc : B (27 / 40) (17 / 25) c) : B (135805682134730463 / 250000000000000000) (109732661737978257 / 200000000000000000) ((s3c1 12225 46 c)^2) := bsq (sGlobal66_hz72 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal66_hz99 {c : ℝ} (hc : B (27 / 40) (17 / 25) c) : B (90267338262021743 / 200000000000000000) (114194317865269537 / 250000000000000000) ((1 : ℝ) - ((s3c1 12225 46 c)^2)) := bsub (bpoint (1 : ℝ)) (sGlobal66_hz98 hc) (by norm_num) (by norm_num)

theorem sGlobal66_hz100 {c : ℝ} (hc : B (27 / 40) (17 / 25) c) : B (167953991339538563 / 250000000000000000) (337926497725865731 / 500000000000000000) (√((1 : ℝ) - ((s3c1 12225 46 c)^2))) := bsqrt (sGlobal66_hz99 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal66_hz101 {c : ℝ} (hc : B (27 / 40) (17 / 25) c) : B (84422884053340497 / 40000000000000000) (424650961083563101 / 200000000000000000) (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))) := bmul pi_mem (sGlobal66_hz100 hc) (by norm_num) (by norm_num)

theorem sGlobal66_hz102 {c : ℝ} (hc : B (27 / 40) (17 / 25) c) : B (872992798684794520739 / 500000000000000000) (447115474509229860259 / 250000000000000000) (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2))))) := bdiv (sGlobal66_hz97 hc) (sGlobal66_hz101 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal66_hz103 {c : ℝ} (hc : B (27 / 40) (17 / 25) c) : B (-176914719332511481509 / 250000000000000000) (226295340769463488553 / 1000000000000000000) ((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) := badd (sGlobal66_hz96 hc) (sGlobal66_hz102 hc) (by norm_num) (by norm_num)

theorem sGlobal66_hz104 : B (3762781186094069 / 250000000000000000) (376278118609407 / 25000000000000000) ((s3e0 12225 46)^2) := bsq sGlobal66_hz16 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal66_hz105 {c : ℝ} (hc : B (27 / 40) (17 / 25) c) : B (-2211386956891567343 / 3125000000000000) (226310391894207864833 / 1000000000000000000) (((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) := badd (sGlobal66_hz103 hc) sGlobal66_hz104 (by norm_num) (by norm_num)

theorem sGlobal66_hz106 {c : ℝ} (hc : B (27 / 40) (17 / 25) c) : B (-669146752754054279629 / 1000000000000000000) (264807465348332134849 / 1000000000000000000) ((((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) + (s3rs 12225 46 maskSlack)) := badd (sGlobal66_hz105 hc) sGlobal66_hz29 (by norm_num) (by norm_num)

theorem sGlobal66_hz107 {c : ℝ} (hc : B (27 / 40) (17 / 25) c) : B (-669146752754054279629 / 1000000000000000000) (264807465348332134849 / 1000000000000000000) (s3U 12225 46 maskSlack c) := by
    convert (sGlobal66_hz106 hc) using 1 <;>
      norm_num [s3U] <;> ring

theorem sGlobal66_hz108 {c : ℝ} (hc : B (27 / 40) (17 / 25) c) : B (-1679374620623206224621 / 500000000000000000) (-409732490972486998173 / 125000000000000000) ((s3Cpp 12225 c) - (s3rpp 12225 46)) := bsub (sGlobal66_hz90 hc) sGlobal66_hz37 (by norm_num) (by norm_num)

theorem sGlobal66_hz109 {c : ℝ} (hc : B (27 / 40) (17 / 25) c) : B (-1679374620623206224621 / 500000000000000000) (-409732490972486998173 / 125000000000000000) (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ)) := bweaken (bmin (sGlobal66_hz108 hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem sGlobal66_hz110 {c : ℝ} (hc : B (27 / 40) (17 / 25) c) : B (-514234297482095280877 / 200000000000000000) (-2503548827070423103337 / 1000000000000000000) ((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) := bmul (sGlobal66_hz76 hc) (sGlobal66_hz109 hc) (by norm_num) (by norm_num)

theorem sGlobal66_hz111 {c : ℝ} (hc : B (27 / 40) (17 / 25) c) : B (-514237307707044156133 / 200000000000000000) (-2503563878195167479613 / 1000000000000000000) (((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) := bsub (sGlobal66_hz110 hc) sGlobal66_hz104 (by norm_num) (by norm_num)

theorem sGlobal66_hz112 {c : ℝ} (hc : B (27 / 40) (17 / 25) c) : B (-2609683611989345050681 / 1000000000000000000) (-158878809477900921859 / 62500000000000000) ((((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) - (s3rs 12225 46 maskSlack)) := bsub (sGlobal66_hz111 hc) sGlobal66_hz29 (by norm_num) (by norm_num)

theorem sGlobal66_hz113 {c : ℝ} (hc : B (27 / 40) (17 / 25) c) : B (-2609683611989345050681 / 1000000000000000000) (-158878809477900921859 / 62500000000000000) (s3L 12225 46 maskSlack c) := by
    convert (sGlobal66_hz112 hc) using 1 <;>
      norm_num [s3L] <;> ring

theorem sGlobal66_hz114 {c : ℝ} (hc : B (27 / 40) (17 / 25) c) : B 0 (669146752754054279629 / 1000000000000000000) |(s3U 12225 46 maskSlack c)| := bweaken (babs (sGlobal66_hz107 hc)) (by norm_num) (by norm_num)

theorem sGlobal66_hz115 {c : ℝ} (hc : B (27 / 40) (17 / 25) c) : B 0 (2609683611989345050681 / 1000000000000000000) |(s3L 12225 46 maskSlack c)| := bweaken (babs (sGlobal66_hz113 hc)) (by norm_num) (by norm_num)

theorem sGlobal66_hz116 {c : ℝ} (hc : B (27 / 40) (17 / 25) c) : B 0 (2609683611989345050681 / 1000000000000000000) (max |(s3U 12225 46 maskSlack c)| |(s3L 12225 46 maskSlack c)|) := bweaken (bmax (sGlobal66_hz114 hc) (sGlobal66_hz115 hc)) (by norm_num) (by norm_num)

theorem sGlobal66_hz117 {c : ℝ} (hc : B (27 / 40) (17 / 25) c) : B 0 (2609683611989345050681 / 1000000000000000000) (s3nks 12225 46 maskSlack c) := by
    convert (sGlobal66_hz116 hc) using 1 <;>
      norm_num [s3nks] <;> ring

theorem sGlobal66 {c : ℝ} (hc : B (27 / 40) (17 / 25) c) :
    0 < s3am 12225 46 ∧ 0 ≤ s3dm 12225 46 c ∧
    s3dm 12225 46 c ^ 2 ≤ 2 * s3ap 12225 46 ^ 2 ∧ s3c1 12225 46 c < 1 ∧
    0 ≤ s3Cpa 12225 c - s3r1 12225 46 ∧
    s3e0 12225 46 ≤ (s3Cpa 12225 c - s3r1 12225 46) / s3ap 12225 46 ∧
    s3nks 12225 46 maskSlack c ≤ 12225 * (6671 / 31250) := by

  refine ⟨lt_of_lt_of_le (by norm_num) sGlobal66_hz14.1,
    le_trans (by norm_num) (sGlobal66_hz64 hc).1, ?_,
    lt_of_le_of_lt (sGlobal66_hz72 hc).2 (by norm_num), ?_, ?_,
    le_trans (sGlobal66_hz117 hc).2 (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (sGlobal66_hz64 hc).1) (sGlobal66_hz64 hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) sGlobal66_hz9.1 2
    nlinarith only [h1, h2]
  · linarith only [(sGlobal66_hz84 hc).1, sGlobal66_hz33.2]
  · have hap : 0 < s3ap 12225 46 := lt_of_lt_of_le (by norm_num) sGlobal66_hz9.1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul sGlobal66_hz16.2 sGlobal66_hz9.2 (le_trans (by norm_num) sGlobal66_hz9.1) (by norm_num)
    linarith only [h, (sGlobal66_hz84 hc).1, sGlobal66_hz33.2]

end BstLean.Part255
