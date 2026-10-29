import BstLean.Part255SGlobal63
import BstLean.Part255Numeric10
namespace BstLean.Part255
open Real BstLean.Part130 BstLean.Part182 BstLean.Part197 BstLean.Part246
theorem sGlobal67_hz0 : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal67_hz1 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) ((√(23 : ℝ)) / (12225 : ℝ)) := bdiv sGlobal67_hz0 (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal67_hz2 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) maskSlack := by
    convert sGlobal67_hz1 using 1 <;>
      norm_num [maskSlack] <;> ring

theorem sGlobal67_hz3 : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal67_hz4 : B (6395294793910793 / 500000000000000000) (12790589587821587 / 1000000000000000000) (√((2 / 12225) : ℝ)) := bsqrt (bpoint ((2 / 12225) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal67_hz5 : B (7230130686979 / 62500000000000000) (23136418198333 / 200000000000000000) (√((2 / 149450625) : ℝ)) := bsqrt (bpoint ((2 / 149450625) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal67_hz6 : B (2211334438749598093 / 20000000000000000) (110566721937479904651 / 1000000000000000000) (√(12225 : ℝ)) := bsqrt (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal67_hz7 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))) := bmul sGlobal67_hz3 sGlobal67_hz4 (by norm_num) (by norm_num)

theorem sGlobal67_hz8 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) ((√(12225 : ℝ)) + ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := badd sGlobal67_hz6 sGlobal67_hz7 (by norm_num) (by norm_num)

theorem sGlobal67_hz9 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) (s3ap 12225 46) := by
    convert sGlobal67_hz8 using 1 <;>
      norm_num [s3ap, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal67_hz10 : B (163599182004089 / 1000000000000000000) (16359918200409 / 100000000000000000) ((2 : ℝ) / (12225 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal67_hz11 : B (1222499983640081799591 / 100000000000000000) (12224999836400817995911 / 1000000000000000000) ((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ))) := bsub (bpoint (12225 : ℝ)) sGlobal67_hz10 (by norm_num) (by norm_num)

theorem sGlobal67_hz12 : B (110566721197658827907 / 1000000000000000000) (27641680299414706977 / 250000000000000000) (√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) := bsqrt sGlobal67_hz11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal67_hz13 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) ((√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) - ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bsub sGlobal67_hz12 sGlobal67_hz7 (by norm_num) (by norm_num)

theorem sGlobal67_hz14 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) (s3am 12225 46) := by
    convert sGlobal67_hz13 using 1 <;>
      norm_num [s3am, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal67_hz15 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√((2 / 12225) : ℝ)) * (√(92 : ℝ))) := bmul sGlobal67_hz4 sGlobal67_hz3 (by norm_num) (by norm_num)

theorem sGlobal67_hz16 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) (s3e0 12225 46) := by
    convert sGlobal67_hz15 using 1 <;>
      norm_num [s3e0, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal67_hz17 : B (250196148528560847 / 500000000000000000) (100078459411424339 / 200000000000000000) (((1 / 2) : ℝ) + maskSlack) := badd (bpoint ((1 / 2) : ℝ)) sGlobal67_hz2 (by norm_num) (by norm_num)

theorem sGlobal67_hz18 : B (59827153232297998295487 / 800000000000000) (23930861292919199366019 / 320000000000000) ((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack)) := bmul (bpoint (149450625 : ℝ)) sGlobal67_hz17 (by norm_num) (by norm_num)

theorem sGlobal67_hz19 : B (1729554180017180009583 / 200000000000000000) (8647770900085900056557 / 1000000000000000000) (√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) := bsqrt sGlobal67_hz18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal67_hz20 : B (4328681281566262743499 / 500000000000000000) (8657362563132525495641 / 1000000000000000000) ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))) := badd sGlobal67_hz19 sGlobal67_hz3 (by norm_num) (by norm_num)

theorem sGlobal67_hz21 : B (110732771457999278473 / 1000000000000000000) (55366385728999643621 / 500000000000000000) ((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ)))) := bmul sGlobal67_hz4 sGlobal67_hz20 (by norm_num) (by norm_num)

theorem sGlobal67_hz22 : B (209099159 / 15625000000000000) (13382346177 / 1000000000000000000) ((2 : ℝ) / (149450625 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (149450625 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal67_hz23 : B (2452349334953899930479 / 200000000000000000) (12261746674769501594427 / 1000000000000000000) (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2) := bsq sGlobal67_hz21 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal67_hz24 : B (82045469362091 / 500000000000000000) (32818187747289 / 200000000000000000) (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2)) := bmul sGlobal67_hz22 sGlobal67_hz23 (by norm_num) (by norm_num)

theorem sGlobal67_hz25 : B (82045469362091 / 250000000000000000) (32818187747289 / 100000000000000000) ((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) := bmul (bpoint (2 : ℝ)) sGlobal67_hz24 (by norm_num) (by norm_num)

theorem sGlobal67_hz26 : B (117258080744995992792057 / 1000000000000000000) (58629040372497996396029 / 500000000000000000) (√(13749457500 : ℝ)) := bsqrt (bpoint (13749457500 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal67_hz27 : B (117304080744995992792057 / 1000000000000000000) (58652040372497996396029 / 500000000000000000) ((√(13749457500 : ℝ)) + (46 : ℝ)) := badd sGlobal67_hz26 (bpoint (46 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal67_hz28 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal67_hz25 sGlobal67_hz27 (by norm_num) (by norm_num)

theorem sGlobal67_hz29 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (s3rs 12225 46 maskSlack) := by
    convert sGlobal67_hz28 using 1 <;>
      norm_num [s3rs, s3pp, s3K, mA, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal67_hz30 : B (490797546012267 / 1000000000000000000) (49079754601227 / 100000000000000000) ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (3 : ℝ)) sGlobal67_hz10 (by norm_num) (by norm_num)

theorem sGlobal67_hz31 : B (490797546012267 / 500000000000000000) (49079754601227 / 50000000000000000) ((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal67_hz30 (by norm_num) (by norm_num)

theorem sGlobal67_hz32 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal67_hz31 sGlobal67_hz27 (by norm_num) (by norm_num)

theorem sGlobal67_hz33 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (s3r1 12225 46) := by
    convert sGlobal67_hz32 using 1 <;>
      norm_num [s3r1, mA] <;> ring

theorem sGlobal67_hz34 : B (163599182004089 / 500000000000000000) (16359918200409 / 50000000000000000) ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (2 : ℝ)) sGlobal67_hz10 (by norm_num) (by norm_num)

theorem sGlobal67_hz35 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal67_hz34 (by norm_num) (by norm_num)

theorem sGlobal67_hz36 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal67_hz35 sGlobal67_hz27 (by norm_num) (by norm_num)

theorem sGlobal67_hz37 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (s3rpp 12225 46) := by
    convert sGlobal67_hz36 using 1 <;>
      norm_num [s3rpp, mA] <;> ring

theorem sGlobal67_hz38 {c : ℝ} (hc : B (17 / 25) (137 / 200) c) : B (17 / 25) (137 / 200) c := hc

theorem sGlobal67_hz39 : B (147604047826218153 / 200000000000000000) (738020239131090767 / 1000000000000000000) (kdot ((17 / 25))) := by
    constructor
    · apply bkdot_lower (q := (436435780471984763 / 1000000000000000000)) (a := (20575842303374401 / 50000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (218217890235992381 / 500000000000000000)) (a := (205758423033744009 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal67_hz40 : B (289 / 625) (289 / 625) (((17 / 25) : ℝ)^2) := bsq (bpoint ((17 / 25) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal67_hz41 : B (336 / 625) (336 / 625) ((1 : ℝ) - (((17 / 25) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal67_hz40 (by norm_num) (by norm_num)

theorem sGlobal67_hz42 : B (733212111192934401 / 1000000000000000000) (366606055596467201 / 500000000000000000) (√((1 : ℝ) - (((17 / 25) : ℝ)^2))) := bsqrt sGlobal67_hz41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal67_hz43 : B (233388663662399819 / 1000000000000000000) (11669433183119991 / 50000000000000000) ((√((1 : ℝ) - (((17 / 25) : ℝ)^2))) / Real.pi) := bdiv sGlobal67_hz42 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal67_hz44 : B (12546344065228543 / 25000000000000000) (250926881304570861 / 500000000000000000) (((17 / 25) : ℝ) * (kdot ((17 / 25)))) := bmul (bpoint ((17 / 25) : ℝ)) sGlobal67_hz39 (by norm_num) (by norm_num)

theorem sGlobal67_hz45 : B (735242426271541539 / 1000000000000000000) (367621213135770771 / 500000000000000000) (((√((1 : ℝ) - (((17 / 25) : ℝ)^2))) / Real.pi) + (((17 / 25) : ℝ) * (kdot ((17 / 25))))) := badd sGlobal67_hz43 sGlobal67_hz44 (by norm_num) (by norm_num)

theorem sGlobal67_hz46 : B (735242426271541539 / 1000000000000000000) (367621213135770771 / 500000000000000000) (kappa ((17 / 25))) := by rw [kappa_eq]; exact sGlobal67_hz45

theorem sGlobal67_hz47 : B (740197817494345467 / 1000000000000000000) (74019781749434547 / 100000000000000000) (kdot ((137 / 200))) := by
    constructor
    · apply bkdot_lower (q := (432369772507331441 / 1000000000000000000)) (a := (40809631397317949 / 100000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (5404622156341643 / 12500000000000000)) (a := (12753009811661859 / 31250000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal67_hz48 : B (18769 / 40000) (18769 / 40000) (((137 / 200) : ℝ)^2) := bsq (bpoint ((137 / 200) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal67_hz49 : B (21231 / 40000) (21231 / 40000) ((1 : ℝ) - (((137 / 200) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal67_hz48 (by norm_num) (by norm_num)

theorem sGlobal67_hz50 : B (728543066674853477 / 1000000000000000000) (364271533337426739 / 500000000000000000) (√((1 : ℝ) - (((137 / 200) : ℝ)^2))) := bsqrt sGlobal67_hz49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal67_hz51 : B (57975615158315607 / 250000000000000000) (23190246063326243 / 100000000000000000) ((√((1 : ℝ) - (((137 / 200) : ℝ)^2))) / Real.pi) := bdiv sGlobal67_hz50 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal67_hz52 : B (126758876245906661 / 250000000000000000) (507035504983626647 / 1000000000000000000) (((137 / 200) : ℝ) * (kdot ((137 / 200)))) := bmul (bpoint ((137 / 200) : ℝ)) sGlobal67_hz47 (by norm_num) (by norm_num)

theorem sGlobal67_hz53 : B (46183622851055567 / 62500000000000000) (738937965616889077 / 1000000000000000000) (((√((1 : ℝ) - (((137 / 200) : ℝ)^2))) / Real.pi) + (((137 / 200) : ℝ) * (kdot ((137 / 200))))) := badd sGlobal67_hz51 sGlobal67_hz52 (by norm_num) (by norm_num)

theorem sGlobal67_hz54 : B (46183622851055567 / 62500000000000000) (738937965616889077 / 1000000000000000000) (kappa ((137 / 200))) := by rw [kappa_eq]; exact sGlobal67_hz53

theorem sGlobal67_hz55 {c : ℝ} (hc : B (17 / 25) (137 / 200) c) : B (735242426271541539 / 1000000000000000000) (738937965616889077 / 1000000000000000000) (kappa c) := bkappa (sGlobal67_hz38 hc) (by norm_num) (by norm_num) sGlobal67_hz46.1 sGlobal67_hz54.2

theorem sGlobal67_hz56 : B 24450 24450 ((2 : ℝ) * (12225 : ℝ)) := bmul (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal67_hz57 {c : ℝ} (hc : B (17 / 25) (137 / 200) c) : B (261062034383110923 / 1000000000000000000) (264757573728458461 / 1000000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (sGlobal67_hz55 hc) (by norm_num) (by norm_num)

theorem sGlobal67_hz58 {c : ℝ} (hc : B (17 / 25) (137 / 200) c) : B (127659334813341241347 / 20000000000000000) (129466453553216187429 / 20000000000000000) (((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) := bmul sGlobal67_hz56 (sGlobal67_hz57 hc) (by norm_num) (by norm_num)

theorem sGlobal67_hz59 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (4 : ℝ)) sGlobal67_hz10 (by norm_num) (by norm_num)

theorem sGlobal67_hz60 {c : ℝ} (hc : B (17 / 25) (137 / 200) c) : B (638296608627033405099 / 100000000000000000) (3236661011632040677547 / 500000000000000000) ((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bsub (sGlobal67_hz58 hc) sGlobal67_hz59 (by norm_num) (by norm_num)

theorem sGlobal67_hz61 {c : ℝ} (hc : B (17 / 25) (137 / 200) c) : B (79893467106330628007 / 1000000000000000000) (8045695758145519981 / 100000000000000000) (√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) := bsqrt (sGlobal67_hz60 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal67_hz62 : B (30670756373515103 / 125000000000000000) (122683025494060423 / 500000000000000000) ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal67_hz7 (by norm_num) (by norm_num)

theorem sGlobal67_hz63 {c : ℝ} (hc : B (17 / 25) (137 / 200) c) : B (79648101055342507161 / 1000000000000000000) (40105795765233539493 / 500000000000000000) ((√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) - ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))))) := bsub (sGlobal67_hz61 hc) sGlobal67_hz62 (by norm_num) (by norm_num)

theorem sGlobal67_hz64 {c : ℝ} (hc : B (17 / 25) (137 / 200) c) : B (79648101055342507161 / 1000000000000000000) (40105795765233539493 / 500000000000000000) (s3dm 12225 46 c) := by
    convert (sGlobal67_hz63 hc) using 1 <;>
      norm_num [s3dm, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal67_hz65 : B (6126072185528622723889 / 500000000000000000) (2450428874211449090087 / 200000000000000000) ((s3ap 12225 46)^2) := bsq sGlobal67_hz9 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal67_hz66 : B (6126072185528622723889 / 250000000000000000) (2450428874211449090087 / 100000000000000000) ((2 : ℝ) * ((s3ap 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal67_hz65 (by norm_num) (by norm_num)

theorem sGlobal67_hz67 {c : ℝ} (hc : B (17 / 25) (137 / 200) c) : B (6343820001722052202967 / 1000000000000000000) (257355976634019921543 / 40000000000000000) ((s3dm 12225 46 c)^2) := bsq (sGlobal67_hz64 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal67_hz68 {c : ℝ} (hc : B (17 / 25) (137 / 200) c) : B (18070389326263992856981 / 1000000000000000000) (18160468740392438697903 / 1000000000000000000) (((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) := bsub sGlobal67_hz66 (sGlobal67_hz67 hc) (by norm_num) (by norm_num)

theorem sGlobal67_hz69 : B (1524735695971823534271 / 125000000000000000) (609894278388729413841 / 50000000000000000) ((s3am 12225 46)^2) := bsq sGlobal67_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal67_hz70 : B (1524735695971823534271 / 62500000000000000) (609894278388729413841 / 25000000000000000) ((2 : ℝ) * ((s3am 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal67_hz69 (by norm_num) (by norm_num)

theorem sGlobal67_hz71 {c : ℝ} (hc : B (17 / 25) (137 / 200) c) : B (29628724135605739 / 40000000000000000) (372205261303039067 / 500000000000000000) ((((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) / ((2 : ℝ) * ((s3am 12225 46)^2))) := bdiv (sGlobal67_hz68 hc) sGlobal67_hz70 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal67_hz72 {c : ℝ} (hc : B (17 / 25) (137 / 200) c) : B (29628724135605739 / 40000000000000000) (372205261303039067 / 500000000000000000) (s3c1 12225 46 c) := by
    convert (sGlobal67_hz71 hc) using 1 <;>
      norm_num [s3c1] <;> ring

theorem sGlobal67_hz73 {c : ℝ} (hc : B (17 / 25) (137 / 200) c) : B (147604047826218153 / 200000000000000000) (74019781749434547 / 100000000000000000) (kdot c) := bkdot (sGlobal67_hz38 hc) sGlobal67_hz39.1 sGlobal67_hz47.2

theorem sGlobal67_hz74 : B (11961165185371251 / 15625000000000000) (382757285931880033 / 500000000000000000) (kdot ((29628724135605739 / 40000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (385941850119072131 / 1000000000000000000)) (a := (46041106150416799 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (38594185011907213 / 100000000000000000)) (a := (36832884920333439 / 100000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal67_hz75 : B (383634700677760109 / 500000000000000000) (38363470067776011 / 50000000000000000) (kdot ((372205261303039067 / 500000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (9569453683606193 / 25000000000000000)) (a := (365572369483526187 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (382778147344247719 / 1000000000000000000)) (a := (73114473896705237 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal67_hz76 {c : ℝ} (hc : B (17 / 25) (137 / 200) c) : B (11961165185371251 / 15625000000000000) (38363470067776011 / 50000000000000000) (kdot (s3c1 12225 46 c)) := bkdot (sGlobal67_hz72 hc) sGlobal67_hz74.1 sGlobal67_hz75.2

theorem sGlobal67_hz77 {c : ℝ} (hc : B (17 / 25) (137 / 200) c) : B (289 / 625) (18769 / 40000) (c^2) := bsq (sGlobal67_hz38 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal67_hz78 {c : ℝ} (hc : B (17 / 25) (137 / 200) c) : B (21231 / 40000) (336 / 625) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (sGlobal67_hz77 hc) (by norm_num) (by norm_num)

theorem sGlobal67_hz79 {c : ℝ} (hc : B (17 / 25) (137 / 200) c) : B (728543066674853477 / 1000000000000000000) (366606055596467201 / 500000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (sGlobal67_hz78 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal67_hz80 : B (39119999999999765769 / 1600000000000000) (3912000000000000489 / 160000000000000) ((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (149450625 : ℝ)) sGlobal67_hz10 (by norm_num) (by norm_num)

theorem sGlobal67_hz81 {c : ℝ} (hc : B (17 / 25) (137 / 200) c) : B (268839764142336783 / 500000000000000000) (135680501116357849 / 250000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (sGlobal67_hz79 hc) (sGlobal67_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal67_hz82 {c : ℝ} (hc : B (17 / 25) (137 / 200) c) : B (13146264466560189975441 / 1000000000000000000) (2653910601835959858179 / 200000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) := bmul sGlobal67_hz80 (sGlobal67_hz81 hc) (by norm_num) (by norm_num)

theorem sGlobal67_hz83 {c : ℝ} (hc : B (17 / 25) (137 / 200) c) : B (164328305832002374693 / 25000000000000000) (829347063073737455681 / 125000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) / (2 : ℝ)) := bdiv (sGlobal67_hz82 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal67_hz84 {c : ℝ} (hc : B (17 / 25) (137 / 200) c) : B (164328305832002374693 / 25000000000000000) (829347063073737455681 / 125000000000000000) (s3Cpa 12225 c) := by
    convert (sGlobal67_hz83 hc) using 1 <;>
      norm_num [s3Cpa, mA] <;> ring

theorem sGlobal67_hz85 {c : ℝ} (hc : B (17 / 25) (137 / 200) c) : B (57975615158315607 / 250000000000000000) (11669433183119991 / 50000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (sGlobal67_hz79 hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal67_hz86 {c : ℝ} (hc : B (17 / 25) (137 / 200) c) : B (12546344065228543 / 25000000000000000) (507035504983626647 / 1000000000000000000) (c * (kdot c)) := bmul (sGlobal67_hz38 hc) (sGlobal67_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal67_hz87 {c : ℝ} (hc : B (17 / 25) (137 / 200) c) : B (-275133044350364219 / 1000000000000000000) (-2684650989467419 / 10000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (sGlobal67_hz85 hc) (sGlobal67_hz86 hc) (by norm_num) (by norm_num)

theorem sGlobal67_hz88 {c : ℝ} (hc : B (17 / 25) (137 / 200) c) : B (-3363501467183202997713 / 500000000000000000) (-6563971669247800153219 / 1000000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) := bmul sGlobal67_hz80 (sGlobal67_hz87 hc) (by norm_num) (by norm_num)

theorem sGlobal67_hz89 {c : ℝ} (hc : B (17 / 25) (137 / 200) c) : B (-3363501467183202997713 / 1000000000000000000) (-3281985834623900076609 / 1000000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) / (2 : ℝ)) := bdiv (sGlobal67_hz88 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal67_hz90 {c : ℝ} (hc : B (17 / 25) (137 / 200) c) : B (-3363501467183202997713 / 1000000000000000000) (-3281985834623900076609 / 1000000000000000000) (s3Cpp 12225 c) := by
    convert (sGlobal67_hz89 hc) using 1 <;>
      norm_num [s3Cpp, mA] <;> ring

theorem sGlobal67_hz91 {c : ℝ} (hc : B (17 / 25) (137 / 200) c) : B (6688277343213832696121 / 1000000000000000000) (3374960807261819028837 / 500000000000000000) ((s3Cpa 12225 c) + (s3r1 12225 46)) := badd (sGlobal67_hz84 hc) sGlobal67_hz33 (by norm_num) (by norm_num)

theorem sGlobal67_hz92 {c : ℝ} (hc : B (17 / 25) (137 / 200) c) : B (30279032955983859257 / 500000000000000000) (30558107645437497779 / 500000000000000000) (((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) := bdiv (sGlobal67_hz91 hc) sGlobal67_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal67_hz93 {c : ℝ} (hc : B (17 / 25) (137 / 200) c) : B (30340374468730889463 / 500000000000000000) (61238898316369055981 / 1000000000000000000) ((((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) + (s3e0 12225 46)) := badd (sGlobal67_hz92 hc) sGlobal67_hz16 (by norm_num) (by norm_num)

theorem sGlobal67_hz94 {c : ℝ} (hc : B (17 / 25) (137 / 200) c) : B (30340374468730889463 / 500000000000000000) (61238898316369055981 / 1000000000000000000) (s3Lam 12225 46 c) := by
    convert (sGlobal67_hz93 hc) using 1 <;>
      norm_num [s3Lam] <;> ring

theorem sGlobal67_hz95 {c : ℝ} (hc : B (17 / 25) (137 / 200) c) : B (-3286738060560711192113 / 1000000000000000000) (-3205222428001407801791 / 1000000000000000000) ((s3Cpp 12225 c) + (s3rpp 12225 46)) := badd (sGlobal67_hz90 hc) sGlobal67_hz37 (by norm_num) (by norm_num)

theorem sGlobal67_hz96 {c : ℝ} (hc : B (17 / 25) (137 / 200) c) : B (-15761334650867627743 / 6250000000000000) (-320522242800140780179 / 200000000000000000) (if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) := bweaken (bfirst (sGlobal67_hz95 hc) (sGlobal67_hz76 hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem sGlobal67_hz97 {c : ℝ} (hc : B (17 / 25) (137 / 200) c) : B (736430658322253762423 / 200000000000000000) (3750202667002588799243 / 1000000000000000000) ((s3Lam 12225 46 c)^2) := bsq (sGlobal67_hz94 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal67_hz98 {c : ℝ} (hc : B (17 / 25) (137 / 200) c) : B (274331654344945639 / 500000000000000000) (110829405233330873 / 200000000000000000) ((s3c1 12225 46 c)^2) := bsq (sGlobal67_hz72 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal67_hz99 {c : ℝ} (hc : B (17 / 25) (137 / 200) c) : B (89170594766669127 / 200000000000000000) (225668345655054361 / 500000000000000000) ((1 : ℝ) - ((s3c1 12225 46 c)^2)) := bsub (bpoint (1 : ℝ)) (sGlobal67_hz98 hc) (by norm_num) (by norm_num)

theorem sGlobal67_hz100 {c : ℝ} (hc : B (17 / 25) (137 / 200) c) : B (333861114025482771 / 500000000000000000) (335907982679077129 / 500000000000000000) (√((1 : ℝ) - ((s3c1 12225 46 c)^2))) := bsqrt (sGlobal67_hz99 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal67_hz101 {c : ℝ} (hc : B (17 / 25) (137 / 200) c) : B (2097711246283521911 / 1000000000000000000) (422114420266702489 / 200000000000000000) (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))) := bmul pi_mem (sGlobal67_hz100 hc) (by norm_num) (by norm_num)

theorem sGlobal67_hz102 {c : ℝ} (hc : B (17 / 25) (137 / 200) c) : B (1744623312932447042431 / 1000000000000000000) (1787759241719639368623 / 1000000000000000000) (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2))))) := bdiv (sGlobal67_hz97 hc) (sGlobal67_hz101 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal67_hz103 {c : ℝ} (hc : B (17 / 25) (137 / 200) c) : B (-777190231206373396449 / 1000000000000000000) (11571751732433466733 / 62500000000000000) ((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) := badd (sGlobal67_hz96 hc) (sGlobal67_hz102 hc) (by norm_num) (by norm_num)

theorem sGlobal67_hz104 : B (3762781186094069 / 250000000000000000) (376278118609407 / 25000000000000000) ((s3e0 12225 46)^2) := bsq sGlobal67_hz16 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal67_hz105 {c : ℝ} (hc : B (17 / 25) (137 / 200) c) : B (-777175180081629020173 / 1000000000000000000) (23145384855459980501 / 125000000000000000) (((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) := badd (sGlobal67_hz103 hc) sGlobal67_hz104 (by norm_num) (by norm_num)

theorem sGlobal67_hz106 {c : ℝ} (hc : B (17 / 25) (137 / 200) c) : B (-369339053315190875021 / 500000000000000000) (27957519037225514253 / 125000000000000000) ((((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) + (s3rs 12225 46 maskSlack)) := badd (sGlobal67_hz105 hc) sGlobal67_hz29 (by norm_num) (by norm_num)

theorem sGlobal67_hz107 {c : ℝ} (hc : B (17 / 25) (137 / 200) c) : B (-369339053315190875021 / 500000000000000000) (27957519037225514253 / 125000000000000000) (s3U 12225 46 maskSlack c) := by
    convert (sGlobal67_hz106 hc) using 1 <;>
      norm_num [s3U] <;> ring

theorem sGlobal67_hz108 {c : ℝ} (hc : B (17 / 25) (137 / 200) c) : B (-3440264873805695272531 / 1000000000000000000) (-3358749241246391882209 / 1000000000000000000) ((s3Cpp 12225 c) - (s3rpp 12225 46)) := bsub (sGlobal67_hz90 hc) sGlobal67_hz37 (by norm_num) (by norm_num)

theorem sGlobal67_hz109 {c : ℝ} (hc : B (17 / 25) (137 / 200) c) : B (-3440264873805695272531 / 1000000000000000000) (-3358749241246391882209 / 1000000000000000000) (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ)) := bweaken (bmin (sGlobal67_hz108 hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem sGlobal67_hz110 {c : ℝ} (hc : B (17 / 25) (137 / 200) c) : B (-1319804985114660063469 / 500000000000000000) (-1285585743705230323293 / 500000000000000000) ((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) := bmul (sGlobal67_hz76 hc) (sGlobal67_hz109 hc) (by norm_num) (by norm_num)

theorem sGlobal67_hz111 {c : ℝ} (hc : B (17 / 25) (137 / 200) c) : B (-1319812510677032251609 / 500000000000000000) (-1285593269267602511431 / 500000000000000000) (((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) := bsub (sGlobal67_hz110 hc) sGlobal67_hz104 (by norm_num) (by norm_num)

theorem sGlobal67_hz112 {c : ℝ} (hc : B (17 / 25) (137 / 200) c) : B (-1339061047404094386617 / 500000000000000000) (-2609683611986452292993 / 1000000000000000000) ((((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) - (s3rs 12225 46 maskSlack)) := bsub (sGlobal67_hz111 hc) sGlobal67_hz29 (by norm_num) (by norm_num)

theorem sGlobal67_hz113 {c : ℝ} (hc : B (17 / 25) (137 / 200) c) : B (-1339061047404094386617 / 500000000000000000) (-2609683611986452292993 / 1000000000000000000) (s3L 12225 46 maskSlack c) := by
    convert (sGlobal67_hz112 hc) using 1 <;>
      norm_num [s3L] <;> ring

theorem sGlobal67_hz114 {c : ℝ} (hc : B (17 / 25) (137 / 200) c) : B 0 (369339053315190875021 / 500000000000000000) |(s3U 12225 46 maskSlack c)| := bweaken (babs (sGlobal67_hz107 hc)) (by norm_num) (by norm_num)

theorem sGlobal67_hz115 {c : ℝ} (hc : B (17 / 25) (137 / 200) c) : B 0 (1339061047404094386617 / 500000000000000000) |(s3L 12225 46 maskSlack c)| := bweaken (babs (sGlobal67_hz113 hc)) (by norm_num) (by norm_num)

theorem sGlobal67_hz116 {c : ℝ} (hc : B (17 / 25) (137 / 200) c) : B 0 (1339061047404094386617 / 500000000000000000) (max |(s3U 12225 46 maskSlack c)| |(s3L 12225 46 maskSlack c)|) := bweaken (bmax (sGlobal67_hz114 hc) (sGlobal67_hz115 hc)) (by norm_num) (by norm_num)

theorem sGlobal67_hz117 {c : ℝ} (hc : B (17 / 25) (137 / 200) c) : B 0 (1339061047404094386617 / 500000000000000000) (s3nks 12225 46 maskSlack c) := by
    convert (sGlobal67_hz116 hc) using 1 <;>
      norm_num [s3nks] <;> ring

theorem sGlobal67 {c : ℝ} (hc : B (17 / 25) (137 / 200) c) :
    0 < s3am 12225 46 ∧ 0 ≤ s3dm 12225 46 c ∧
    s3dm 12225 46 c ^ 2 ≤ 2 * s3ap 12225 46 ^ 2 ∧ s3c1 12225 46 c < 1 ∧
    0 ≤ s3Cpa 12225 c - s3r1 12225 46 ∧
    s3e0 12225 46 ≤ (s3Cpa 12225 c - s3r1 12225 46) / s3ap 12225 46 ∧
    s3nks 12225 46 maskSlack c ≤ 12225 * (21907 / 100000) := by

  refine ⟨lt_of_lt_of_le (by norm_num) sGlobal67_hz14.1,
    le_trans (by norm_num) (sGlobal67_hz64 hc).1, ?_,
    lt_of_le_of_lt (sGlobal67_hz72 hc).2 (by norm_num), ?_, ?_,
    le_trans (sGlobal67_hz117 hc).2 (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (sGlobal67_hz64 hc).1) (sGlobal67_hz64 hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) sGlobal67_hz9.1 2
    nlinarith only [h1, h2]
  · linarith only [(sGlobal67_hz84 hc).1, sGlobal67_hz33.2]
  · have hap : 0 < s3ap 12225 46 := lt_of_lt_of_le (by norm_num) sGlobal67_hz9.1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul sGlobal67_hz16.2 sGlobal67_hz9.2 (le_trans (by norm_num) sGlobal67_hz9.1) (by norm_num)
    linarith only [h, (sGlobal67_hz84 hc).1, sGlobal67_hz33.2]

end BstLean.Part255
