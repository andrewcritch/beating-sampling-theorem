import BstLean.Part255SGlobal13
import BstLean.Part255Numeric10
namespace BstLean.Part255
open Real BstLean.Part130 BstLean.Part182 BstLean.Part197 BstLean.Part246
theorem sGlobal17_hz0 : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal17_hz1 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) ((√(23 : ℝ)) / (12225 : ℝ)) := bdiv sGlobal17_hz0 (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal17_hz2 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) maskSlack := by
    convert sGlobal17_hz1 using 1 <;>
      norm_num [maskSlack] <;> ring

theorem sGlobal17_hz3 : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal17_hz4 : B (6395294793910793 / 500000000000000000) (12790589587821587 / 1000000000000000000) (√((2 / 12225) : ℝ)) := bsqrt (bpoint ((2 / 12225) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal17_hz5 : B (7230130686979 / 62500000000000000) (23136418198333 / 200000000000000000) (√((2 / 149450625) : ℝ)) := bsqrt (bpoint ((2 / 149450625) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal17_hz6 : B (2211334438749598093 / 20000000000000000) (110566721937479904651 / 1000000000000000000) (√(12225 : ℝ)) := bsqrt (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal17_hz7 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))) := bmul sGlobal17_hz3 sGlobal17_hz4 (by norm_num) (by norm_num)

theorem sGlobal17_hz8 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) ((√(12225 : ℝ)) + ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := badd sGlobal17_hz6 sGlobal17_hz7 (by norm_num) (by norm_num)

theorem sGlobal17_hz9 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) (s3ap 12225 46) := by
    convert sGlobal17_hz8 using 1 <;>
      norm_num [s3ap, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal17_hz10 : B (163599182004089 / 1000000000000000000) (16359918200409 / 100000000000000000) ((2 : ℝ) / (12225 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal17_hz11 : B (1222499983640081799591 / 100000000000000000) (12224999836400817995911 / 1000000000000000000) ((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ))) := bsub (bpoint (12225 : ℝ)) sGlobal17_hz10 (by norm_num) (by norm_num)

theorem sGlobal17_hz12 : B (110566721197658827907 / 1000000000000000000) (27641680299414706977 / 250000000000000000) (√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) := bsqrt sGlobal17_hz11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal17_hz13 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) ((√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) - ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bsub sGlobal17_hz12 sGlobal17_hz7 (by norm_num) (by norm_num)

theorem sGlobal17_hz14 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) (s3am 12225 46) := by
    convert sGlobal17_hz13 using 1 <;>
      norm_num [s3am, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal17_hz15 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√((2 / 12225) : ℝ)) * (√(92 : ℝ))) := bmul sGlobal17_hz4 sGlobal17_hz3 (by norm_num) (by norm_num)

theorem sGlobal17_hz16 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) (s3e0 12225 46) := by
    convert sGlobal17_hz15 using 1 <;>
      norm_num [s3e0, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal17_hz17 : B (250196148528560847 / 500000000000000000) (100078459411424339 / 200000000000000000) (((1 / 2) : ℝ) + maskSlack) := badd (bpoint ((1 / 2) : ℝ)) sGlobal17_hz2 (by norm_num) (by norm_num)

theorem sGlobal17_hz18 : B (59827153232297998295487 / 800000000000000) (23930861292919199366019 / 320000000000000) ((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack)) := bmul (bpoint (149450625 : ℝ)) sGlobal17_hz17 (by norm_num) (by norm_num)

theorem sGlobal17_hz19 : B (1729554180017180009583 / 200000000000000000) (8647770900085900056557 / 1000000000000000000) (√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) := bsqrt sGlobal17_hz18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal17_hz20 : B (4328681281566262743499 / 500000000000000000) (8657362563132525495641 / 1000000000000000000) ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))) := badd sGlobal17_hz19 sGlobal17_hz3 (by norm_num) (by norm_num)

theorem sGlobal17_hz21 : B (110732771457999278473 / 1000000000000000000) (55366385728999643621 / 500000000000000000) ((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ)))) := bmul sGlobal17_hz4 sGlobal17_hz20 (by norm_num) (by norm_num)

theorem sGlobal17_hz22 : B (209099159 / 15625000000000000) (13382346177 / 1000000000000000000) ((2 : ℝ) / (149450625 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (149450625 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal17_hz23 : B (2452349334953899930479 / 200000000000000000) (12261746674769501594427 / 1000000000000000000) (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2) := bsq sGlobal17_hz21 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal17_hz24 : B (82045469362091 / 500000000000000000) (32818187747289 / 200000000000000000) (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2)) := bmul sGlobal17_hz22 sGlobal17_hz23 (by norm_num) (by norm_num)

theorem sGlobal17_hz25 : B (82045469362091 / 250000000000000000) (32818187747289 / 100000000000000000) ((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) := bmul (bpoint (2 : ℝ)) sGlobal17_hz24 (by norm_num) (by norm_num)

theorem sGlobal17_hz26 : B (117258080744995992792057 / 1000000000000000000) (58629040372497996396029 / 500000000000000000) (√(13749457500 : ℝ)) := bsqrt (bpoint (13749457500 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal17_hz27 : B (117304080744995992792057 / 1000000000000000000) (58652040372497996396029 / 500000000000000000) ((√(13749457500 : ℝ)) + (46 : ℝ)) := badd sGlobal17_hz26 (bpoint (46 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal17_hz28 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal17_hz25 sGlobal17_hz27 (by norm_num) (by norm_num)

theorem sGlobal17_hz29 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (s3rs 12225 46 maskSlack) := by
    convert sGlobal17_hz28 using 1 <;>
      norm_num [s3rs, s3pp, s3K, mA, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal17_hz30 : B (490797546012267 / 1000000000000000000) (49079754601227 / 100000000000000000) ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (3 : ℝ)) sGlobal17_hz10 (by norm_num) (by norm_num)

theorem sGlobal17_hz31 : B (490797546012267 / 500000000000000000) (49079754601227 / 50000000000000000) ((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal17_hz30 (by norm_num) (by norm_num)

theorem sGlobal17_hz32 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal17_hz31 sGlobal17_hz27 (by norm_num) (by norm_num)

theorem sGlobal17_hz33 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (s3r1 12225 46) := by
    convert sGlobal17_hz32 using 1 <;>
      norm_num [s3r1, mA] <;> ring

theorem sGlobal17_hz34 : B (163599182004089 / 500000000000000000) (16359918200409 / 50000000000000000) ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (2 : ℝ)) sGlobal17_hz10 (by norm_num) (by norm_num)

theorem sGlobal17_hz35 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal17_hz34 (by norm_num) (by norm_num)

theorem sGlobal17_hz36 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal17_hz35 sGlobal17_hz27 (by norm_num) (by norm_num)

theorem sGlobal17_hz37 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (s3rpp 12225 46) := by
    convert sGlobal17_hz36 using 1 <;>
      norm_num [s3rpp, mA] <;> ring

theorem sGlobal17_hz38 {c : ℝ} (hc : B (43 / 100) (87 / 200) c) : B (43 / 100) (87 / 200) c := hc

theorem sGlobal17_hz39 : B (160371611308842497 / 250000000000000000) (128297289047923071 / 200000000000000000) (kdot ((43 / 100))) := by
    constructor
    · apply bkdot_lower (q := (631348872337156077 / 1000000000000000000)) (a := (56315177493046183 / 100000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (157837218084289019 / 250000000000000000)) (a := (70393971865474153 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal17_hz40 : B (1849 / 10000) (1849 / 10000) (((43 / 100) : ℝ)^2) := bsq (bpoint ((43 / 100) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal17_hz41 : B (8151 / 10000) (8151 / 10000) ((1 : ℝ) - (((43 / 100) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal17_hz40 (by norm_num) (by norm_num)

theorem sGlobal17_hz42 : B (902828887442133189 / 1000000000000000000) (90282888744213319 / 100000000000000000) (√((1 : ℝ) - (((43 / 100) : ℝ)^2))) := bsqrt sGlobal17_hz41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal17_hz43 : B (143689680202571887 / 500000000000000000) (11495174416205751 / 40000000000000000) ((√((1 : ℝ) - (((43 / 100) : ℝ)^2))) / Real.pi) := bdiv sGlobal17_hz42 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal17_hz44 : B (137919585725604547 / 500000000000000000) (275839171453034603 / 1000000000000000000) (((43 / 100) : ℝ) * (kdot ((43 / 100)))) := bmul (bpoint ((43 / 100) : ℝ)) sGlobal17_hz39 (by norm_num) (by norm_num)

theorem sGlobal17_hz45 : B (140804632964088217 / 250000000000000000) (281609265929089189 / 500000000000000000) (((√((1 : ℝ) - (((43 / 100) : ℝ)^2))) / Real.pi) + (((43 / 100) : ℝ) * (kdot ((43 / 100))))) := badd sGlobal17_hz43 sGlobal17_hz44 (by norm_num) (by norm_num)

theorem sGlobal17_hz46 : B (140804632964088217 / 250000000000000000) (281609265929089189 / 500000000000000000) (kappa ((43 / 100))) := by rw [kappa_eq]; exact sGlobal17_hz45

theorem sGlobal17_hz47 : B (643251632656853101 / 1000000000000000000) (25730065306399753 / 40000000000000000) (kdot ((87 / 200))) := by
    constructor
    · apply bkdot_lower (q := (78434708416112299 / 125000000000000000)) (a := (560379025012691601 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (627477667328898391 / 1000000000000000000)) (a := (112075805001551633 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal17_hz48 : B (7569 / 40000) (7569 / 40000) (((87 / 200) : ℝ)^2) := bsq (bpoint ((87 / 200) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal17_hz49 : B (32431 / 40000) (32431 / 40000) ((1 : ℝ) - (((87 / 200) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal17_hz48 (by norm_num) (by norm_num)

theorem sGlobal17_hz50 : B (900430452616969191 / 1000000000000000000) (112553806577121149 / 125000000000000000) (√((1 : ℝ) - (((87 / 200) : ℝ)^2))) := bsqrt sGlobal17_hz49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal17_hz51 : B (143307957444463291 / 500000000000000000) (286615914888926583 / 1000000000000000000) ((√((1 : ℝ) - (((87 / 200) : ℝ)^2))) / Real.pi) := bdiv sGlobal17_hz50 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal17_hz52 : B (139907230102865549 / 500000000000000000) (139907230103548657 / 500000000000000000) (((87 / 200) : ℝ) * (kdot ((87 / 200)))) := bmul (bpoint ((87 / 200) : ℝ)) sGlobal17_hz47 (by norm_num) (by norm_num)

theorem sGlobal17_hz53 : B (7080379688683221 / 12500000000000000) (566430375096023897 / 1000000000000000000) (((√((1 : ℝ) - (((87 / 200) : ℝ)^2))) / Real.pi) + (((87 / 200) : ℝ) * (kdot ((87 / 200))))) := badd sGlobal17_hz51 sGlobal17_hz52 (by norm_num) (by norm_num)

theorem sGlobal17_hz54 : B (7080379688683221 / 12500000000000000) (566430375096023897 / 1000000000000000000) (kappa ((87 / 200))) := by rw [kappa_eq]; exact sGlobal17_hz53

theorem sGlobal17_hz55 {c : ℝ} (hc : B (43 / 100) (87 / 200) c) : B (140804632964088217 / 250000000000000000) (566430375096023897 / 1000000000000000000) (kappa c) := bkappa (sGlobal17_hz38 hc) (by norm_num) (by norm_num) sGlobal17_hz46.1 sGlobal17_hz54.2

theorem sGlobal17_hz56 : B 24450 24450 ((2 : ℝ) * (12225 : ℝ)) := bmul (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal17_hz57 {c : ℝ} (hc : B (43 / 100) (87 / 200) c) : B (433569624903976103 / 1000000000000000000) (109195367035911783 / 250000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (sGlobal17_hz55 hc) (by norm_num) (by norm_num)

theorem sGlobal17_hz58 {c : ℝ} (hc : B (43 / 100) (87 / 200) c) : B (212015546578044314367 / 20000000000000000) (53396534480560861887 / 5000000000000000) (((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) := bmul sGlobal17_hz56 (sGlobal17_hz57 hc) (by norm_num) (by norm_num)

theorem sGlobal17_hz59 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (4 : ℝ)) sGlobal17_hz10 (by norm_num) (by norm_num)

theorem sGlobal17_hz60 {c : ℝ} (hc : B (43 / 100) (87 / 200) c) : B (1060077667450548770199 / 100000000000000000) (2669826560428861090261 / 250000000000000000) ((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bsub (sGlobal17_hz58 hc) sGlobal17_hz59 (by norm_num) (by norm_num)

theorem sGlobal17_hz61 {c : ℝ} (hc : B (43 / 100) (87 / 200) c) : B (51480036602807227661 / 500000000000000000) (103340728861932478443 / 1000000000000000000) (√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) := bsqrt (sGlobal17_hz60 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal17_hz62 : B (30670756373515103 / 125000000000000000) (122683025494060423 / 500000000000000000) ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal17_hz7 (by norm_num) (by norm_num)

theorem sGlobal17_hz63 {c : ℝ} (hc : B (43 / 100) (87 / 200) c) : B (25678676788656583619 / 250000000000000000) (103095362810944357619 / 1000000000000000000) ((√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) - ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))))) := bsub (sGlobal17_hz61 hc) sGlobal17_hz62 (by norm_num) (by norm_num)

theorem sGlobal17_hz64 {c : ℝ} (hc : B (43 / 100) (87 / 200) c) : B (25678676788656583619 / 250000000000000000) (103095362810944357619 / 1000000000000000000) (s3dm 12225 46 c) := by
    convert (sGlobal17_hz63 hc) using 1 <;>
      norm_num [s3dm, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal17_hz65 : B (6126072185528622723889 / 500000000000000000) (2450428874211449090087 / 200000000000000000) ((s3ap 12225 46)^2) := bsq sGlobal17_hz9 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal17_hz66 : B (6126072185528622723889 / 250000000000000000) (2450428874211449090087 / 100000000000000000) ((2 : ℝ) * ((s3ap 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal17_hz65 (by norm_num) (by norm_num)

theorem sGlobal17_hz67 {c : ℝ} (hc : B (43 / 100) (87 / 200) c) : B (10550311065860646304281 / 1000000000000000000) (1328581729140031109851 / 125000000000000000) ((s3dm 12225 46 c)^2) := bsq (sGlobal17_hz64 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal17_hz68 {c : ℝ} (hc : B (43 / 100) (87 / 200) c) : B (3468908727248560504187 / 250000000000000000) (13953977676253844596589 / 1000000000000000000) (((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) := bsub sGlobal17_hz66 (sGlobal17_hz67 hc) (by norm_num) (by norm_num)

theorem sGlobal17_hz69 : B (1524735695971823534271 / 125000000000000000) (609894278388729413841 / 50000000000000000) ((s3am 12225 46)^2) := bsq sGlobal17_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal17_hz70 : B (1524735695971823534271 / 62500000000000000) (609894278388729413841 / 25000000000000000) ((2 : ℝ) * ((s3am 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal17_hz69 (by norm_num) (by norm_num)

theorem sGlobal17_hz71 {c : ℝ} (hc : B (43 / 100) (87 / 200) c) : B (56877213808481999 / 100000000000000000) (114396692760576881 / 200000000000000000) ((((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) / ((2 : ℝ) * ((s3am 12225 46)^2))) := bdiv (sGlobal17_hz68 hc) sGlobal17_hz70 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal17_hz72 {c : ℝ} (hc : B (43 / 100) (87 / 200) c) : B (56877213808481999 / 100000000000000000) (114396692760576881 / 200000000000000000) (s3c1 12225 46 c) := by
    convert (sGlobal17_hz71 hc) using 1 <;>
      norm_num [s3c1] <;> ring

theorem sGlobal17_hz73 {c : ℝ} (hc : B (43 / 100) (87 / 200) c) : B (160371611308842497 / 250000000000000000) (25730065306399753 / 40000000000000000) (kdot c) := bkdot (sGlobal17_hz38 hc) sGlobal17_hz39.1 sGlobal17_hz47.2

theorem sGlobal17_hz74 : B (86572671887944311 / 125000000000000000) (346290687551777481 / 500000000000000000) (kdot ((56877213808481999 / 100000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (1048584583826113 / 2000000000000000)) (a := (96578409355134953 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (524292291913056499 / 1000000000000000000)) (a := (241446023387837011 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal17_hz75 : B (173456465072100929 / 250000000000000000) (173456465072101023 / 250000000000000000) (kdot ((114396692760576881 / 200000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (521802658485040659 / 1000000000000000000)) (a := (480937214018562931 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (260901329242520329 / 500000000000000000)) (a := (240468607009281171 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal17_hz76 {c : ℝ} (hc : B (43 / 100) (87 / 200) c) : B (86572671887944311 / 125000000000000000) (173456465072101023 / 250000000000000000) (kdot (s3c1 12225 46 c)) := bkdot (sGlobal17_hz72 hc) sGlobal17_hz74.1 sGlobal17_hz75.2

theorem sGlobal17_hz77 {c : ℝ} (hc : B (43 / 100) (87 / 200) c) : B (1849 / 10000) (7569 / 40000) (c^2) := bsq (sGlobal17_hz38 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal17_hz78 {c : ℝ} (hc : B (43 / 100) (87 / 200) c) : B (32431 / 40000) (8151 / 10000) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (sGlobal17_hz77 hc) (by norm_num) (by norm_num)

theorem sGlobal17_hz79 {c : ℝ} (hc : B (43 / 100) (87 / 200) c) : B (900430452616969191 / 1000000000000000000) (90282888744213319 / 100000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (sGlobal17_hz78 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal17_hz80 : B (39119999999999765769 / 1600000000000000) (3912000000000000489 / 160000000000000) ((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (149450625 : ℝ)) sGlobal17_hz10 (by norm_num) (by norm_num)

theorem sGlobal17_hz81 {c : ℝ} (hc : B (43 / 100) (87 / 200) c) : B (577613930230934817 / 1000000000000000000) (580746155859757971 / 1000000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (sGlobal17_hz79 hc) (sGlobal17_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal17_hz82 {c : ℝ} (hc : B (43 / 100) (87 / 200) c) : B (14122660594146271716219 / 1000000000000000000) (443726359711596380183 / 31250000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) := bmul sGlobal17_hz80 (sGlobal17_hz81 hc) (by norm_num) (by norm_num)

theorem sGlobal17_hz83 {c : ℝ} (hc : B (43 / 100) (87 / 200) c) : B (7061330297073135858109 / 1000000000000000000) (443726359711596380183 / 62500000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) / (2 : ℝ)) := bdiv (sGlobal17_hz82 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal17_hz84 {c : ℝ} (hc : B (43 / 100) (87 / 200) c) : B (7061330297073135858109 / 1000000000000000000) (443726359711596380183 / 62500000000000000) (s3Cpa 12225 c) := by
    convert (sGlobal17_hz83 hc) using 1 <;>
      norm_num [s3Cpa, mA] <;> ring

theorem sGlobal17_hz85 {c : ℝ} (hc : B (43 / 100) (87 / 200) c) : B (143307957444463291 / 500000000000000000) (11495174416205751 / 40000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (sGlobal17_hz79 hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal17_hz86 {c : ℝ} (hc : B (43 / 100) (87 / 200) c) : B (137919585725604547 / 500000000000000000) (139907230103548657 / 500000000000000000) (c * (kdot c)) := bmul (sGlobal17_hz38 hc) (sGlobal17_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal17_hz87 {c : ℝ} (hc : B (43 / 100) (87 / 200) c) : B (1700363670457317 / 250000000000000000) (11540188953934681 / 1000000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (sGlobal17_hz85 hc) (sGlobal17_hz86 hc) (by norm_num) (by norm_num)

theorem sGlobal17_hz88 {c : ℝ} (hc : B (43 / 100) (87 / 200) c) : B (33259113394144921381 / 200000000000000000) (7053940498092574643 / 25000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) := bmul sGlobal17_hz80 (sGlobal17_hz87 hc) (by norm_num) (by norm_num)

theorem sGlobal17_hz89 {c : ℝ} (hc : B (43 / 100) (87 / 200) c) : B (20786945871340575863 / 250000000000000000) (7053940498092574643 / 50000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) / (2 : ℝ)) := bdiv (sGlobal17_hz88 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal17_hz90 {c : ℝ} (hc : B (43 / 100) (87 / 200) c) : B (20786945871340575863 / 250000000000000000) (7053940498092574643 / 50000000000000000) (s3Cpp 12225 c) := by
    convert (sGlobal17_hz89 hc) using 1 <;>
      norm_num [s3Cpp, mA] <;> ring

theorem sGlobal17_hz91 {c : ℝ} (hc : B (43 / 100) (87 / 200) c) : B (717647540700687356651 / 100000000000000000) (3607383432659640247577 / 500000000000000000) ((s3Cpa 12225 c) + (s3r1 12225 46)) := badd (sGlobal17_hz84 hc) sGlobal17_hz33 (by norm_num) (by norm_num)

theorem sGlobal17_hz92 {c : ℝ} (hc : B (43 / 100) (87 / 200) c) : B (12995677314550713457 / 200000000000000000) (65325091192994966003 / 1000000000000000000) (((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) := bdiv (sGlobal17_hz91 hc) sGlobal17_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal17_hz93 {c : ℝ} (hc : B (43 / 100) (87 / 200) c) : B (65101069598247627697 / 1000000000000000000) (32723887109244513213 / 500000000000000000) ((((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) + (s3e0 12225 46)) := badd (sGlobal17_hz92 hc) sGlobal17_hz16 (by norm_num) (by norm_num)

theorem sGlobal17_hz94 {c : ℝ} (hc : B (43 / 100) (87 / 200) c) : B (65101069598247627697 / 1000000000000000000) (32723887109244513213 / 500000000000000000) (s3Lam 12225 46 c) := by
    convert (sGlobal17_hz93 hc) using 1 <;>
      norm_num [s3Lam] <;> ring

theorem sGlobal17_hz95 {c : ℝ} (hc : B (43 / 100) (87 / 200) c) : B (39977797526963527263 / 250000000000000000) (108921108292171883839 / 500000000000000000) ((s3Cpp 12225 c) + (s3rpp 12225 46)) := badd (sGlobal17_hz90 hc) sGlobal17_hz37 (by norm_num) (by norm_num)

theorem sGlobal17_hz96 {c : ℝ} (hc : B (43 / 100) (87 / 200) c) : B (39977797526963527263 / 500000000000000000) (151144563328765163819 / 1000000000000000000) (if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) := bweaken (bfirst (sGlobal17_hz95 hc) (sGlobal17_hz76 hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem sGlobal17_hz97 {c : ℝ} (hc : B (43 / 100) (87 / 200) c) : B (4238149262835881537477 / 1000000000000000000) (1070852787538579223439 / 250000000000000000) ((s3Lam 12225 46 c)^2) := bsq (sGlobal17_hz94 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal17_hz98 {c : ℝ} (hc : B (43 / 100) (87 / 200) c) : B (161750872530788769 / 500000000000000000) (13086603314557823 / 40000000000000000) ((s3c1 12225 46 c)^2) := bsq (sGlobal17_hz72 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal17_hz99 {c : ℝ} (hc : B (43 / 100) (87 / 200) c) : B (26913396685442177 / 40000000000000000) (338249127469211231 / 500000000000000000) ((1 : ℝ) - ((s3c1 12225 46 c)^2)) := bsub (bpoint (1 : ℝ)) (sGlobal17_hz98 hc) (by norm_num) (by norm_num)

theorem sGlobal17_hz100 {c : ℝ} (hc : B (43 / 100) (87 / 200) c) : B (820265150506867763 / 1000000000000000000) (822495139765836223 / 1000000000000000000) (√((1 : ℝ) - ((s3c1 12225 46 c)^2))) := bsqrt (sGlobal17_hz99 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal17_hz101 {c : ℝ} (hc : B (43 / 100) (87 / 200) c) : B (2576938970828101829 / 1000000000000000000) (2583944688701661291 / 1000000000000000000) (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))) := bmul pi_mem (sGlobal17_hz100 hc) (by norm_num) (by norm_num)

theorem sGlobal17_hz102 {c : ℝ} (hc : B (43 / 100) (87 / 200) c) : B (205023219022801441499 / 125000000000000000) (332441800030509731517 / 200000000000000000) (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2))))) := bdiv (sGlobal17_hz97 hc) (sGlobal17_hz101 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal17_hz103 {c : ℝ} (hc : B (43 / 100) (87 / 200) c) : B (860070673618169293259 / 500000000000000000) (453338390870328455351 / 250000000000000000) ((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) := badd (sGlobal17_hz96 hc) (sGlobal17_hz102 hc) (by norm_num) (by norm_num)

theorem sGlobal17_hz104 : B (3762781186094069 / 250000000000000000) (376278118609407 / 25000000000000000) ((s3e0 12225 46)^2) := bsq sGlobal17_hz16 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal17_hz105 {c : ℝ} (hc : B (43 / 100) (87 / 200) c) : B (860078199180541481397 / 500000000000000000) (453342153651514549421 / 250000000000000000) (((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) := badd (sGlobal17_hz103 hc) sGlobal17_hz104 (by norm_num) (by norm_num)

theorem sGlobal17_hz106 {c : ℝ} (hc : B (43 / 100) (87 / 200) c) : B (70346138872493209317 / 40000000000000000) (18518656880601824677 / 10000000000000000) ((((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) + (s3rs 12225 46 maskSlack)) := badd (sGlobal17_hz105 hc) sGlobal17_hz29 (by norm_num) (by norm_num)

theorem sGlobal17_hz107 {c : ℝ} (hc : B (43 / 100) (87 / 200) c) : B (70346138872493209317 / 40000000000000000) (18518656880601824677 / 10000000000000000) (s3U 12225 46 maskSlack c) := by
    convert (sGlobal17_hz106 hc) using 1 <;>
      norm_num [s3U] <;> ring

theorem sGlobal17_hz108 {c : ℝ} (hc : B (43 / 100) (87 / 200) c) : B (3192188431435014317 / 500000000000000000) (3215770166967984363 / 50000000000000000) ((s3Cpp 12225 c) - (s3rpp 12225 46)) := bsub (sGlobal17_hz90 hc) sGlobal17_hz37 (by norm_num) (by norm_num)

theorem sGlobal17_hz109 {c : ℝ} (hc : B (43 / 100) (87 / 200) c) : B 0 0 (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ)) := bweaken (bmin (sGlobal17_hz108 hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem sGlobal17_hz110 {c : ℝ} (hc : B (43 / 100) (87 / 200) c) : B 0 0 ((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) := bmul (sGlobal17_hz76 hc) (sGlobal17_hz109 hc) (by norm_num) (by norm_num)

theorem sGlobal17_hz111 {c : ℝ} (hc : B (43 / 100) (87 / 200) c) : B (-376278118609407 / 25000000000000000) (-3762781186094069 / 250000000000000000) (((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) := bsub (sGlobal17_hz110 hc) sGlobal17_hz104 (by norm_num) (by norm_num)

theorem sGlobal17_hz112 {c : ℝ} (hc : B (43 / 100) (87 / 200) c) : B (-4814015572358580787 / 125000000000000000) (-38512124575991646407 / 1000000000000000000) ((((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) - (s3rs 12225 46 maskSlack)) := bsub (sGlobal17_hz111 hc) sGlobal17_hz29 (by norm_num) (by norm_num)

theorem sGlobal17_hz113 {c : ℝ} (hc : B (43 / 100) (87 / 200) c) : B (-4814015572358580787 / 125000000000000000) (-38512124575991646407 / 1000000000000000000) (s3L 12225 46 maskSlack c) := by
    convert (sGlobal17_hz112 hc) using 1 <;>
      norm_num [s3L] <;> ring

theorem sGlobal17_hz114 {c : ℝ} (hc : B (43 / 100) (87 / 200) c) : B 0 (18518656880601824677 / 10000000000000000) |(s3U 12225 46 maskSlack c)| := bweaken (babs (sGlobal17_hz107 hc)) (by norm_num) (by norm_num)

theorem sGlobal17_hz115 {c : ℝ} (hc : B (43 / 100) (87 / 200) c) : B 0 (4814015572358580787 / 125000000000000000) |(s3L 12225 46 maskSlack c)| := bweaken (babs (sGlobal17_hz113 hc)) (by norm_num) (by norm_num)

theorem sGlobal17_hz116 {c : ℝ} (hc : B (43 / 100) (87 / 200) c) : B 0 (18518656880601824677 / 10000000000000000) (max |(s3U 12225 46 maskSlack c)| |(s3L 12225 46 maskSlack c)|) := bweaken (bmax (sGlobal17_hz114 hc) (sGlobal17_hz115 hc)) (by norm_num) (by norm_num)

theorem sGlobal17_hz117 {c : ℝ} (hc : B (43 / 100) (87 / 200) c) : B 0 (18518656880601824677 / 10000000000000000) (s3nks 12225 46 maskSlack c) := by
    convert (sGlobal17_hz116 hc) using 1 <;>
      norm_num [s3nks] <;> ring

theorem sGlobal17 {c : ℝ} (hc : B (43 / 100) (87 / 200) c) :
    0 < s3am 12225 46 ∧ 0 ≤ s3dm 12225 46 c ∧
    s3dm 12225 46 c ^ 2 ≤ 2 * s3ap 12225 46 ^ 2 ∧ s3c1 12225 46 c < 1 ∧
    0 ≤ s3Cpa 12225 c - s3r1 12225 46 ∧
    s3e0 12225 46 ≤ (s3Cpa 12225 c - s3r1 12225 46) / s3ap 12225 46 ∧
    s3nks 12225 46 maskSlack c ≤ 12225 * (75741 / 500000) := by

  refine ⟨lt_of_lt_of_le (by norm_num) sGlobal17_hz14.1,
    le_trans (by norm_num) (sGlobal17_hz64 hc).1, ?_,
    lt_of_le_of_lt (sGlobal17_hz72 hc).2 (by norm_num), ?_, ?_,
    le_trans (sGlobal17_hz117 hc).2 (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (sGlobal17_hz64 hc).1) (sGlobal17_hz64 hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) sGlobal17_hz9.1 2
    nlinarith only [h1, h2]
  · linarith only [(sGlobal17_hz84 hc).1, sGlobal17_hz33.2]
  · have hap : 0 < s3ap 12225 46 := lt_of_lt_of_le (by norm_num) sGlobal17_hz9.1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul sGlobal17_hz16.2 sGlobal17_hz9.2 (le_trans (by norm_num) sGlobal17_hz9.1) (by norm_num)
    linarith only [h, (sGlobal17_hz84 hc).1, sGlobal17_hz33.2]

end BstLean.Part255
