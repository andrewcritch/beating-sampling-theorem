import BstLean.Part255SGlobal8
import BstLean.Part255Numeric10
namespace BstLean.Part255
open Real BstLean.Part130 BstLean.Part182 BstLean.Part197 BstLean.Part246
theorem sGlobal12_hz0 : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal12_hz1 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) ((√(23 : ℝ)) / (12225 : ℝ)) := bdiv sGlobal12_hz0 (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal12_hz2 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) maskSlack := by
    convert sGlobal12_hz1 using 1 <;>
      norm_num [maskSlack] <;> ring

theorem sGlobal12_hz3 : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal12_hz4 : B (6395294793910793 / 500000000000000000) (12790589587821587 / 1000000000000000000) (√((2 / 12225) : ℝ)) := bsqrt (bpoint ((2 / 12225) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal12_hz5 : B (7230130686979 / 62500000000000000) (23136418198333 / 200000000000000000) (√((2 / 149450625) : ℝ)) := bsqrt (bpoint ((2 / 149450625) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal12_hz6 : B (2211334438749598093 / 20000000000000000) (110566721937479904651 / 1000000000000000000) (√(12225 : ℝ)) := bsqrt (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal12_hz7 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))) := bmul sGlobal12_hz3 sGlobal12_hz4 (by norm_num) (by norm_num)

theorem sGlobal12_hz8 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) ((√(12225 : ℝ)) + ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := badd sGlobal12_hz6 sGlobal12_hz7 (by norm_num) (by norm_num)

theorem sGlobal12_hz9 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) (s3ap 12225 46) := by
    convert sGlobal12_hz8 using 1 <;>
      norm_num [s3ap, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal12_hz10 : B (163599182004089 / 1000000000000000000) (16359918200409 / 100000000000000000) ((2 : ℝ) / (12225 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal12_hz11 : B (1222499983640081799591 / 100000000000000000) (12224999836400817995911 / 1000000000000000000) ((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ))) := bsub (bpoint (12225 : ℝ)) sGlobal12_hz10 (by norm_num) (by norm_num)

theorem sGlobal12_hz12 : B (110566721197658827907 / 1000000000000000000) (27641680299414706977 / 250000000000000000) (√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) := bsqrt sGlobal12_hz11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal12_hz13 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) ((√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) - ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bsub sGlobal12_hz12 sGlobal12_hz7 (by norm_num) (by norm_num)

theorem sGlobal12_hz14 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) (s3am 12225 46) := by
    convert sGlobal12_hz13 using 1 <;>
      norm_num [s3am, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal12_hz15 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√((2 / 12225) : ℝ)) * (√(92 : ℝ))) := bmul sGlobal12_hz4 sGlobal12_hz3 (by norm_num) (by norm_num)

theorem sGlobal12_hz16 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) (s3e0 12225 46) := by
    convert sGlobal12_hz15 using 1 <;>
      norm_num [s3e0, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal12_hz17 : B (250196148528560847 / 500000000000000000) (100078459411424339 / 200000000000000000) (((1 / 2) : ℝ) + maskSlack) := badd (bpoint ((1 / 2) : ℝ)) sGlobal12_hz2 (by norm_num) (by norm_num)

theorem sGlobal12_hz18 : B (59827153232297998295487 / 800000000000000) (23930861292919199366019 / 320000000000000) ((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack)) := bmul (bpoint (149450625 : ℝ)) sGlobal12_hz17 (by norm_num) (by norm_num)

theorem sGlobal12_hz19 : B (1729554180017180009583 / 200000000000000000) (8647770900085900056557 / 1000000000000000000) (√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) := bsqrt sGlobal12_hz18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal12_hz20 : B (4328681281566262743499 / 500000000000000000) (8657362563132525495641 / 1000000000000000000) ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))) := badd sGlobal12_hz19 sGlobal12_hz3 (by norm_num) (by norm_num)

theorem sGlobal12_hz21 : B (110732771457999278473 / 1000000000000000000) (55366385728999643621 / 500000000000000000) ((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ)))) := bmul sGlobal12_hz4 sGlobal12_hz20 (by norm_num) (by norm_num)

theorem sGlobal12_hz22 : B (209099159 / 15625000000000000) (13382346177 / 1000000000000000000) ((2 : ℝ) / (149450625 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (149450625 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal12_hz23 : B (2452349334953899930479 / 200000000000000000) (12261746674769501594427 / 1000000000000000000) (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2) := bsq sGlobal12_hz21 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal12_hz24 : B (82045469362091 / 500000000000000000) (32818187747289 / 200000000000000000) (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2)) := bmul sGlobal12_hz22 sGlobal12_hz23 (by norm_num) (by norm_num)

theorem sGlobal12_hz25 : B (82045469362091 / 250000000000000000) (32818187747289 / 100000000000000000) ((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) := bmul (bpoint (2 : ℝ)) sGlobal12_hz24 (by norm_num) (by norm_num)

theorem sGlobal12_hz26 : B (117258080744995992792057 / 1000000000000000000) (58629040372497996396029 / 500000000000000000) (√(13749457500 : ℝ)) := bsqrt (bpoint (13749457500 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal12_hz27 : B (117304080744995992792057 / 1000000000000000000) (58652040372497996396029 / 500000000000000000) ((√(13749457500 : ℝ)) + (46 : ℝ)) := badd sGlobal12_hz26 (bpoint (46 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal12_hz28 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal12_hz25 sGlobal12_hz27 (by norm_num) (by norm_num)

theorem sGlobal12_hz29 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (s3rs 12225 46 maskSlack) := by
    convert sGlobal12_hz28 using 1 <;>
      norm_num [s3rs, s3pp, s3K, mA, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal12_hz30 : B (490797546012267 / 1000000000000000000) (49079754601227 / 100000000000000000) ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (3 : ℝ)) sGlobal12_hz10 (by norm_num) (by norm_num)

theorem sGlobal12_hz31 : B (490797546012267 / 500000000000000000) (49079754601227 / 50000000000000000) ((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal12_hz30 (by norm_num) (by norm_num)

theorem sGlobal12_hz32 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal12_hz31 sGlobal12_hz27 (by norm_num) (by norm_num)

theorem sGlobal12_hz33 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (s3r1 12225 46) := by
    convert sGlobal12_hz32 using 1 <;>
      norm_num [s3r1, mA] <;> ring

theorem sGlobal12_hz34 : B (163599182004089 / 500000000000000000) (16359918200409 / 50000000000000000) ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (2 : ℝ)) sGlobal12_hz10 (by norm_num) (by norm_num)

theorem sGlobal12_hz35 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal12_hz34 (by norm_num) (by norm_num)

theorem sGlobal12_hz36 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal12_hz35 sGlobal12_hz27 (by norm_num) (by norm_num)

theorem sGlobal12_hz37 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (s3rpp 12225 46) := by
    convert sGlobal12_hz36 using 1 <;>
      norm_num [s3rpp, mA] <;> ring

theorem sGlobal12_hz38 {c : ℝ} (hc : B (81 / 200) (41 / 100) c) : B (81 / 200) (41 / 100) c := hc

theorem sGlobal12_hz39 : B (158182121028224703 / 250000000000000000) (316364242065809491 / 500000000000000000) (kdot ((81 / 200))) := by
    constructor
    · apply bkdot_lower (q := (650759206222997483 / 1000000000000000000)) (a := (576908748091852063 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (325379603111498741 / 500000000000000000)) (a := (576908748062446489 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal12_hz40 : B (6561 / 40000) (6561 / 40000) (((81 / 200) : ℝ)^2) := bsq (bpoint ((81 / 200) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal12_hz41 : B (33439 / 40000) (33439 / 40000) ((1 : ℝ) - (((81 / 200) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal12_hz40 (by norm_num) (by norm_num)

theorem sGlobal12_hz42 : B (457158342371655731 / 500000000000000000) (914316684743311463 / 1000000000000000000) (√((1 : ℝ) - (((81 / 200) : ℝ)^2))) := bsqrt sGlobal12_hz41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal12_hz43 : B (9094876245518259 / 31250000000000000) (291036039856584289 / 1000000000000000000) ((√((1 : ℝ) - (((81 / 200) : ℝ)^2))) / Real.pi) := bdiv sGlobal12_hz42 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal12_hz44 : B (128127518032862009 / 500000000000000000) (32031879509163211 / 125000000000000000) (((81 / 200) : ℝ) * (kdot ((81 / 200)))) := bmul (bpoint ((81 / 200) : ℝ)) sGlobal12_hz39 (by norm_num) (by norm_num)

theorem sGlobal12_hz45 : B (273645537961154153 / 500000000000000000) (547291075929889977 / 1000000000000000000) (((√((1 : ℝ) - (((81 / 200) : ℝ)^2))) / Real.pi) + (((81 / 200) : ℝ) * (kdot ((81 / 200))))) := badd sGlobal12_hz43 sGlobal12_hz44 (by norm_num) (by norm_num)

theorem sGlobal12_hz46 : B (273645537961154153 / 500000000000000000) (547291075929889977 / 1000000000000000000) (kappa ((81 / 200))) := by rw [kappa_eq]; exact sGlobal12_hz45

theorem sGlobal12_hz47 : B (12689426089010923 / 20000000000000000) (317235652232250419 / 500000000000000000) (kdot ((41 / 100))) := by
    constructor
    · apply bkdot_lower (q := (646869164755947181 / 1000000000000000000)) (a := (287085566153606091 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (32343458237797359 / 50000000000000000)) (a := (143542783071323053 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal12_hz48 : B (1681 / 10000) (1681 / 10000) (((41 / 100) : ℝ)^2) := bsq (bpoint ((41 / 100) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal12_hz49 : B (8319 / 10000) (8319 / 10000) ((1 : ℝ) - (((41 / 100) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal12_hz48 (by norm_num) (by norm_num)

theorem sGlobal12_hz50 : B (228021380576471381 / 250000000000000000) (36483420892235421 / 40000000000000000) (√((1 : ℝ) - (((41 / 100) : ℝ)^2))) := bsqrt sGlobal12_hz49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal12_hz51 : B (36290729849383711 / 125000000000000000) (29032583879506969 / 100000000000000000) ((√((1 : ℝ) - (((41 / 100) : ℝ)^2))) / Real.pi) := bdiv sGlobal12_hz50 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal12_hz52 : B (260133234824723921 / 1000000000000000000) (8129163588451417 / 31250000000000000) (((41 / 100) : ℝ) * (kdot ((41 / 100)))) := bmul (bpoint ((41 / 100) : ℝ)) sGlobal12_hz47 (by norm_num) (by norm_num)

theorem sGlobal12_hz53 : B (550459073619793609 / 1000000000000000000) (275229536812757517 / 500000000000000000) (((√((1 : ℝ) - (((41 / 100) : ℝ)^2))) / Real.pi) + (((41 / 100) : ℝ) * (kdot ((41 / 100))))) := badd sGlobal12_hz51 sGlobal12_hz52 (by norm_num) (by norm_num)

theorem sGlobal12_hz54 : B (550459073619793609 / 1000000000000000000) (275229536812757517 / 500000000000000000) (kappa ((41 / 100))) := by rw [kappa_eq]; exact sGlobal12_hz53

theorem sGlobal12_hz55 {c : ℝ} (hc : B (81 / 200) (41 / 100) c) : B (273645537961154153 / 500000000000000000) (275229536812757517 / 500000000000000000) (kappa c) := bkappa (sGlobal12_hz38 hc) (by norm_num) (by norm_num) sGlobal12_hz46.1 sGlobal12_hz54.2

theorem sGlobal12_hz56 : B 24450 24450 ((2 : ℝ) * (12225 : ℝ)) := bmul (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal12_hz57 {c : ℝ} (hc : B (81 / 200) (41 / 100) c) : B (224770463187242483 / 500000000000000000) (226354462038845847 / 500000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (sGlobal12_hz55 hc) (by norm_num) (by norm_num)

theorem sGlobal12_hz58 {c : ℝ} (hc : B (81 / 200) (41 / 100) c) : B (109912756498561574187 / 10000000000000000) (110687331936995619183 / 10000000000000000) (((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) := bmul sGlobal12_hz56 (sGlobal12_hz57 hc) (by norm_num) (by norm_num)

theorem sGlobal12_hz59 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (4 : ℝ)) sGlobal12_hz10 (by norm_num) (by norm_num)

theorem sGlobal12_hz60 {c : ℝ} (hc : B (81 / 200) (41 / 100) c) : B (549563749772971470117 / 50000000000000000) (1383591567412854237743 / 125000000000000000) ((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bsub (sGlobal12_hz58 hc) sGlobal12_hz59 (by norm_num) (by norm_num)

theorem sGlobal12_hz61 {c : ℝ} (hc : B (81 / 200) (41 / 100) c) : B (104839281738570821831 / 1000000000000000000) (105208044080777558679 / 1000000000000000000) (√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) := bsqrt (sGlobal12_hz60 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal12_hz62 : B (30670756373515103 / 125000000000000000) (122683025494060423 / 500000000000000000) ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal12_hz7 (by norm_num) (by norm_num)

theorem sGlobal12_hz63 {c : ℝ} (hc : B (81 / 200) (41 / 100) c) : B (20918783137516540197 / 200000000000000000) (20992535605957887571 / 200000000000000000) ((√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) - ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))))) := bsub (sGlobal12_hz61 hc) sGlobal12_hz62 (by norm_num) (by norm_num)

theorem sGlobal12_hz64 {c : ℝ} (hc : B (81 / 200) (41 / 100) c) : B (20918783137516540197 / 200000000000000000) (20992535605957887571 / 200000000000000000) (s3dm 12225 46 c) := by
    convert (sGlobal12_hz63 hc) using 1 <;>
      norm_num [s3dm, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal12_hz65 : B (6126072185528622723889 / 500000000000000000) (2450428874211449090087 / 200000000000000000) ((s3ap 12225 46)^2) := bsq sGlobal12_hz9 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal12_hz66 : B (6126072185528622723889 / 250000000000000000) (2450428874211449090087 / 100000000000000000) ((2 : ℝ) * ((s3ap 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal12_hz65 (by norm_num) (by norm_num)

theorem sGlobal12_hz67 {c : ℝ} (hc : B (81 / 200) (41 / 100) c) : B (136748589985764482967 / 12500000000000000) (11017163779185242347639 / 1000000000000000000) ((s3dm 12225 46 c)^2) := bsq (sGlobal12_hz64 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal12_hz68 {c : ℝ} (hc : B (81 / 200) (41 / 100) c) : B (13487124962929248547917 / 1000000000000000000) (1356440154325333226351 / 100000000000000000) (((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) := bsub sGlobal12_hz66 (sGlobal12_hz67 hc) (by norm_num) (by norm_num)

theorem sGlobal12_hz69 : B (1524735695971823534271 / 125000000000000000) (609894278388729413841 / 50000000000000000) ((s3am 12225 46)^2) := bsq sGlobal12_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal12_hz70 : B (1524735695971823534271 / 62500000000000000) (609894278388729413841 / 25000000000000000) ((2 : ℝ) * ((s3am 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal12_hz69 (by norm_num) (by norm_num)

theorem sGlobal12_hz71 {c : ℝ} (hc : B (81 / 200) (41 / 100) c) : B (276423419616279287 / 500000000000000000) (13900361529756561 / 25000000000000000) ((((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) / ((2 : ℝ) * ((s3am 12225 46)^2))) := bdiv (sGlobal12_hz68 hc) sGlobal12_hz70 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal12_hz72 {c : ℝ} (hc : B (81 / 200) (41 / 100) c) : B (276423419616279287 / 500000000000000000) (13900361529756561 / 25000000000000000) (s3c1 12225 46 c) := by
    convert (sGlobal12_hz71 hc) using 1 <;>
      norm_num [s3c1] <;> ring

theorem sGlobal12_hz73 {c : ℝ} (hc : B (81 / 200) (41 / 100) c) : B (158182121028224703 / 250000000000000000) (317235652232250419 / 500000000000000000) (kdot c) := bkdot (sGlobal12_hz38 hc) sGlobal12_hz39.1 sGlobal12_hz47.2

theorem sGlobal12_hz74 : B (686458545017806581 / 1000000000000000000) (686458545017808057 / 1000000000000000000) (kdot ((276423419616279287 / 500000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (13415406907773729 / 25000000000000000)) (a := (492509765783956859 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (536616276310949159 / 1000000000000000000)) (a := (492509765783954543 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal12_hz75 : B (343835046688097469 / 500000000000000000) (343835046688098059 / 500000000000000000) (kdot ((13900361529756561 / 25000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (267083834227906611 / 500000000000000000)) (a := (245303335036433021 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (534167668455813221 / 1000000000000000000)) (a := (49060667007286419 / 100000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal12_hz76 {c : ℝ} (hc : B (81 / 200) (41 / 100) c) : B (686458545017806581 / 1000000000000000000) (343835046688098059 / 500000000000000000) (kdot (s3c1 12225 46 c)) := bkdot (sGlobal12_hz72 hc) sGlobal12_hz74.1 sGlobal12_hz75.2

theorem sGlobal12_hz77 {c : ℝ} (hc : B (81 / 200) (41 / 100) c) : B (6561 / 40000) (1681 / 10000) (c^2) := bsq (sGlobal12_hz38 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal12_hz78 {c : ℝ} (hc : B (81 / 200) (41 / 100) c) : B (8319 / 10000) (33439 / 40000) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (sGlobal12_hz77 hc) (by norm_num) (by norm_num)

theorem sGlobal12_hz79 {c : ℝ} (hc : B (81 / 200) (41 / 100) c) : B (228021380576471381 / 250000000000000000) (914316684743311463 / 1000000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (sGlobal12_hz78 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal12_hz80 : B (39119999999999765769 / 1600000000000000) (3912000000000000489 / 160000000000000) ((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (149450625 : ℝ)) sGlobal12_hz10 (by norm_num) (by norm_num)

theorem sGlobal12_hz81 {c : ℝ} (hc : B (81 / 200) (41 / 100) c) : B (577102489909924503 / 1000000000000000000) (145026924915686649 / 250000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (sGlobal12_hz79 hc) (sGlobal12_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal12_hz82 {c : ℝ} (hc : B (81 / 200) (41 / 100) c) : B (14110155878297569613791 / 1000000000000000000) (2836726651350831209031 / 200000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) := bmul sGlobal12_hz80 (sGlobal12_hz81 hc) (by norm_num) (by norm_num)

theorem sGlobal12_hz83 {c : ℝ} (hc : B (81 / 200) (41 / 100) c) : B (1411015587829756961379 / 200000000000000000) (3545908314188539011289 / 500000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) / (2 : ℝ)) := bdiv (sGlobal12_hz82 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal12_hz84 {c : ℝ} (hc : B (81 / 200) (41 / 100) c) : B (1411015587829756961379 / 200000000000000000) (3545908314188539011289 / 500000000000000000) (s3Cpa 12225 c) := by
    convert (sGlobal12_hz83 hc) using 1 <;>
      norm_num [s3Cpa, mA] <;> ring

theorem sGlobal12_hz85 {c : ℝ} (hc : B (81 / 200) (41 / 100) c) : B (36290729849383711 / 125000000000000000) (291036039856584289 / 1000000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (sGlobal12_hz79 hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal12_hz86 {c : ℝ} (hc : B (81 / 200) (41 / 100) c) : B (128127518032862009 / 500000000000000000) (8129163588451417 / 31250000000000000) (c * (kdot c)) := bmul (sGlobal12_hz38 hc) (sGlobal12_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal12_hz87 {c : ℝ} (hc : B (81 / 200) (41 / 100) c) : B (3774075495578043 / 125000000000000000) (34781003790860271 / 1000000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (sGlobal12_hz85 hc) (sGlobal12_hz86 hc) (by norm_num) (by norm_num)

theorem sGlobal12_hz88 {c : ℝ} (hc : B (81 / 200) (41 / 100) c) : B (184552291733765197693 / 250000000000000000) (3401582170746134929 / 4000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) := bmul sGlobal12_hz80 (sGlobal12_hz87 hc) (by norm_num) (by norm_num)

theorem sGlobal12_hz89 {c : ℝ} (hc : B (81 / 200) (41 / 100) c) : B (184552291733765197693 / 500000000000000000) (3401582170746134929 / 8000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) / (2 : ℝ)) := bdiv (sGlobal12_hz88 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal12_hz90 {c : ℝ} (hc : B (81 / 200) (41 / 100) c) : B (184552291733765197693 / 500000000000000000) (3401582170746134929 / 8000000000000000) (s3Cpp 12225 c) := by
    convert (sGlobal12_hz89 hc) using 1 <;>
      norm_num [s3Cpp, mA] <;> ring

theorem sGlobal12_hz91 {c : ℝ} (hc : B (81 / 200) (41 / 100) c) : B (224069470283828828603 / 31250000000000000) (1801740434577704108701 / 250000000000000000) ((s3Cpa 12225 c) + (s3r1 12225 46)) := badd (sGlobal12_hz84 hc) sGlobal12_hz33 (by norm_num) (by norm_num)

theorem sGlobal12_hz92 {c : ℝ} (hc : B (81 / 200) (41 / 100) c) : B (32460887738934717937 / 500000000000000000) (65254420768971741651 / 1000000000000000000) (((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) := bdiv (sGlobal12_hz91 hc) sGlobal12_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal12_hz93 {c : ℝ} (hc : B (81 / 200) (41 / 100) c) : B (32522229251681748143 / 500000000000000000) (32688551897232901037 / 500000000000000000) ((((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) + (s3e0 12225 46)) := badd (sGlobal12_hz92 hc) sGlobal12_hz16 (by norm_num) (by norm_num)

theorem sGlobal12_hz94 {c : ℝ} (hc : B (81 / 200) (41 / 100) c) : B (32522229251681748143 / 500000000000000000) (32688551897232901037 / 500000000000000000) (s3Lam 12225 46 c) := by
    convert (sGlobal12_hz93 hc) using 1 <;>
      norm_num [s3Lam] <;> ring

theorem sGlobal12_hz95 {c : ℝ} (hc : B (81 / 200) (41 / 100) c) : B (222933995045011100493 / 500000000000000000) (501961177965759140943 / 1000000000000000000) ((s3Cpp 12225 c) + (s3rpp 12225 46)) := badd (sGlobal12_hz90 hc) sGlobal12_hz37 (by norm_num) (by norm_num)

theorem sGlobal12_hz96 {c : ℝ} (hc : B (81 / 200) (41 / 100) c) : B (222933995045011100493 / 1000000000000000000) (172591845061469492903 / 500000000000000000) (if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) := bweaken (bfirst (sGlobal12_hz95 hc) (sGlobal12_hz76 hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem sGlobal12_hz97 {c : ℝ} (hc : B (81 / 200) (41 / 100) c) : B (423078158199577583919 / 100000000000000000) (854833140110470955103 / 200000000000000000) ((s3Lam 12225 46 c)^2) := bsq (sGlobal12_hz94 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal12_hz98 {c : ℝ} (hc : B (81 / 200) (41 / 100) c) : B (152819813824715233 / 500000000000000000) (154576040526348929 / 500000000000000000) ((s3c1 12225 46 c)^2) := bsq (sGlobal12_hz72 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal12_hz99 {c : ℝ} (hc : B (81 / 200) (41 / 100) c) : B (345423959473651071 / 500000000000000000) (347180186175284767 / 500000000000000000) ((1 : ℝ) - ((s3c1 12225 46 c)^2)) := bsub (bpoint (1 : ℝ)) (sGlobal12_hz98 hc) (by norm_num) (by norm_num)

theorem sGlobal12_hz100 {c : ℝ} (hc : B (81 / 200) (41 / 100) c) : B (166234523363506191 / 200000000000000000) (833282888550202701 / 1000000000000000000) (√((1 : ℝ) - ((s3c1 12225 46 c)^2))) := bsqrt (sGlobal12_hz99 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal12_hz101 {c : ℝ} (hc : B (81 / 200) (41 / 100) c) : B (2611205786858959479 / 1000000000000000000) (2617835401031399241 / 1000000000000000000) (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))) := bmul pi_mem (sGlobal12_hz100 hc) (by norm_num) (by norm_num)

theorem sGlobal12_hz102 {c : ℝ} (hc : B (81 / 200) (41 / 100) c) : B (1616137355438349178653 / 1000000000000000000) (1636855173216272319003 / 1000000000000000000) (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2))))) := bdiv (sGlobal12_hz97 hc) (sGlobal12_hz101 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal12_hz103 {c : ℝ} (hc : B (81 / 200) (41 / 100) c) : B (919535675241680139573 / 500000000000000000) (1982038863339211304809 / 1000000000000000000) ((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) := badd (sGlobal12_hz96 hc) (sGlobal12_hz102 hc) (by norm_num) (by norm_num)

theorem sGlobal12_hz104 : B (3762781186094069 / 250000000000000000) (376278118609407 / 25000000000000000) ((s3e0 12225 46)^2) := bsq sGlobal12_hz16 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal12_hz105 {c : ℝ} (hc : B (81 / 200) (41 / 100) c) : B (919543200804052327711 / 500000000000000000) (1982053914463955681089 / 1000000000000000000) (((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) := badd (sGlobal12_hz103 hc) sGlobal12_hz104 (by norm_num) (by norm_num)

theorem sGlobal12_hz106 {c : ℝ} (hc : B (81 / 200) (41 / 100) c) : B (1877583475059351925553 / 1000000000000000000) (404110197583615990221 / 200000000000000000) ((((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) + (s3rs 12225 46 maskSlack)) := badd (sGlobal12_hz105 hc) sGlobal12_hz29 (by norm_num) (by norm_num)

theorem sGlobal12_hz107 {c : ℝ} (hc : B (81 / 200) (41 / 100) c) : B (1877583475059351925553 / 1000000000000000000) (404110197583615990221 / 200000000000000000) (s3U 12225 46 maskSlack c) := by
    convert (sGlobal12_hz106 hc) using 1 <;>
      norm_num [s3U] <;> ring

theorem sGlobal12_hz108 {c : ℝ} (hc : B (81 / 200) (41 / 100) c) : B (36542647105629765071 / 125000000000000000) (13937374588831002421 / 40000000000000000) ((s3Cpp 12225 c) - (s3rpp 12225 46)) := bsub (sGlobal12_hz90 hc) sGlobal12_hz37 (by norm_num) (by norm_num)

theorem sGlobal12_hz109 {c : ℝ} (hc : B (81 / 200) (41 / 100) c) : B 0 0 (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ)) := bweaken (bmin (sGlobal12_hz108 hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem sGlobal12_hz110 {c : ℝ} (hc : B (81 / 200) (41 / 100) c) : B 0 0 ((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) := bmul (sGlobal12_hz76 hc) (sGlobal12_hz109 hc) (by norm_num) (by norm_num)

theorem sGlobal12_hz111 {c : ℝ} (hc : B (81 / 200) (41 / 100) c) : B (-376278118609407 / 25000000000000000) (-3762781186094069 / 250000000000000000) (((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) := bsub (sGlobal12_hz110 hc) sGlobal12_hz104 (by norm_num) (by norm_num)

theorem sGlobal12_hz112 {c : ℝ} (hc : B (81 / 200) (41 / 100) c) : B (-4814015572358580787 / 125000000000000000) (-38512124575991646407 / 1000000000000000000) ((((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) - (s3rs 12225 46 maskSlack)) := bsub (sGlobal12_hz111 hc) sGlobal12_hz29 (by norm_num) (by norm_num)

theorem sGlobal12_hz113 {c : ℝ} (hc : B (81 / 200) (41 / 100) c) : B (-4814015572358580787 / 125000000000000000) (-38512124575991646407 / 1000000000000000000) (s3L 12225 46 maskSlack c) := by
    convert (sGlobal12_hz112 hc) using 1 <;>
      norm_num [s3L] <;> ring

theorem sGlobal12_hz114 {c : ℝ} (hc : B (81 / 200) (41 / 100) c) : B 0 (404110197583615990221 / 200000000000000000) |(s3U 12225 46 maskSlack c)| := bweaken (babs (sGlobal12_hz107 hc)) (by norm_num) (by norm_num)

theorem sGlobal12_hz115 {c : ℝ} (hc : B (81 / 200) (41 / 100) c) : B 0 (4814015572358580787 / 125000000000000000) |(s3L 12225 46 maskSlack c)| := bweaken (babs (sGlobal12_hz113 hc)) (by norm_num) (by norm_num)

theorem sGlobal12_hz116 {c : ℝ} (hc : B (81 / 200) (41 / 100) c) : B 0 (404110197583615990221 / 200000000000000000) (max |(s3U 12225 46 maskSlack c)| |(s3L 12225 46 maskSlack c)|) := bweaken (bmax (sGlobal12_hz114 hc) (sGlobal12_hz115 hc)) (by norm_num) (by norm_num)

theorem sGlobal12_hz117 {c : ℝ} (hc : B (81 / 200) (41 / 100) c) : B 0 (404110197583615990221 / 200000000000000000) (s3nks 12225 46 maskSlack c) := by
    convert (sGlobal12_hz116 hc) using 1 <;>
      norm_num [s3nks] <;> ring

theorem sGlobal12 {c : ℝ} (hc : B (81 / 200) (41 / 100) c) :
    0 < s3am 12225 46 ∧ 0 ≤ s3dm 12225 46 c ∧
    s3dm 12225 46 c ^ 2 ≤ 2 * s3ap 12225 46 ^ 2 ∧ s3c1 12225 46 c < 1 ∧
    0 ≤ s3Cpa 12225 c - s3r1 12225 46 ∧
    s3e0 12225 46 ≤ (s3Cpa 12225 c - s3r1 12225 46) / s3ap 12225 46 ∧
    s3nks 12225 46 maskSlack c ≤ 12225 * (165281 / 1000000) := by

  refine ⟨lt_of_lt_of_le (by norm_num) sGlobal12_hz14.1,
    le_trans (by norm_num) (sGlobal12_hz64 hc).1, ?_,
    lt_of_le_of_lt (sGlobal12_hz72 hc).2 (by norm_num), ?_, ?_,
    le_trans (sGlobal12_hz117 hc).2 (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (sGlobal12_hz64 hc).1) (sGlobal12_hz64 hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) sGlobal12_hz9.1 2
    nlinarith only [h1, h2]
  · linarith only [(sGlobal12_hz84 hc).1, sGlobal12_hz33.2]
  · have hap : 0 < s3ap 12225 46 := lt_of_lt_of_le (by norm_num) sGlobal12_hz9.1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul sGlobal12_hz16.2 sGlobal12_hz9.2 (le_trans (by norm_num) sGlobal12_hz9.1) (by norm_num)
    linarith only [h, (sGlobal12_hz84 hc).1, sGlobal12_hz33.2]

end BstLean.Part255
