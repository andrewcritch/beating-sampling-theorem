import BstLean.Part255SGlobal7
import BstLean.Part255Numeric10
namespace BstLean.Part255
open Real BstLean.Part130 BstLean.Part182 BstLean.Part197 BstLean.Part246
theorem sGlobal11_hz0 : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal11_hz1 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) ((√(23 : ℝ)) / (12225 : ℝ)) := bdiv sGlobal11_hz0 (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal11_hz2 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) maskSlack := by
    convert sGlobal11_hz1 using 1 <;>
      norm_num [maskSlack] <;> ring

theorem sGlobal11_hz3 : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal11_hz4 : B (6395294793910793 / 500000000000000000) (12790589587821587 / 1000000000000000000) (√((2 / 12225) : ℝ)) := bsqrt (bpoint ((2 / 12225) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal11_hz5 : B (7230130686979 / 62500000000000000) (23136418198333 / 200000000000000000) (√((2 / 149450625) : ℝ)) := bsqrt (bpoint ((2 / 149450625) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal11_hz6 : B (2211334438749598093 / 20000000000000000) (110566721937479904651 / 1000000000000000000) (√(12225 : ℝ)) := bsqrt (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal11_hz7 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))) := bmul sGlobal11_hz3 sGlobal11_hz4 (by norm_num) (by norm_num)

theorem sGlobal11_hz8 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) ((√(12225 : ℝ)) + ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := badd sGlobal11_hz6 sGlobal11_hz7 (by norm_num) (by norm_num)

theorem sGlobal11_hz9 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) (s3ap 12225 46) := by
    convert sGlobal11_hz8 using 1 <;>
      norm_num [s3ap, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal11_hz10 : B (163599182004089 / 1000000000000000000) (16359918200409 / 100000000000000000) ((2 : ℝ) / (12225 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal11_hz11 : B (1222499983640081799591 / 100000000000000000) (12224999836400817995911 / 1000000000000000000) ((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ))) := bsub (bpoint (12225 : ℝ)) sGlobal11_hz10 (by norm_num) (by norm_num)

theorem sGlobal11_hz12 : B (110566721197658827907 / 1000000000000000000) (27641680299414706977 / 250000000000000000) (√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) := bsqrt sGlobal11_hz11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal11_hz13 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) ((√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) - ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bsub sGlobal11_hz12 sGlobal11_hz7 (by norm_num) (by norm_num)

theorem sGlobal11_hz14 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) (s3am 12225 46) := by
    convert sGlobal11_hz13 using 1 <;>
      norm_num [s3am, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal11_hz15 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√((2 / 12225) : ℝ)) * (√(92 : ℝ))) := bmul sGlobal11_hz4 sGlobal11_hz3 (by norm_num) (by norm_num)

theorem sGlobal11_hz16 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) (s3e0 12225 46) := by
    convert sGlobal11_hz15 using 1 <;>
      norm_num [s3e0, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal11_hz17 : B (250196148528560847 / 500000000000000000) (100078459411424339 / 200000000000000000) (((1 / 2) : ℝ) + maskSlack) := badd (bpoint ((1 / 2) : ℝ)) sGlobal11_hz2 (by norm_num) (by norm_num)

theorem sGlobal11_hz18 : B (59827153232297998295487 / 800000000000000) (23930861292919199366019 / 320000000000000) ((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack)) := bmul (bpoint (149450625 : ℝ)) sGlobal11_hz17 (by norm_num) (by norm_num)

theorem sGlobal11_hz19 : B (1729554180017180009583 / 200000000000000000) (8647770900085900056557 / 1000000000000000000) (√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) := bsqrt sGlobal11_hz18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal11_hz20 : B (4328681281566262743499 / 500000000000000000) (8657362563132525495641 / 1000000000000000000) ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))) := badd sGlobal11_hz19 sGlobal11_hz3 (by norm_num) (by norm_num)

theorem sGlobal11_hz21 : B (110732771457999278473 / 1000000000000000000) (55366385728999643621 / 500000000000000000) ((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ)))) := bmul sGlobal11_hz4 sGlobal11_hz20 (by norm_num) (by norm_num)

theorem sGlobal11_hz22 : B (209099159 / 15625000000000000) (13382346177 / 1000000000000000000) ((2 : ℝ) / (149450625 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (149450625 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal11_hz23 : B (2452349334953899930479 / 200000000000000000) (12261746674769501594427 / 1000000000000000000) (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2) := bsq sGlobal11_hz21 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal11_hz24 : B (82045469362091 / 500000000000000000) (32818187747289 / 200000000000000000) (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2)) := bmul sGlobal11_hz22 sGlobal11_hz23 (by norm_num) (by norm_num)

theorem sGlobal11_hz25 : B (82045469362091 / 250000000000000000) (32818187747289 / 100000000000000000) ((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) := bmul (bpoint (2 : ℝ)) sGlobal11_hz24 (by norm_num) (by norm_num)

theorem sGlobal11_hz26 : B (117258080744995992792057 / 1000000000000000000) (58629040372497996396029 / 500000000000000000) (√(13749457500 : ℝ)) := bsqrt (bpoint (13749457500 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal11_hz27 : B (117304080744995992792057 / 1000000000000000000) (58652040372497996396029 / 500000000000000000) ((√(13749457500 : ℝ)) + (46 : ℝ)) := badd sGlobal11_hz26 (bpoint (46 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal11_hz28 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal11_hz25 sGlobal11_hz27 (by norm_num) (by norm_num)

theorem sGlobal11_hz29 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (s3rs 12225 46 maskSlack) := by
    convert sGlobal11_hz28 using 1 <;>
      norm_num [s3rs, s3pp, s3K, mA, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal11_hz30 : B (490797546012267 / 1000000000000000000) (49079754601227 / 100000000000000000) ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (3 : ℝ)) sGlobal11_hz10 (by norm_num) (by norm_num)

theorem sGlobal11_hz31 : B (490797546012267 / 500000000000000000) (49079754601227 / 50000000000000000) ((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal11_hz30 (by norm_num) (by norm_num)

theorem sGlobal11_hz32 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal11_hz31 sGlobal11_hz27 (by norm_num) (by norm_num)

theorem sGlobal11_hz33 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (s3r1 12225 46) := by
    convert sGlobal11_hz32 using 1 <;>
      norm_num [s3r1, mA] <;> ring

theorem sGlobal11_hz34 : B (163599182004089 / 500000000000000000) (16359918200409 / 50000000000000000) ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (2 : ℝ)) sGlobal11_hz10 (by norm_num) (by norm_num)

theorem sGlobal11_hz35 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal11_hz34 (by norm_num) (by norm_num)

theorem sGlobal11_hz36 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal11_hz35 sGlobal11_hz27 (by norm_num) (by norm_num)

theorem sGlobal11_hz37 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (s3rpp 12225 46) := by
    convert sGlobal11_hz36 using 1 <;>
      norm_num [s3rpp, mA] <;> ring

theorem sGlobal11_hz38 {c : ℝ} (hc : B (2 / 5) (81 / 200) c) : B (2 / 5) (81 / 200) c := hc

theorem sGlobal11_hz39 : B (315494940215399341 / 500000000000000000) (630989880455876101 / 1000000000000000000) (kdot ((2 / 5))) := by
    constructor
    · apply bkdot_lower (q := (81831708838497143 / 125000000000000000)) (a := (579639740369447029 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (654653670707977143 / 1000000000000000000)) (a := (579639740330055513 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal11_hz40 : B (4 / 25) (4 / 25) (((2 / 5) : ℝ)^2) := bsq (bpoint ((2 / 5) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal11_hz41 : B (21 / 25) (21 / 25) ((1 : ℝ) - (((2 / 5) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal11_hz40 (by norm_num) (by norm_num)

theorem sGlobal11_hz42 : B (916515138991168001 / 1000000000000000000) (458257569495584001 / 500000000000000000) (√((1 : ℝ) - (((2 / 5) : ℝ)^2))) := bsqrt sGlobal11_hz41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal11_hz43 : B (145867914788999887 / 500000000000000000) (11669433183119991 / 40000000000000000) ((√((1 : ℝ) - (((2 / 5) : ℝ)^2))) / Real.pi) := bdiv sGlobal11_hz42 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal11_hz44 : B (15774747010769967 / 62500000000000000) (252395952182350441 / 1000000000000000000) (((2 / 5) : ℝ) * (kdot ((2 / 5)))) := bmul (bpoint ((2 / 5) : ℝ)) sGlobal11_hz39 (by norm_num) (by norm_num)

theorem sGlobal11_hz45 : B (272065890875159623 / 500000000000000000) (68016472720043777 / 125000000000000000) (((√((1 : ℝ) - (((2 / 5) : ℝ)^2))) / Real.pi) + (((2 / 5) : ℝ) * (kdot ((2 / 5))))) := badd sGlobal11_hz43 sGlobal11_hz44 (by norm_num) (by norm_num)

theorem sGlobal11_hz46 : B (272065890875159623 / 500000000000000000) (68016472720043777 / 125000000000000000) (kappa ((2 / 5))) := by rw [kappa_eq]; exact sGlobal11_hz45

theorem sGlobal11_hz47 : B (158182121028224703 / 250000000000000000) (316364242065809491 / 500000000000000000) (kdot ((81 / 200))) := by
    constructor
    · apply bkdot_lower (q := (650759206222997483 / 1000000000000000000)) (a := (576908748091852063 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (325379603111498741 / 500000000000000000)) (a := (576908748062446489 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal11_hz48 : B (6561 / 40000) (6561 / 40000) (((81 / 200) : ℝ)^2) := bsq (bpoint ((81 / 200) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal11_hz49 : B (33439 / 40000) (33439 / 40000) ((1 : ℝ) - (((81 / 200) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal11_hz48 (by norm_num) (by norm_num)

theorem sGlobal11_hz50 : B (457158342371655731 / 500000000000000000) (914316684743311463 / 1000000000000000000) (√((1 : ℝ) - (((81 / 200) : ℝ)^2))) := bsqrt sGlobal11_hz49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal11_hz51 : B (9094876245518259 / 31250000000000000) (291036039856584289 / 1000000000000000000) ((√((1 : ℝ) - (((81 / 200) : ℝ)^2))) / Real.pi) := bdiv sGlobal11_hz50 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal11_hz52 : B (128127518032862009 / 500000000000000000) (32031879509163211 / 125000000000000000) (((81 / 200) : ℝ) * (kdot ((81 / 200)))) := bmul (bpoint ((81 / 200) : ℝ)) sGlobal11_hz47 (by norm_num) (by norm_num)

theorem sGlobal11_hz53 : B (273645537961154153 / 500000000000000000) (547291075929889977 / 1000000000000000000) (((√((1 : ℝ) - (((81 / 200) : ℝ)^2))) / Real.pi) + (((81 / 200) : ℝ) * (kdot ((81 / 200))))) := badd sGlobal11_hz51 sGlobal11_hz52 (by norm_num) (by norm_num)

theorem sGlobal11_hz54 : B (273645537961154153 / 500000000000000000) (547291075929889977 / 1000000000000000000) (kappa ((81 / 200))) := by rw [kappa_eq]; exact sGlobal11_hz53

theorem sGlobal11_hz55 {c : ℝ} (hc : B (2 / 5) (81 / 200) c) : B (272065890875159623 / 500000000000000000) (547291075929889977 / 1000000000000000000) (kappa c) := bkappa (sGlobal11_hz38 hc) (by norm_num) (by norm_num) sGlobal11_hz46.1 sGlobal11_hz54.2

theorem sGlobal11_hz56 : B 24450 24450 ((2 : ℝ) * (12225 : ℝ)) := bmul (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal11_hz57 {c : ℝ} (hc : B (2 / 5) (81 / 200) c) : B (452708924070110023 / 1000000000000000000) (227934109124840377 / 500000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (sGlobal11_hz55 hc) (by norm_num) (by norm_num)

theorem sGlobal11_hz58 {c : ℝ} (hc : B (2 / 5) (81 / 200) c) : B (221374663870283801247 / 20000000000000000) (111459779362046944353 / 10000000000000000) (((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) := bmul sGlobal11_hz56 (sGlobal11_hz57 hc) (by norm_num) (by norm_num)

theorem sGlobal11_hz59 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (4 : ℝ)) sGlobal11_hz10 (by norm_num) (by norm_num)

theorem sGlobal11_hz60 {c : ℝ} (hc : B (2 / 5) (81 / 200) c) : B (1106873253911746204599 / 100000000000000000) (5442371719632796103 / 488281250000000) ((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bsub (sGlobal11_hz58 hc) sGlobal11_hz59 (by norm_num) (by norm_num)

theorem sGlobal11_hz61 {c : ℝ} (hc : B (2 / 5) (81 / 200) c) : B (105208044079896581099 / 1000000000000000000) (84459608454912331 / 800000000000000) (√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) := bsqrt (sGlobal11_hz60 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal11_hz62 : B (30670756373515103 / 125000000000000000) (122683025494060423 / 500000000000000000) ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal11_hz7 (by norm_num) (by norm_num)

theorem sGlobal11_hz63 {c : ℝ} (hc : B (2 / 5) (81 / 200) c) : B (104962678028908460253 / 1000000000000000000) (52664572258826146463 / 500000000000000000) ((√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) - ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))))) := bsub (sGlobal11_hz61 hc) sGlobal11_hz62 (by norm_num) (by norm_num)

theorem sGlobal11_hz64 {c : ℝ} (hc : B (2 / 5) (81 / 200) c) : B (104962678028908460253 / 1000000000000000000) (52664572258826146463 / 500000000000000000) (s3dm 12225 46 c) := by
    convert (sGlobal11_hz63 hc) using 1 <;>
      norm_num [s3dm, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal11_hz65 : B (6126072185528622723889 / 500000000000000000) (2450428874211449090087 / 200000000000000000) ((s3ap 12225 46)^2) := bsq sGlobal11_hz9 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal11_hz66 : B (6126072185528622723889 / 250000000000000000) (2450428874211449090087 / 100000000000000000) ((2 : ℝ) * ((s3ap 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal11_hz65 (by norm_num) (by norm_num)

theorem sGlobal11_hz67 {c : ℝ} (hc : B (2 / 5) (81 / 200) c) : B (5508581889500151405429 / 500000000000000000) (1109422868482048207503 / 100000000000000000) ((s3dm 12225 46 c)^2) := bsq (sGlobal11_hz64 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal11_hz68 {c : ℝ} (hc : B (2 / 5) (81 / 200) c) : B (6705030028647004410263 / 500000000000000000) (3371781240778547022503 / 250000000000000000) (((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) := bsub sGlobal11_hz66 (sGlobal11_hz67 hc) (by norm_num) (by norm_num)

theorem sGlobal11_hz69 : B (1524735695971823534271 / 125000000000000000) (609894278388729413841 / 50000000000000000) ((s3am 12225 46)^2) := bsq sGlobal11_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal11_hz70 : B (1524735695971823534271 / 62500000000000000) (609894278388729413841 / 25000000000000000) ((2 : ℝ) * ((s3am 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal11_hz69 (by norm_num) (by norm_num)

theorem sGlobal11_hz71 {c : ℝ} (hc : B (2 / 5) (81 / 200) c) : B (68710986746351793 / 125000000000000000) (276423419620069689 / 500000000000000000) ((((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) / ((2 : ℝ) * ((s3am 12225 46)^2))) := bdiv (sGlobal11_hz68 hc) sGlobal11_hz70 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal11_hz72 {c : ℝ} (hc : B (2 / 5) (81 / 200) c) : B (68710986746351793 / 125000000000000000) (276423419620069689 / 500000000000000000) (s3c1 12225 46 c) := by
    convert (sGlobal11_hz71 hc) using 1 <;>
      norm_num [s3c1] <;> ring

theorem sGlobal11_hz73 {c : ℝ} (hc : B (2 / 5) (81 / 200) c) : B (315494940215399341 / 500000000000000000) (316364242065809491 / 500000000000000000) (kdot c) := bkdot (sGlobal11_hz38 hc) sGlobal11_hz39.1 sGlobal11_hz47.2

theorem sGlobal11_hz74 : B (342626677297731311 / 500000000000000000) (137050670919092893 / 200000000000000000) (kdot ((68710986746351793 / 125000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (53905700133331429 / 100000000000000000)) (a := (24720143723623157 / 50000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (539057001333314289 / 1000000000000000000)) (a := (61800359309057531 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal11_hz75 : B (68645854502070241 / 100000000000000000) (343229272510351943 / 500000000000000000) (kdot ((276423419620069689 / 500000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (134154069076272639 / 250000000000000000)) (a := (246254882889704051 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (107323255261018111 / 200000000000000000)) (a := (246254882889702893 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal11_hz76 {c : ℝ} (hc : B (2 / 5) (81 / 200) c) : B (342626677297731311 / 500000000000000000) (343229272510351943 / 500000000000000000) (kdot (s3c1 12225 46 c)) := bkdot (sGlobal11_hz72 hc) sGlobal11_hz74.1 sGlobal11_hz75.2

theorem sGlobal11_hz77 {c : ℝ} (hc : B (2 / 5) (81 / 200) c) : B (4 / 25) (6561 / 40000) (c^2) := bsq (sGlobal11_hz38 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal11_hz78 {c : ℝ} (hc : B (2 / 5) (81 / 200) c) : B (33439 / 40000) (21 / 25) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (sGlobal11_hz77 hc) (by norm_num) (by norm_num)

theorem sGlobal11_hz79 {c : ℝ} (hc : B (2 / 5) (81 / 200) c) : B (457158342371655731 / 500000000000000000) (458257569495584001 / 500000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (sGlobal11_hz78 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal11_hz80 : B (39119999999999765769 / 1600000000000000) (3912000000000000489 / 160000000000000) ((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (149450625 : ℝ)) sGlobal11_hz10 (by norm_num) (by norm_num)

theorem sGlobal11_hz81 {c : ℝ} (hc : B (2 / 5) (81 / 200) c) : B (36057785973879147 / 62500000000000000) (579905234577561809 / 1000000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (sGlobal11_hz79 hc) (sGlobal11_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal11_hz82 {c : ℝ} (hc : B (2 / 5) (81 / 200) c) : B (14105805872981437847887 / 1000000000000000000) (7089341492710694001193 / 500000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) := bmul sGlobal11_hz80 (sGlobal11_hz81 hc) (by norm_num) (by norm_num)

theorem sGlobal11_hz83 {c : ℝ} (hc : B (2 / 5) (81 / 200) c) : B (7052902936490718923943 / 1000000000000000000) (7089341492710694001193 / 1000000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) / (2 : ℝ)) := bdiv (sGlobal11_hz82 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal11_hz84 {c : ℝ} (hc : B (2 / 5) (81 / 200) c) : B (7052902936490718923943 / 1000000000000000000) (7089341492710694001193 / 1000000000000000000) (s3Cpa 12225 c) := by
    convert (sGlobal11_hz83 hc) using 1 <;>
      norm_num [s3Cpa, mA] <;> ring

theorem sGlobal11_hz85 {c : ℝ} (hc : B (2 / 5) (81 / 200) c) : B (9094876245518259 / 31250000000000000) (11669433183119991 / 40000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (sGlobal11_hz79 hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal11_hz86 {c : ℝ} (hc : B (2 / 5) (81 / 200) c) : B (15774747010769967 / 62500000000000000) (32031879509163211 / 125000000000000000) (c * (kdot c)) := bmul (sGlobal11_hz38 hc) (sGlobal11_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal11_hz87 {c : ℝ} (hc : B (2 / 5) (81 / 200) c) : B (173905018916393 / 5000000000000000) (39339877405680303 / 1000000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (sGlobal11_hz85 hc) (sGlobal11_hz86 hc) (by norm_num) (by norm_num)

theorem sGlobal11_hz88 {c : ℝ} (hc : B (2 / 5) (81 / 200) c) : B (53149721406322292391 / 62500000000000000) (961860002568883528583 / 1000000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) := bmul sGlobal11_hz80 (sGlobal11_hz87 hc) (by norm_num) (by norm_num)

theorem sGlobal11_hz89 {c : ℝ} (hc : B (2 / 5) (81 / 200) c) : B (53149721406322292391 / 125000000000000000) (120232500321110441073 / 250000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) / (2 : ℝ)) := bdiv (sGlobal11_hz88 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal11_hz90 {c : ℝ} (hc : B (2 / 5) (81 / 200) c) : B (53149721406322292391 / 125000000000000000) (120232500321110441073 / 250000000000000000) (s3Cpp 12225 c) := by
    convert (sGlobal11_hz89 hc) using 1 <;>
      norm_num [s3Cpp, mA] <;> ring

theorem sGlobal11_hz91 {c : ℝ} (hc : B (2 / 5) (81 / 200) c) : B (896006005803057079043 / 125000000000000000) (7204486602644432413419 / 1000000000000000000) ((s3Cpa 12225 c) + (s3r1 12225 46)) := badd (sGlobal11_hz84 hc) sGlobal11_hz33 (by norm_num) (by norm_num)

theorem sGlobal11_hz92 {c : ℝ} (hc : B (2 / 5) (81 / 200) c) : B (8112760277800831513 / 125000000000000000) (16308002500356285821 / 250000000000000000) (((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) := bdiv (sGlobal11_hz91 hc) sGlobal11_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal11_hz93 {c : ℝ} (hc : B (2 / 5) (81 / 200) c) : B (16256191311975178129 / 250000000000000000) (65354693026919203707 / 1000000000000000000) ((((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) + (s3e0 12225 46)) := badd (sGlobal11_hz92 hc) sGlobal11_hz16 (by norm_num) (by norm_num)

theorem sGlobal11_hz94 {c : ℝ} (hc : B (2 / 5) (81 / 200) c) : B (16256191311975178129 / 250000000000000000) (65354693026919203707 / 1000000000000000000) (s3Lam 12225 46 c) := by
    convert (sGlobal11_hz93 hc) using 1 <;>
      norm_num [s3Lam] <;> ring

theorem sGlobal11_hz95 {c : ℝ} (hc : B (2 / 5) (81 / 200) c) : B (62745147234133768091 / 125000000000000000) (55769340790693403911 / 100000000000000000) ((s3Cpp 12225 c) + (s3rpp 12225 46)) := badd (sGlobal11_hz90 hc) sGlobal11_hz37 (by norm_num) (by norm_num)

theorem sGlobal11_hz96 {c : ℝ} (hc : B (2 / 5) (81 / 200) c) : B (62745147234133768091 / 250000000000000000) (382833405359431856639 / 1000000000000000000) (if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) := bweaken (bfirst (sGlobal11_hz95 hc) (sGlobal11_hz76 hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem sGlobal11_hz97 {c : ℝ} (hc : B (2 / 5) (81 / 200) c) : B (169128803821783848433 / 40000000000000000) (1067808975160710397219 / 250000000000000000) ((s3Lam 12225 46 c)^2) := bsq (sGlobal11_hz94 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal11_hz98 {c : ℝ} (hc : B (2 / 5) (81 / 200) c) : B (18884798798629327 / 62500000000000000) (152819813828906257 / 500000000000000000) ((s3c1 12225 46 c)^2) := bsq (sGlobal11_hz72 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal11_hz99 {c : ℝ} (hc : B (2 / 5) (81 / 200) c) : B (347180186171093743 / 500000000000000000) (43615201201370673 / 62500000000000000) ((1 : ℝ) - ((s3c1 12225 46 c)^2)) := bsub (bpoint (1 : ℝ)) (sGlobal11_hz98 hc) (by norm_num) (by norm_num)

theorem sGlobal11_hz100 {c : ℝ} (hc : B (2 / 5) (81 / 200) c) : B (416641444272586583 / 500000000000000000) (835370109126446281 / 1000000000000000000) (√((1 : ℝ) - ((s3c1 12225 46 c)^2))) := bsqrt (sGlobal11_hz99 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal11_hz101 {c : ℝ} (hc : B (2 / 5) (81 / 200) c) : B (261783540101559849 / 100000000000000000) (2624392597860147527 / 1000000000000000000) (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))) := bmul pi_mem (sGlobal11_hz100 hc) (by norm_num) (by norm_num)

theorem sGlobal11_hz102 {c : ℝ} (hc : B (2 / 5) (81 / 200) c) : B (1611123312492255318571 / 1000000000000000000) (815795351187053344769 / 500000000000000000) (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2))))) := bdiv (sGlobal11_hz97 hc) (sGlobal11_hz101 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal11_hz103 {c : ℝ} (hc : B (2 / 5) (81 / 200) c) : B (372420780285758078187 / 200000000000000000) (2014424107733538546177 / 1000000000000000000) ((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) := badd (sGlobal11_hz96 hc) (sGlobal11_hz102 hc) (by norm_num) (by norm_num)

theorem sGlobal11_hz104 : B (3762781186094069 / 250000000000000000) (376278118609407 / 25000000000000000) ((s3e0 12225 46)^2) := bsq sGlobal11_hz16 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal11_hz105 {c : ℝ} (hc : B (2 / 5) (81 / 200) c) : B (1862118952553534767211 / 1000000000000000000) (2014439158858282922457 / 1000000000000000000) (((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) := badd (sGlobal11_hz103 hc) sGlobal11_hz104 (by norm_num) (by norm_num)

theorem sGlobal11_hz106 {c : ℝ} (hc : B (2 / 5) (81 / 200) c) : B (950308013002391018671 / 500000000000000000) (2052936232312407192473 / 1000000000000000000) ((((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) + (s3rs 12225 46 maskSlack)) := badd (sGlobal11_hz105 hc) sGlobal11_hz29 (by norm_num) (by norm_num)

theorem sGlobal11_hz107 {c : ℝ} (hc : B (2 / 5) (81 / 200) c) : B (950308013002391018671 / 500000000000000000) (2052936232312407192473 / 1000000000000000000) (s3U 12225 46 maskSlack c) := by
    convert (sGlobal11_hz106 hc) using 1 <;>
      norm_num [s3U] <;> ring

theorem sGlobal11_hz108 {c : ℝ} (hc : B (2 / 5) (81 / 200) c) : B (34843436462808606431 / 100000000000000000) (101041648665487489673 / 250000000000000000) ((s3Cpp 12225 c) - (s3rpp 12225 46)) := bsub (sGlobal11_hz90 hc) sGlobal11_hz37 (by norm_num) (by norm_num)

theorem sGlobal11_hz109 {c : ℝ} (hc : B (2 / 5) (81 / 200) c) : B 0 0 (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ)) := bweaken (bmin (sGlobal11_hz108 hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem sGlobal11_hz110 {c : ℝ} (hc : B (2 / 5) (81 / 200) c) : B 0 0 ((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) := bmul (sGlobal11_hz76 hc) (sGlobal11_hz109 hc) (by norm_num) (by norm_num)

theorem sGlobal11_hz111 {c : ℝ} (hc : B (2 / 5) (81 / 200) c) : B (-376278118609407 / 25000000000000000) (-3762781186094069 / 250000000000000000) (((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) := bsub (sGlobal11_hz110 hc) sGlobal11_hz104 (by norm_num) (by norm_num)

theorem sGlobal11_hz112 {c : ℝ} (hc : B (2 / 5) (81 / 200) c) : B (-4814015572358580787 / 125000000000000000) (-38512124575991646407 / 1000000000000000000) ((((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) - (s3rs 12225 46 maskSlack)) := bsub (sGlobal11_hz111 hc) sGlobal11_hz29 (by norm_num) (by norm_num)

theorem sGlobal11_hz113 {c : ℝ} (hc : B (2 / 5) (81 / 200) c) : B (-4814015572358580787 / 125000000000000000) (-38512124575991646407 / 1000000000000000000) (s3L 12225 46 maskSlack c) := by
    convert (sGlobal11_hz112 hc) using 1 <;>
      norm_num [s3L] <;> ring

theorem sGlobal11_hz114 {c : ℝ} (hc : B (2 / 5) (81 / 200) c) : B 0 (2052936232312407192473 / 1000000000000000000) |(s3U 12225 46 maskSlack c)| := bweaken (babs (sGlobal11_hz107 hc)) (by norm_num) (by norm_num)

theorem sGlobal11_hz115 {c : ℝ} (hc : B (2 / 5) (81 / 200) c) : B 0 (4814015572358580787 / 125000000000000000) |(s3L 12225 46 maskSlack c)| := bweaken (babs (sGlobal11_hz113 hc)) (by norm_num) (by norm_num)

theorem sGlobal11_hz116 {c : ℝ} (hc : B (2 / 5) (81 / 200) c) : B 0 (2052936232312407192473 / 1000000000000000000) (max |(s3U 12225 46 maskSlack c)| |(s3L 12225 46 maskSlack c)|) := bweaken (bmax (sGlobal11_hz114 hc) (sGlobal11_hz115 hc)) (by norm_num) (by norm_num)

theorem sGlobal11_hz117 {c : ℝ} (hc : B (2 / 5) (81 / 200) c) : B 0 (2052936232312407192473 / 1000000000000000000) (s3nks 12225 46 maskSlack c) := by
    convert (sGlobal11_hz116 hc) using 1 <;>
      norm_num [s3nks] <;> ring

theorem sGlobal11 {c : ℝ} (hc : B (2 / 5) (81 / 200) c) :
    0 < s3am 12225 46 ∧ 0 ≤ s3dm 12225 46 c ∧
    s3dm 12225 46 c ^ 2 ≤ 2 * s3ap 12225 46 ^ 2 ∧ s3c1 12225 46 c < 1 ∧
    0 ≤ s3Cpa 12225 c - s3r1 12225 46 ∧
    s3e0 12225 46 ≤ (s3Cpa 12225 c - s3r1 12225 46) / s3ap 12225 46 ∧
    s3nks 12225 46 maskSlack c ≤ 12225 * (16793 / 100000) := by

  refine ⟨lt_of_lt_of_le (by norm_num) sGlobal11_hz14.1,
    le_trans (by norm_num) (sGlobal11_hz64 hc).1, ?_,
    lt_of_le_of_lt (sGlobal11_hz72 hc).2 (by norm_num), ?_, ?_,
    le_trans (sGlobal11_hz117 hc).2 (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (sGlobal11_hz64 hc).1) (sGlobal11_hz64 hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) sGlobal11_hz9.1 2
    nlinarith only [h1, h2]
  · linarith only [(sGlobal11_hz84 hc).1, sGlobal11_hz33.2]
  · have hap : 0 < s3ap 12225 46 := lt_of_lt_of_le (by norm_num) sGlobal11_hz9.1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul sGlobal11_hz16.2 sGlobal11_hz9.2 (le_trans (by norm_num) sGlobal11_hz9.1) (by norm_num)
    linarith only [h, (sGlobal11_hz84 hc).1, sGlobal11_hz33.2]

end BstLean.Part255
