import BstLean.Part255SGlobal25
import BstLean.Part255Numeric10
namespace BstLean.Part255
open Real BstLean.Part130 BstLean.Part182 BstLean.Part197 BstLean.Part246
theorem sGlobal29_hz0 : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal29_hz1 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) ((√(23 : ℝ)) / (12225 : ℝ)) := bdiv sGlobal29_hz0 (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal29_hz2 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) maskSlack := by
    convert sGlobal29_hz1 using 1 <;>
      norm_num [maskSlack] <;> ring

theorem sGlobal29_hz3 : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal29_hz4 : B (6395294793910793 / 500000000000000000) (12790589587821587 / 1000000000000000000) (√((2 / 12225) : ℝ)) := bsqrt (bpoint ((2 / 12225) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal29_hz5 : B (7230130686979 / 62500000000000000) (23136418198333 / 200000000000000000) (√((2 / 149450625) : ℝ)) := bsqrt (bpoint ((2 / 149450625) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal29_hz6 : B (2211334438749598093 / 20000000000000000) (110566721937479904651 / 1000000000000000000) (√(12225 : ℝ)) := bsqrt (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal29_hz7 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))) := bmul sGlobal29_hz3 sGlobal29_hz4 (by norm_num) (by norm_num)

theorem sGlobal29_hz8 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) ((√(12225 : ℝ)) + ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := badd sGlobal29_hz6 sGlobal29_hz7 (by norm_num) (by norm_num)

theorem sGlobal29_hz9 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) (s3ap 12225 46) := by
    convert sGlobal29_hz8 using 1 <;>
      norm_num [s3ap, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal29_hz10 : B (163599182004089 / 1000000000000000000) (16359918200409 / 100000000000000000) ((2 : ℝ) / (12225 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal29_hz11 : B (1222499983640081799591 / 100000000000000000) (12224999836400817995911 / 1000000000000000000) ((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ))) := bsub (bpoint (12225 : ℝ)) sGlobal29_hz10 (by norm_num) (by norm_num)

theorem sGlobal29_hz12 : B (110566721197658827907 / 1000000000000000000) (27641680299414706977 / 250000000000000000) (√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) := bsqrt sGlobal29_hz11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal29_hz13 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) ((√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) - ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bsub sGlobal29_hz12 sGlobal29_hz7 (by norm_num) (by norm_num)

theorem sGlobal29_hz14 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) (s3am 12225 46) := by
    convert sGlobal29_hz13 using 1 <;>
      norm_num [s3am, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal29_hz15 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√((2 / 12225) : ℝ)) * (√(92 : ℝ))) := bmul sGlobal29_hz4 sGlobal29_hz3 (by norm_num) (by norm_num)

theorem sGlobal29_hz16 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) (s3e0 12225 46) := by
    convert sGlobal29_hz15 using 1 <;>
      norm_num [s3e0, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal29_hz17 : B (250196148528560847 / 500000000000000000) (100078459411424339 / 200000000000000000) (((1 / 2) : ℝ) + maskSlack) := badd (bpoint ((1 / 2) : ℝ)) sGlobal29_hz2 (by norm_num) (by norm_num)

theorem sGlobal29_hz18 : B (59827153232297998295487 / 800000000000000) (23930861292919199366019 / 320000000000000) ((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack)) := bmul (bpoint (149450625 : ℝ)) sGlobal29_hz17 (by norm_num) (by norm_num)

theorem sGlobal29_hz19 : B (1729554180017180009583 / 200000000000000000) (8647770900085900056557 / 1000000000000000000) (√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) := bsqrt sGlobal29_hz18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal29_hz20 : B (4328681281566262743499 / 500000000000000000) (8657362563132525495641 / 1000000000000000000) ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))) := badd sGlobal29_hz19 sGlobal29_hz3 (by norm_num) (by norm_num)

theorem sGlobal29_hz21 : B (110732771457999278473 / 1000000000000000000) (55366385728999643621 / 500000000000000000) ((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ)))) := bmul sGlobal29_hz4 sGlobal29_hz20 (by norm_num) (by norm_num)

theorem sGlobal29_hz22 : B (209099159 / 15625000000000000) (13382346177 / 1000000000000000000) ((2 : ℝ) / (149450625 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (149450625 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal29_hz23 : B (2452349334953899930479 / 200000000000000000) (12261746674769501594427 / 1000000000000000000) (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2) := bsq sGlobal29_hz21 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal29_hz24 : B (82045469362091 / 500000000000000000) (32818187747289 / 200000000000000000) (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2)) := bmul sGlobal29_hz22 sGlobal29_hz23 (by norm_num) (by norm_num)

theorem sGlobal29_hz25 : B (82045469362091 / 250000000000000000) (32818187747289 / 100000000000000000) ((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) := bmul (bpoint (2 : ℝ)) sGlobal29_hz24 (by norm_num) (by norm_num)

theorem sGlobal29_hz26 : B (117258080744995992792057 / 1000000000000000000) (58629040372497996396029 / 500000000000000000) (√(13749457500 : ℝ)) := bsqrt (bpoint (13749457500 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal29_hz27 : B (117304080744995992792057 / 1000000000000000000) (58652040372497996396029 / 500000000000000000) ((√(13749457500 : ℝ)) + (46 : ℝ)) := badd sGlobal29_hz26 (bpoint (46 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal29_hz28 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal29_hz25 sGlobal29_hz27 (by norm_num) (by norm_num)

theorem sGlobal29_hz29 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (s3rs 12225 46 maskSlack) := by
    convert sGlobal29_hz28 using 1 <;>
      norm_num [s3rs, s3pp, s3K, mA, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal29_hz30 : B (490797546012267 / 1000000000000000000) (49079754601227 / 100000000000000000) ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (3 : ℝ)) sGlobal29_hz10 (by norm_num) (by norm_num)

theorem sGlobal29_hz31 : B (490797546012267 / 500000000000000000) (49079754601227 / 50000000000000000) ((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal29_hz30 (by norm_num) (by norm_num)

theorem sGlobal29_hz32 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal29_hz31 sGlobal29_hz27 (by norm_num) (by norm_num)

theorem sGlobal29_hz33 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (s3r1 12225 46) := by
    convert sGlobal29_hz32 using 1 <;>
      norm_num [s3r1, mA] <;> ring

theorem sGlobal29_hz34 : B (163599182004089 / 500000000000000000) (16359918200409 / 50000000000000000) ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (2 : ℝ)) sGlobal29_hz10 (by norm_num) (by norm_num)

theorem sGlobal29_hz35 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal29_hz34 (by norm_num) (by norm_num)

theorem sGlobal29_hz36 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal29_hz35 sGlobal29_hz27 (by norm_num) (by norm_num)

theorem sGlobal29_hz37 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (s3rpp 12225 46) := by
    convert sGlobal29_hz36 using 1 <;>
      norm_num [s3rpp, mA] <;> ring

theorem sGlobal29_hz38 {c : ℝ} (hc : B (49 / 100) (99 / 200) c) : B (49 / 100) (99 / 200) c := hc

theorem sGlobal29_hz39 : B (331501615486170743 / 500000000000000000) (331501615486221571 / 500000000000000000) (kdot ((49 / 100))) := by
    constructor
    · apply bkdot_lower (q := (117009722535288643 / 200000000000000000)) (a := (529353286930394177 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (292524306338221607 / 500000000000000000)) (a := (529353286930234499 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal29_hz40 : B (2401 / 10000) (2401 / 10000) (((49 / 100) : ℝ)^2) := bsq (bpoint ((49 / 100) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal29_hz41 : B (7599 / 10000) (7599 / 10000) ((1 : ℝ) - (((49 / 100) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal29_hz40 (by norm_num) (by norm_num)

theorem sGlobal29_hz42 : B (87172243288790039 / 100000000000000000) (871722432887900391 / 1000000000000000000) (√((1 : ℝ) - (((49 / 100) : ℝ)^2))) := bsqrt sGlobal29_hz41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal29_hz43 : B (11099114735856187 / 40000000000000000) (69369467099101169 / 250000000000000000) ((√((1 : ℝ) - (((49 / 100) : ℝ)^2))) / Real.pi) := bdiv sGlobal29_hz42 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal29_hz44 : B (10152236974263979 / 31250000000000000) (16243579158824857 / 50000000000000000) (((49 / 100) : ℝ) * (kdot ((49 / 100)))) := bmul (bpoint ((49 / 100) : ℝ)) sGlobal29_hz39 (by norm_num) (by norm_num)

theorem sGlobal29_hz45 : B (602349451572852003 / 1000000000000000000) (75293681446612727 / 125000000000000000) (((√((1 : ℝ) - (((49 / 100) : ℝ)^2))) / Real.pi) + (((49 / 100) : ℝ) * (kdot ((49 / 100))))) := badd sGlobal29_hz43 sGlobal29_hz44 (by norm_num) (by norm_num)

theorem sGlobal29_hz46 : B (602349451572852003 / 1000000000000000000) (75293681446612727 / 125000000000000000) (kappa ((49 / 100))) := by rw [kappa_eq]; exact sGlobal29_hz45

theorem sGlobal29_hz47 : B (332415973159448007 / 500000000000000000) (83103993289871197 / 125000000000000000) (kdot ((99 / 200))) := by
    constructor
    · apply bkdot_lower (q := (290599656804885193 / 500000000000000000)) (a := (526480747581272869 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (116239862721954077 / 200000000000000000)) (a := (526480747581157319 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal29_hz48 : B (9801 / 40000) (9801 / 40000) (((99 / 200) : ℝ)^2) := bsq (bpoint ((99 / 200) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal29_hz49 : B (30199 / 40000) (30199 / 40000) ((1 : ℝ) - (((99 / 200) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal29_hz48 (by norm_num) (by norm_num)

theorem sGlobal29_hz50 : B (434446486923303363 / 500000000000000000) (868892973846606727 / 1000000000000000000) (√((1 : ℝ) - (((99 / 200) : ℝ)^2))) := bsqrt sGlobal29_hz49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal29_hz51 : B (276577223611008791 / 1000000000000000000) (34572152951376099 / 125000000000000000) ((√((1 : ℝ) - (((99 / 200) : ℝ)^2))) / Real.pi) := bdiv sGlobal29_hz50 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal29_hz52 : B (164545906713926763 / 500000000000000000) (329091813427889941 / 1000000000000000000) (((99 / 200) : ℝ) * (kdot ((99 / 200)))) := bmul (bpoint ((99 / 200) : ℝ)) sGlobal29_hz47 (by norm_num) (by norm_num)

theorem sGlobal29_hz53 : B (605669037038862317 / 1000000000000000000) (605669037038898733 / 1000000000000000000) (((√((1 : ℝ) - (((99 / 200) : ℝ)^2))) / Real.pi) + (((99 / 200) : ℝ) * (kdot ((99 / 200))))) := badd sGlobal29_hz51 sGlobal29_hz52 (by norm_num) (by norm_num)

theorem sGlobal29_hz54 : B (605669037038862317 / 1000000000000000000) (605669037038898733 / 1000000000000000000) (kappa ((99 / 200))) := by rw [kappa_eq]; exact sGlobal29_hz53

theorem sGlobal29_hz55 {c : ℝ} (hc : B (49 / 100) (99 / 200) c) : B (602349451572852003 / 1000000000000000000) (605669037038898733 / 1000000000000000000) (kappa c) := bkappa (sGlobal29_hz38 hc) (by norm_num) (by norm_num) sGlobal29_hz46.1 sGlobal29_hz54.2

theorem sGlobal29_hz56 : B 24450 24450 ((2 : ℝ) * (12225 : ℝ)) := bmul (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal29_hz57 {c : ℝ} (hc : B (49 / 100) (99 / 200) c) : B (394330962961101267 / 1000000000000000000) (397650548427147997 / 1000000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (sGlobal29_hz55 hc) (by norm_num) (by norm_num)

theorem sGlobal29_hz58 {c : ℝ} (hc : B (49 / 100) (99 / 200) c) : B (192827840887978519563 / 20000000000000000) (194451118180875370533 / 20000000000000000) (((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) := bmul sGlobal29_hz56 (sGlobal29_hz57 hc) (by norm_num) (by norm_num)

theorem sGlobal29_hz59 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (4 : ℝ)) sGlobal29_hz10 (by norm_num) (by norm_num)

theorem sGlobal29_hz60 {c : ℝ} (hc : B (49 / 100) (99 / 200) c) : B (964139139000219796179 / 100000000000000000) (4861277627323520255147 / 500000000000000000) ((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bsub (sGlobal29_hz58 hc) sGlobal29_hz59 (by norm_num) (by norm_num)

theorem sGlobal29_hz61 {c : ℝ} (hc : B (49 / 100) (99 / 200) c) : B (12273823384291642281 / 125000000000000000) (98603018486489755687 / 1000000000000000000) (√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) := bsqrt (sGlobal29_hz60 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal29_hz62 : B (30670756373515103 / 125000000000000000) (122683025494060423 / 500000000000000000) ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal29_hz7 (by norm_num) (by norm_num)

theorem sGlobal29_hz63 {c : ℝ} (hc : B (49 / 100) (99 / 200) c) : B (48972610511672508701 / 500000000000000000) (98357652435501634863 / 1000000000000000000) ((√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) - ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))))) := bsub (sGlobal29_hz61 hc) sGlobal29_hz62 (by norm_num) (by norm_num)

theorem sGlobal29_hz64 {c : ℝ} (hc : B (49 / 100) (99 / 200) c) : B (48972610511672508701 / 500000000000000000) (98357652435501634863 / 1000000000000000000) (s3dm 12225 46 c) := by
    convert (sGlobal29_hz63 hc) using 1 <;>
      norm_num [s3dm, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal29_hz65 : B (6126072185528622723889 / 500000000000000000) (2450428874211449090087 / 200000000000000000) ((s3ap 12225 46)^2) := bsq sGlobal29_hz9 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal29_hz66 : B (6126072185528622723889 / 250000000000000000) (2450428874211449090087 / 100000000000000000) ((2 : ℝ) * ((s3ap 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal29_hz65 (by norm_num) (by norm_num)

theorem sGlobal29_hz67 {c : ℝ} (hc : B (49 / 100) (99 / 200) c) : B (29978957254099708681 / 3125000000000000) (4837113896311470342117 / 500000000000000000) ((s3dm 12225 46 c)^2) := bsq (sGlobal29_hz64 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal29_hz68 {c : ℝ} (hc : B (49 / 100) (99 / 200) c) : B (7415030474745775105661 / 500000000000000000) (298220448416051682459 / 20000000000000000) (((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) := bsub sGlobal29_hz66 (sGlobal29_hz67 hc) (by norm_num) (by norm_num)

theorem sGlobal29_hz69 : B (1524735695971823534271 / 125000000000000000) (609894278388729413841 / 50000000000000000) ((s3am 12225 46)^2) := bsq sGlobal29_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal29_hz70 : B (1524735695971823534271 / 62500000000000000) (609894278388729413841 / 25000000000000000) ((2 : ℝ) * ((s3am 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal29_hz69 (by norm_num) (by norm_num)

theorem sGlobal29_hz71 {c : ℝ} (hc : B (49 / 100) (99 / 200) c) : B (151973684978965399 / 250000000000000000) (611213408174437691 / 1000000000000000000) ((((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) / ((2 : ℝ) * ((s3am 12225 46)^2))) := bdiv (sGlobal29_hz68 hc) sGlobal29_hz70 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal29_hz72 {c : ℝ} (hc : B (49 / 100) (99 / 200) c) : B (151973684978965399 / 250000000000000000) (611213408174437691 / 1000000000000000000) (s3c1 12225 46 c) := by
    convert (sGlobal29_hz71 hc) using 1 <;>
      norm_num [s3c1] <;> ring

theorem sGlobal29_hz73 {c : ℝ} (hc : B (49 / 100) (99 / 200) c) : B (331501615486170743 / 500000000000000000) (83103993289871197 / 125000000000000000) (kdot c) := bkdot (sGlobal29_hz38 hc) sGlobal29_hz39.1 sGlobal29_hz47.2

theorem sGlobal29_hz74 : B (353992872584803897 / 500000000000000000) (353992872584803911 / 500000000000000000) (kdot ((151973684978965399 / 250000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (493824379795506363 / 1000000000000000000)) (a := (458694918859328973 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (246912189897753181 / 500000000000000000)) (a := (458694918859328931 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal29_hz75 : B (17732957233587939 / 25000000000000000) (709318289343517581 / 1000000000000000000) (kdot ((611213408174437691 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (245611733385429921 / 500000000000000000)) (a := (456601763365659573 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (491223466770859841 / 1000000000000000000)) (a := (456601763365659541 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal29_hz76 {c : ℝ} (hc : B (49 / 100) (99 / 200) c) : B (353992872584803897 / 500000000000000000) (709318289343517581 / 1000000000000000000) (kdot (s3c1 12225 46 c)) := bkdot (sGlobal29_hz72 hc) sGlobal29_hz74.1 sGlobal29_hz75.2

theorem sGlobal29_hz77 {c : ℝ} (hc : B (49 / 100) (99 / 200) c) : B (2401 / 10000) (9801 / 40000) (c^2) := bsq (sGlobal29_hz38 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal29_hz78 {c : ℝ} (hc : B (49 / 100) (99 / 200) c) : B (30199 / 40000) (7599 / 10000) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (sGlobal29_hz77 hc) (by norm_num) (by norm_num)

theorem sGlobal29_hz79 {c : ℝ} (hc : B (49 / 100) (99 / 200) c) : B (434446486923303363 / 500000000000000000) (871722432887900391 / 1000000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (sGlobal29_hz78 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal29_hz80 : B (39119999999999765769 / 1600000000000000) (3912000000000000489 / 160000000000000) ((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (149450625 : ℝ)) sGlobal29_hz10 (by norm_num) (by norm_num)

theorem sGlobal29_hz81 {c : ℝ} (hc : B (49 / 100) (99 / 200) c) : B (576078849029466469 / 1000000000000000000) (72443615213346269 / 125000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (sGlobal29_hz79 hc) (sGlobal29_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal29_hz82 {c : ℝ} (hc : B (49 / 100) (99 / 200) c) : B (7042563929385185416173 / 500000000000000000) (14169971135730531987647 / 1000000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) := bmul sGlobal29_hz80 (sGlobal29_hz81 hc) (by norm_num) (by norm_num)

theorem sGlobal29_hz83 {c : ℝ} (hc : B (49 / 100) (99 / 200) c) : B (7042563929385185416173 / 1000000000000000000) (221405798995789562307 / 31250000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) / (2 : ℝ)) := bdiv (sGlobal29_hz82 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal29_hz84 {c : ℝ} (hc : B (49 / 100) (99 / 200) c) : B (7042563929385185416173 / 1000000000000000000) (221405798995789562307 / 31250000000000000) (s3Cpa 12225 c) := by
    convert (sGlobal29_hz83 hc) using 1 <;>
      norm_num [s3Cpa, mA] <;> ring

theorem sGlobal29_hz85 {c : ℝ} (hc : B (49 / 100) (99 / 200) c) : B (276577223611008791 / 1000000000000000000) (69369467099101169 / 250000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (sGlobal29_hz79 hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal29_hz86 {c : ℝ} (hc : B (49 / 100) (99 / 200) c) : B (10152236974263979 / 31250000000000000) (329091813427889941 / 1000000000000000000) (c * (kdot c)) := bmul (sGlobal29_hz38 hc) (sGlobal29_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal29_hz87 {c : ℝ} (hc : B (49 / 100) (99 / 200) c) : B (-1050291796337623 / 20000000000000000) (-11848428695010663 / 250000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (sGlobal29_hz85 hc) (sGlobal29_hz86 hc) (by norm_num) (by norm_num)

theorem sGlobal29_hz88 {c : ℝ} (hc : B (49 / 100) (99 / 200) c) : B (-641990860511372138999 / 500000000000000000) (-579388163186017951613 / 500000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) := bmul sGlobal29_hz80 (sGlobal29_hz87 hc) (by norm_num) (by norm_num)

theorem sGlobal29_hz89 {c : ℝ} (hc : B (49 / 100) (99 / 200) c) : B (-641990860511372138999 / 1000000000000000000) (-579388163186017951613 / 1000000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) / (2 : ℝ)) := bdiv (sGlobal29_hz88 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal29_hz90 {c : ℝ} (hc : B (49 / 100) (99 / 200) c) : B (-641990860511372138999 / 1000000000000000000) (-579388163186017951613 / 1000000000000000000) (s3Cpp 12225 c) := by
    convert (sGlobal29_hz89 hc) using 1 <;>
      norm_num [s3Cpp, mA] <;> ring

theorem sGlobal29_hz91 {c : ℝ} (hc : B (49 / 100) (99 / 200) c) : B (3578854519659461562287 / 500000000000000000) (144002613555980088121 / 20000000000000000) ((s3Cpa 12225 c) + (s3r1 12225 46)) := badd (sGlobal29_hz84 hc) sGlobal29_hz33 (by norm_num) (by norm_num)

theorem sGlobal29_hz92 {c : ℝ} (hc : B (49 / 100) (99 / 200) c) : B (12961693827531347783 / 200000000000000000) (65192569892954663327 / 1000000000000000000) (((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) := bdiv (sGlobal29_hz91 hc) sGlobal29_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal29_hz93 {c : ℝ} (hc : B (49 / 100) (99 / 200) c) : B (64931152163150799327 / 1000000000000000000) (52252202334758979 / 800000000000000) ((((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) + (s3e0 12225 46)) := badd (sGlobal29_hz92 hc) sGlobal29_hz16 (by norm_num) (by norm_num)

theorem sGlobal29_hz94 {c : ℝ} (hc : B (49 / 100) (99 / 200) c) : B (64931152163150799327 / 1000000000000000000) (52252202334758979 / 800000000000000) (s3Lam 12225 46 c) := by
    convert (sGlobal29_hz93 hc) using 1 <;>
      norm_num [s3Lam] <;> ring

theorem sGlobal29_hz95 {c : ℝ} (hc : B (49 / 100) (99 / 200) c) : B (-565227453888880333399 / 1000000000000000000) (-100524951312705135359 / 200000000000000000) ((s3Cpp 12225 c) + (s3rpp 12225 46)) := badd (sGlobal29_hz90 hc) sGlobal29_hz37 (by norm_num) (by norm_num)

theorem sGlobal29_hz96 {c : ℝ} (hc : B (49 / 100) (99 / 200) c) : B (-12528942833826642559 / 31250000000000000) (-251312378281762838397 / 1000000000000000000) (if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) := bweaken (bfirst (sGlobal29_hz95 hc) (sGlobal29_hz76 hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem sGlobal29_hz97 {c : ℝ} (hc : B (49 / 100) (99 / 200) c) : B (527006815154280340833 / 125000000000000000) (266630141487557782823 / 62500000000000000) ((s3Lam 12225 46 c)^2) := bsq (sGlobal29_hz94 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal29_hz98 {c : ℝ} (hc : B (49 / 100) (99 / 200) c) : B (369536014817373013 / 1000000000000000000) (5837216098940809 / 15625000000000000) ((s3c1 12225 46 c)^2) := bsq (sGlobal29_hz72 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal29_hz99 {c : ℝ} (hc : B (49 / 100) (99 / 200) c) : B (9787783901059191 / 15625000000000000) (630463985182626987 / 1000000000000000000) ((1 : ℝ) - ((s3c1 12225 46 c)^2)) := bsub (bpoint (1 : ℝ)) (sGlobal29_hz98 hc) (by norm_num) (by norm_num)

theorem sGlobal29_hz100 {c : ℝ} (hc : B (49 / 100) (99 / 200) c) : B (791465836071139727 / 1000000000000000000) (794017622715407361 / 1000000000000000000) (√((1 : ℝ) - ((s3c1 12225 46 c)^2))) := bsqrt (sGlobal29_hz99 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal29_hz101 {c : ℝ} (hc : B (49 / 100) (99 / 200) c) : B (49729265123367923 / 20000000000000000) (2494479930343555901 / 1000000000000000000) (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))) := bmul pi_mem (sGlobal29_hz100 hc) (by norm_num) (by norm_num)

theorem sGlobal29_hz102 {c : ℝ} (hc : B (49 / 100) (99 / 200) c) : B (1690153714988430652269 / 1000000000000000000) (857861513380031901223 / 500000000000000000) (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2))))) := bdiv (sGlobal29_hz97 hc) (sGlobal29_hz101 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal29_hz103 {c : ℝ} (hc : B (49 / 100) (99 / 200) c) : B (1289227544305978090381 / 1000000000000000000) (1464410648478300964049 / 1000000000000000000) ((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) := badd (sGlobal29_hz96 hc) (sGlobal29_hz102 hc) (by norm_num) (by norm_num)

theorem sGlobal29_hz104 : B (3762781186094069 / 250000000000000000) (376278118609407 / 25000000000000000) ((s3e0 12225 46)^2) := bsq sGlobal29_hz16 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal29_hz105 {c : ℝ} (hc : B (49 / 100) (99 / 200) c) : B (1289242595430722466657 / 1000000000000000000) (1464425699603045340329 / 1000000000000000000) (((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) := badd (sGlobal29_hz103 hc) sGlobal29_hz104 (by norm_num) (by norm_num)

theorem sGlobal29_hz106 {c : ℝ} (hc : B (49 / 100) (99 / 200) c) : B (331934917220492434197 / 250000000000000000) (300584554611433922069 / 200000000000000000) ((((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) + (s3rs 12225 46 maskSlack)) := badd (sGlobal29_hz105 hc) sGlobal29_hz29 (by norm_num) (by norm_num)

theorem sGlobal29_hz107 {c : ℝ} (hc : B (49 / 100) (99 / 200) c) : B (331934917220492434197 / 250000000000000000) (300584554611433922069 / 200000000000000000) (s3U 12225 46 maskSlack c) := by
    convert (sGlobal29_hz106 hc) using 1 <;>
      norm_num [s3U] <;> ring

theorem sGlobal29_hz108 {c : ℝ} (hc : B (49 / 100) (99 / 200) c) : B (-718754267133864413817 / 1000000000000000000) (-656151569808509757213 / 1000000000000000000) ((s3Cpp 12225 c) - (s3rpp 12225 46)) := bsub (sGlobal29_hz90 hc) sGlobal29_hz37 (by norm_num) (by norm_num)

theorem sGlobal29_hz109 {c : ℝ} (hc : B (49 / 100) (99 / 200) c) : B (-718754267133864413817 / 1000000000000000000) (-656151569808509757213 / 1000000000000000000) (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ)) := bweaken (bmin (sGlobal29_hz108 hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem sGlobal29_hz110 {c : ℝ} (hc : B (49 / 100) (99 / 200) c) : B (-254912773610873183573 / 500000000000000000) (-92909191619017141617 / 200000000000000000) ((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) := bmul (sGlobal29_hz76 hc) (sGlobal29_hz109 hc) (by norm_num) (by norm_num)

theorem sGlobal29_hz111 {c : ℝ} (hc : B (49 / 100) (99 / 200) c) : B (-254920299173245371713 / 500000000000000000) (-464561009219830084361 / 1000000000000000000) (((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) := bsub (sGlobal29_hz110 hc) sGlobal29_hz104 (by norm_num) (by norm_num)

theorem sGlobal29_hz112 {c : ℝ} (hc : B (49 / 100) (99 / 200) c) : B (-274168835900307506721 / 500000000000000000) (-125764520667769338623 / 250000000000000000) ((((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) - (s3rs 12225 46 maskSlack)) := bsub (sGlobal29_hz111 hc) sGlobal29_hz29 (by norm_num) (by norm_num)

theorem sGlobal29_hz113 {c : ℝ} (hc : B (49 / 100) (99 / 200) c) : B (-274168835900307506721 / 500000000000000000) (-125764520667769338623 / 250000000000000000) (s3L 12225 46 maskSlack c) := by
    convert (sGlobal29_hz112 hc) using 1 <;>
      norm_num [s3L] <;> ring

theorem sGlobal29_hz114 {c : ℝ} (hc : B (49 / 100) (99 / 200) c) : B 0 (300584554611433922069 / 200000000000000000) |(s3U 12225 46 maskSlack c)| := bweaken (babs (sGlobal29_hz107 hc)) (by norm_num) (by norm_num)

theorem sGlobal29_hz115 {c : ℝ} (hc : B (49 / 100) (99 / 200) c) : B 0 (274168835900307506721 / 500000000000000000) |(s3L 12225 46 maskSlack c)| := bweaken (babs (sGlobal29_hz113 hc)) (by norm_num) (by norm_num)

theorem sGlobal29_hz116 {c : ℝ} (hc : B (49 / 100) (99 / 200) c) : B 0 (300584554611433922069 / 200000000000000000) (max |(s3U 12225 46 maskSlack c)| |(s3L 12225 46 maskSlack c)|) := bweaken (bmax (sGlobal29_hz114 hc) (sGlobal29_hz115 hc)) (by norm_num) (by norm_num)

theorem sGlobal29_hz117 {c : ℝ} (hc : B (49 / 100) (99 / 200) c) : B 0 (300584554611433922069 / 200000000000000000) (s3nks 12225 46 maskSlack c) := by
    convert (sGlobal29_hz116 hc) using 1 <;>
      norm_num [s3nks] <;> ring

theorem sGlobal29 {c : ℝ} (hc : B (49 / 100) (99 / 200) c) :
    0 < s3am 12225 46 ∧ 0 ≤ s3dm 12225 46 c ∧
    s3dm 12225 46 c ^ 2 ≤ 2 * s3ap 12225 46 ^ 2 ∧ s3c1 12225 46 c < 1 ∧
    0 ≤ s3Cpa 12225 c - s3r1 12225 46 ∧
    s3e0 12225 46 ≤ (s3Cpa 12225 c - s3r1 12225 46) / s3ap 12225 46 ∧
    s3nks 12225 46 maskSlack c ≤ 12225 * (122939 / 1000000) := by

  refine ⟨lt_of_lt_of_le (by norm_num) sGlobal29_hz14.1,
    le_trans (by norm_num) (sGlobal29_hz64 hc).1, ?_,
    lt_of_le_of_lt (sGlobal29_hz72 hc).2 (by norm_num), ?_, ?_,
    le_trans (sGlobal29_hz117 hc).2 (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (sGlobal29_hz64 hc).1) (sGlobal29_hz64 hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) sGlobal29_hz9.1 2
    nlinarith only [h1, h2]
  · linarith only [(sGlobal29_hz84 hc).1, sGlobal29_hz33.2]
  · have hap : 0 < s3ap 12225 46 := lt_of_lt_of_le (by norm_num) sGlobal29_hz9.1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul sGlobal29_hz16.2 sGlobal29_hz9.2 (le_trans (by norm_num) sGlobal29_hz9.1) (by norm_num)
    linarith only [h, (sGlobal29_hz84 hc).1, sGlobal29_hz33.2]

end BstLean.Part255
