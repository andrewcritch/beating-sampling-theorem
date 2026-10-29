import BstLean.Part255SGlobal9
import BstLean.Part255Numeric10
namespace BstLean.Part255
open Real BstLean.Part130 BstLean.Part182 BstLean.Part197 BstLean.Part246
theorem sGlobal13_hz0 : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal13_hz1 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) ((√(23 : ℝ)) / (12225 : ℝ)) := bdiv sGlobal13_hz0 (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal13_hz2 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) maskSlack := by
    convert sGlobal13_hz1 using 1 <;>
      norm_num [maskSlack] <;> ring

theorem sGlobal13_hz3 : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal13_hz4 : B (6395294793910793 / 500000000000000000) (12790589587821587 / 1000000000000000000) (√((2 / 12225) : ℝ)) := bsqrt (bpoint ((2 / 12225) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal13_hz5 : B (7230130686979 / 62500000000000000) (23136418198333 / 200000000000000000) (√((2 / 149450625) : ℝ)) := bsqrt (bpoint ((2 / 149450625) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal13_hz6 : B (2211334438749598093 / 20000000000000000) (110566721937479904651 / 1000000000000000000) (√(12225 : ℝ)) := bsqrt (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal13_hz7 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))) := bmul sGlobal13_hz3 sGlobal13_hz4 (by norm_num) (by norm_num)

theorem sGlobal13_hz8 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) ((√(12225 : ℝ)) + ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := badd sGlobal13_hz6 sGlobal13_hz7 (by norm_num) (by norm_num)

theorem sGlobal13_hz9 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) (s3ap 12225 46) := by
    convert sGlobal13_hz8 using 1 <;>
      norm_num [s3ap, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal13_hz10 : B (163599182004089 / 1000000000000000000) (16359918200409 / 100000000000000000) ((2 : ℝ) / (12225 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal13_hz11 : B (1222499983640081799591 / 100000000000000000) (12224999836400817995911 / 1000000000000000000) ((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ))) := bsub (bpoint (12225 : ℝ)) sGlobal13_hz10 (by norm_num) (by norm_num)

theorem sGlobal13_hz12 : B (110566721197658827907 / 1000000000000000000) (27641680299414706977 / 250000000000000000) (√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) := bsqrt sGlobal13_hz11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal13_hz13 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) ((√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) - ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bsub sGlobal13_hz12 sGlobal13_hz7 (by norm_num) (by norm_num)

theorem sGlobal13_hz14 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) (s3am 12225 46) := by
    convert sGlobal13_hz13 using 1 <;>
      norm_num [s3am, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal13_hz15 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√((2 / 12225) : ℝ)) * (√(92 : ℝ))) := bmul sGlobal13_hz4 sGlobal13_hz3 (by norm_num) (by norm_num)

theorem sGlobal13_hz16 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) (s3e0 12225 46) := by
    convert sGlobal13_hz15 using 1 <;>
      norm_num [s3e0, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal13_hz17 : B (250196148528560847 / 500000000000000000) (100078459411424339 / 200000000000000000) (((1 / 2) : ℝ) + maskSlack) := badd (bpoint ((1 / 2) : ℝ)) sGlobal13_hz2 (by norm_num) (by norm_num)

theorem sGlobal13_hz18 : B (59827153232297998295487 / 800000000000000) (23930861292919199366019 / 320000000000000) ((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack)) := bmul (bpoint (149450625 : ℝ)) sGlobal13_hz17 (by norm_num) (by norm_num)

theorem sGlobal13_hz19 : B (1729554180017180009583 / 200000000000000000) (8647770900085900056557 / 1000000000000000000) (√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) := bsqrt sGlobal13_hz18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal13_hz20 : B (4328681281566262743499 / 500000000000000000) (8657362563132525495641 / 1000000000000000000) ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))) := badd sGlobal13_hz19 sGlobal13_hz3 (by norm_num) (by norm_num)

theorem sGlobal13_hz21 : B (110732771457999278473 / 1000000000000000000) (55366385728999643621 / 500000000000000000) ((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ)))) := bmul sGlobal13_hz4 sGlobal13_hz20 (by norm_num) (by norm_num)

theorem sGlobal13_hz22 : B (209099159 / 15625000000000000) (13382346177 / 1000000000000000000) ((2 : ℝ) / (149450625 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (149450625 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal13_hz23 : B (2452349334953899930479 / 200000000000000000) (12261746674769501594427 / 1000000000000000000) (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2) := bsq sGlobal13_hz21 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal13_hz24 : B (82045469362091 / 500000000000000000) (32818187747289 / 200000000000000000) (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2)) := bmul sGlobal13_hz22 sGlobal13_hz23 (by norm_num) (by norm_num)

theorem sGlobal13_hz25 : B (82045469362091 / 250000000000000000) (32818187747289 / 100000000000000000) ((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) := bmul (bpoint (2 : ℝ)) sGlobal13_hz24 (by norm_num) (by norm_num)

theorem sGlobal13_hz26 : B (117258080744995992792057 / 1000000000000000000) (58629040372497996396029 / 500000000000000000) (√(13749457500 : ℝ)) := bsqrt (bpoint (13749457500 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal13_hz27 : B (117304080744995992792057 / 1000000000000000000) (58652040372497996396029 / 500000000000000000) ((√(13749457500 : ℝ)) + (46 : ℝ)) := badd sGlobal13_hz26 (bpoint (46 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal13_hz28 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal13_hz25 sGlobal13_hz27 (by norm_num) (by norm_num)

theorem sGlobal13_hz29 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (s3rs 12225 46 maskSlack) := by
    convert sGlobal13_hz28 using 1 <;>
      norm_num [s3rs, s3pp, s3K, mA, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal13_hz30 : B (490797546012267 / 1000000000000000000) (49079754601227 / 100000000000000000) ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (3 : ℝ)) sGlobal13_hz10 (by norm_num) (by norm_num)

theorem sGlobal13_hz31 : B (490797546012267 / 500000000000000000) (49079754601227 / 50000000000000000) ((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal13_hz30 (by norm_num) (by norm_num)

theorem sGlobal13_hz32 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal13_hz31 sGlobal13_hz27 (by norm_num) (by norm_num)

theorem sGlobal13_hz33 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (s3r1 12225 46) := by
    convert sGlobal13_hz32 using 1 <;>
      norm_num [s3r1, mA] <;> ring

theorem sGlobal13_hz34 : B (163599182004089 / 500000000000000000) (16359918200409 / 50000000000000000) ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (2 : ℝ)) sGlobal13_hz10 (by norm_num) (by norm_num)

theorem sGlobal13_hz35 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal13_hz34 (by norm_num) (by norm_num)

theorem sGlobal13_hz36 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal13_hz35 sGlobal13_hz27 (by norm_num) (by norm_num)

theorem sGlobal13_hz37 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (s3rpp 12225 46) := by
    convert sGlobal13_hz36 using 1 <;>
      norm_num [s3rpp, mA] <;> ring

theorem sGlobal13_hz38 {c : ℝ} (hc : B (41 / 100) (83 / 200) c) : B (41 / 100) (83 / 200) c := hc

theorem sGlobal13_hz39 : B (12689426089010923 / 20000000000000000) (317235652232250419 / 500000000000000000) (kdot ((41 / 100))) := by
    constructor
    · apply bkdot_lower (q := (646869164755947181 / 1000000000000000000)) (a := (287085566153606091 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (32343458237797359 / 50000000000000000)) (a := (143542783071323053 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal13_hz40 : B (1681 / 10000) (1681 / 10000) (((41 / 100) : ℝ)^2) := bsq (bpoint ((41 / 100) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal13_hz41 : B (8319 / 10000) (8319 / 10000) ((1 : ℝ) - (((41 / 100) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal13_hz40 (by norm_num) (by norm_num)

theorem sGlobal13_hz42 : B (228021380576471381 / 250000000000000000) (36483420892235421 / 40000000000000000) (√((1 : ℝ) - (((41 / 100) : ℝ)^2))) := bsqrt sGlobal13_hz41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal13_hz43 : B (36290729849383711 / 125000000000000000) (29032583879506969 / 100000000000000000) ((√((1 : ℝ) - (((41 / 100) : ℝ)^2))) / Real.pi) := bdiv sGlobal13_hz42 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal13_hz44 : B (260133234824723921 / 1000000000000000000) (8129163588451417 / 31250000000000000) (((41 / 100) : ℝ) * (kdot ((41 / 100)))) := bmul (bpoint ((41 / 100) : ℝ)) sGlobal13_hz39 (by norm_num) (by norm_num)

theorem sGlobal13_hz45 : B (550459073619793609 / 1000000000000000000) (275229536812757517 / 500000000000000000) (((√((1 : ℝ) - (((41 / 100) : ℝ)^2))) / Real.pi) + (((41 / 100) : ℝ) * (kdot ((41 / 100))))) := badd sGlobal13_hz43 sGlobal13_hz44 (by norm_num) (by norm_num)

theorem sGlobal13_hz46 : B (550459073619793609 / 1000000000000000000) (275229536812757517 / 500000000000000000) (kappa ((41 / 100))) := by rw [kappa_eq]; exact sGlobal13_hz45

theorem sGlobal13_hz47 : B (318109212453096469 / 500000000000000000) (25448736996663207 / 40000000000000000) (kdot ((83 / 200))) := by
    constructor
    · apply bkdot_lower (q := (321491664681005311 / 500000000000000000)) (a := (285713380956506991 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (642983329362010621 / 1000000000000000000)) (a := (571426761896697749 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal13_hz48 : B (6889 / 40000) (6889 / 40000) (((83 / 200) : ℝ)^2) := bsq (bpoint ((83 / 200) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal13_hz49 : B (33111 / 40000) (33111 / 40000) ((1 : ℝ) - (((83 / 200) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal13_hz48 (by norm_num) (by norm_num)

theorem sGlobal13_hz50 : B (909821411047245029 / 1000000000000000000) (90982141104724503 / 100000000000000000) (√((1 : ℝ) - (((83 / 200) : ℝ)^2))) := bsqrt sGlobal13_hz49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal13_hz51 : B (289605149798024393 / 1000000000000000000) (57921029959604879 / 200000000000000000) ((√((1 : ℝ) - (((83 / 200) : ℝ)^2))) / Real.pi) := bdiv sGlobal13_hz50 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal13_hz52 : B (264030646336070069 / 1000000000000000000) (264030646340380773 / 1000000000000000000) (((83 / 200) : ℝ) * (kdot ((83 / 200)))) := bmul (bpoint ((83 / 200) : ℝ)) sGlobal13_hz47 (by norm_num) (by norm_num)

theorem sGlobal13_hz53 : B (276817898067047231 / 500000000000000000) (34602237258650323 / 62500000000000000) (((√((1 : ℝ) - (((83 / 200) : ℝ)^2))) / Real.pi) + (((83 / 200) : ℝ) * (kdot ((83 / 200))))) := badd sGlobal13_hz51 sGlobal13_hz52 (by norm_num) (by norm_num)

theorem sGlobal13_hz54 : B (276817898067047231 / 500000000000000000) (34602237258650323 / 62500000000000000) (kappa ((83 / 200))) := by rw [kappa_eq]; exact sGlobal13_hz53

theorem sGlobal13_hz55 {c : ℝ} (hc : B (41 / 100) (83 / 200) c) : B (550459073619793609 / 1000000000000000000) (34602237258650323 / 62500000000000000) (kappa c) := bkappa (sGlobal13_hz38 hc) (by norm_num) (by norm_num) sGlobal13_hz46.1 sGlobal13_hz54.2

theorem sGlobal13_hz56 : B 24450 24450 ((2 : ℝ) * (12225 : ℝ)) := bmul (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal13_hz57 {c : ℝ} (hc : B (41 / 100) (83 / 200) c) : B (27897762741349677 / 62500000000000000) (449540926380206391 / 1000000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (sGlobal13_hz55 hc) (by norm_num) (by norm_num)

theorem sGlobal13_hz58 {c : ℝ} (hc : B (41 / 100) (83 / 200) c) : B (13642005980519992053 / 1250000000000000) (219825512999920925199 / 20000000000000000) (((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) := bmul sGlobal13_hz56 (sGlobal13_hz57 hc) (by norm_num) (by norm_num)

theorem sGlobal13_hz59 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (4 : ℝ)) sGlobal13_hz10 (by norm_num) (by norm_num)

theorem sGlobal13_hz60 {c : ℝ} (hc : B (41 / 100) (83 / 200) c) : B (272840103250481640651 / 25000000000000000) (5495637497799659121797 / 500000000000000000) ((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bsub (sGlobal13_hz58 hc) sGlobal13_hz59 (by norm_num) (by norm_num)

theorem sGlobal13_hz61 {c : ℝ} (hc : B (41 / 100) (83 / 200) c) : B (52234098369789215751 / 500000000000000000) (52419640869618990179 / 500000000000000000) (√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) := bsqrt (sGlobal13_hz60 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal13_hz62 : B (30670756373515103 / 125000000000000000) (122683025494060423 / 500000000000000000) ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal13_hz7 (by norm_num) (by norm_num)

theorem sGlobal13_hz63 {c : ℝ} (hc : B (41 / 100) (83 / 200) c) : B (407120432377305901 / 3906250000000000) (52296957844124929767 / 500000000000000000) ((√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) - ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))))) := bsub (sGlobal13_hz61 hc) sGlobal13_hz62 (by norm_num) (by norm_num)

theorem sGlobal13_hz64 {c : ℝ} (hc : B (41 / 100) (83 / 200) c) : B (407120432377305901 / 3906250000000000) (52296957844124929767 / 500000000000000000) (s3dm 12225 46 c) := by
    convert (sGlobal13_hz63 hc) using 1 <;>
      norm_num [s3dm, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal13_hz65 : B (6126072185528622723889 / 500000000000000000) (2450428874211449090087 / 200000000000000000) ((s3ap 12225 46)^2) := bsq sGlobal13_hz9 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal13_hz66 : B (6126072185528622723889 / 250000000000000000) (2450428874211449090087 / 100000000000000000) ((2 : ℝ) * ((s3ap 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal13_hz65 (by norm_num) (by norm_num)

theorem sGlobal13_hz67 {c : ℝ} (hc : B (41 / 100) (83 / 200) c) : B (10862398436742562248451 / 1000000000000000000) (10939887199000720087411 / 1000000000000000000) ((s3dm 12225 46 c)^2) := bsq (sGlobal13_hz64 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal13_hz68 {c : ℝ} (hc : B (41 / 100) (83 / 200) c) : B (2712880308622754161629 / 200000000000000000) (13641890305371928652419 / 1000000000000000000) (((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) := bsub sGlobal13_hz66 (sGlobal13_hz67 hc) (by norm_num) (by norm_num)

theorem sGlobal13_hz69 : B (1524735695971823534271 / 125000000000000000) (609894278388729413841 / 50000000000000000) ((s3am 12225 46)^2) := bsq sGlobal13_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal13_hz70 : B (1524735695971823534271 / 62500000000000000) (609894278388729413841 / 25000000000000000) ((2 : ℝ) * ((s3am 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal13_hz69 (by norm_num) (by norm_num)

theorem sGlobal13_hz71 {c : ℝ} (hc : B (41 / 100) (83 / 200) c) : B (111202892236908343 / 200000000000000000) (279595390315273881 / 500000000000000000) ((((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) / ((2 : ℝ) * ((s3am 12225 46)^2))) := bdiv (sGlobal13_hz68 hc) sGlobal13_hz70 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal13_hz72 {c : ℝ} (hc : B (41 / 100) (83 / 200) c) : B (111202892236908343 / 200000000000000000) (279595390315273881 / 500000000000000000) (s3c1 12225 46 c) := by
    convert (sGlobal13_hz71 hc) using 1 <;>
      norm_num [s3c1] <;> ring

theorem sGlobal13_hz73 {c : ℝ} (hc : B (41 / 100) (83 / 200) c) : B (12689426089010923 / 20000000000000000) (25448736996663207 / 40000000000000000) (kdot c) := bkdot (sGlobal13_hz38 hc) sGlobal13_hz39.1 sGlobal13_hz47.2

theorem sGlobal13_hz74 : B (343835046687002051 / 500000000000000000) (687670093374005281 / 1000000000000000000) (kdot ((111202892236908343 / 200000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (13354191711505913 / 25000000000000000)) (a := (490606670076307399 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (534167668460236519 / 1000000000000000000)) (a := (122651667519076387 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal13_hz75 : B (172222018455691889 / 250000000000000000) (344444036911384249 / 500000000000000000) (kdot ((279595390315273881 / 500000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (3323194212038681 / 6250000000000000)) (a := (97738694172256353 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (531711073926188959 / 1000000000000000000)) (a := (488693470861280287 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal13_hz76 {c : ℝ} (hc : B (41 / 100) (83 / 200) c) : B (343835046687002051 / 500000000000000000) (344444036911384249 / 500000000000000000) (kdot (s3c1 12225 46 c)) := bkdot (sGlobal13_hz72 hc) sGlobal13_hz74.1 sGlobal13_hz75.2

theorem sGlobal13_hz77 {c : ℝ} (hc : B (41 / 100) (83 / 200) c) : B (1681 / 10000) (6889 / 40000) (c^2) := bsq (sGlobal13_hz38 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal13_hz78 {c : ℝ} (hc : B (41 / 100) (83 / 200) c) : B (33111 / 40000) (8319 / 10000) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (sGlobal13_hz77 hc) (by norm_num) (by norm_num)

theorem sGlobal13_hz79 {c : ℝ} (hc : B (41 / 100) (83 / 200) c) : B (909821411047245029 / 1000000000000000000) (36483420892235421 / 40000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (sGlobal13_hz78 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal13_hz80 : B (39119999999999765769 / 1600000000000000) (3912000000000000489 / 160000000000000) ((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (149450625 : ℝ)) sGlobal13_hz10 (by norm_num) (by norm_num)

theorem sGlobal13_hz81 {c : ℝ} (hc : B (41 / 100) (83 / 200) c) : B (577255577484182093 / 1000000000000000000) (580285614390666843 / 1000000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (sGlobal13_hz79 hc) (sGlobal13_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal13_hz82 {c : ℝ} (hc : B (41 / 100) (83 / 200) c) : B (44105933967150523959 / 3125000000000000) (886748954490737880303 / 62500000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) := bmul sGlobal13_hz80 (sGlobal13_hz81 hc) (by norm_num) (by norm_num)

theorem sGlobal13_hz83 {c : ℝ} (hc : B (41 / 100) (83 / 200) c) : B (44105933967150523959 / 6250000000000000) (886748954490737880303 / 125000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) / (2 : ℝ)) := bdiv (sGlobal13_hz82 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal13_hz84 {c : ℝ} (hc : B (41 / 100) (83 / 200) c) : B (44105933967150523959 / 6250000000000000) (886748954490737880303 / 125000000000000000) (s3Cpa 12225 c) := by
    convert (sGlobal13_hz83 hc) using 1 <;>
      norm_num [s3Cpa, mA] <;> ring

theorem sGlobal13_hz85 {c : ℝ} (hc : B (41 / 100) (83 / 200) c) : B (289605149798024393 / 1000000000000000000) (29032583879506969 / 100000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (sGlobal13_hz79 hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal13_hz86 {c : ℝ} (hc : B (41 / 100) (83 / 200) c) : B (260133234824723921 / 1000000000000000000) (264030646340380773 / 1000000000000000000) (c * (kdot c)) := bmul (sGlobal13_hz38 hc) (sGlobal13_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal13_hz87 {c : ℝ} (hc : B (41 / 100) (83 / 200) c) : B (1278725172882181 / 50000000000000000) (30192603970345769 / 1000000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (sGlobal13_hz85 hc) (sGlobal13_hz86 hc) (by norm_num) (by norm_num)

theorem sGlobal13_hz88 {c : ℝ} (hc : B (41 / 100) (83 / 200) c) : B (156324152384845691259 / 250000000000000000) (738209167074954144327 / 1000000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) := bmul sGlobal13_hz80 (sGlobal13_hz87 hc) (by norm_num) (by norm_num)

theorem sGlobal13_hz89 {c : ℝ} (hc : B (41 / 100) (83 / 200) c) : B (156324152384845691259 / 500000000000000000) (92276145884369268041 / 250000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) / (2 : ℝ)) := bdiv (sGlobal13_hz88 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal13_hz90 {c : ℝ} (hc : B (41 / 100) (83 / 200) c) : B (156324152384845691259 / 500000000000000000) (92276145884369268041 / 250000000000000000) (s3Cpp 12225 c) := by
    convert (sGlobal13_hz89 hc) using 1 <;>
      norm_num [s3Cpp, mA] <;> ring

theorem sGlobal13_hz91 {c : ℝ} (hc : B (41 / 100) (83 / 200) c) : B (7172094544677821541841 / 1000000000000000000) (144182734917192829093 / 20000000000000000) ((s3Cpa 12225 c) + (s3r1 12225 46)) := badd (sGlobal13_hz84 hc) sGlobal13_hz33 (by norm_num) (by norm_num)

theorem sGlobal13_hz92 {c : ℝ} (hc : B (41 / 100) (83 / 200) c) : B (16234680167836813871 / 250000000000000000) (2039816064647412991 / 31250000000000000) (((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) := bdiv (sGlobal13_hz91 hc) sGlobal13_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal13_hz93 {c : ℝ} (hc : B (41 / 100) (83 / 200) c) : B (8132675462105164487 / 125000000000000000) (13079359418842255227 / 200000000000000000) ((((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) + (s3e0 12225 46)) := badd (sGlobal13_hz92 hc) sGlobal13_hz16 (by norm_num) (by norm_num)

theorem sGlobal13_hz94 {c : ℝ} (hc : B (41 / 100) (83 / 200) c) : B (8132675462105164487 / 125000000000000000) (13079359418842255227 / 200000000000000000) (s3Lam 12225 46 c) := by
    convert (sGlobal13_hz93 hc) using 1 <;>
      norm_num [s3Lam] <;> ring

theorem sGlobal13_hz95 {c : ℝ} (hc : B (41 / 100) (83 / 200) c) : B (194705855696091594059 / 500000000000000000) (222933995079984673491 / 500000000000000000) ((s3Cpp 12225 c) + (s3rpp 12225 46)) := badd (sGlobal13_hz90 hc) sGlobal13_hz37 (by norm_num) (by norm_num)

theorem sGlobal13_hz96 {c : ℝ} (hc : B (41 / 100) (83 / 200) c) : B (194705855696091594059 / 1000000000000000000) (38394142615066297719 / 125000000000000000) (if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) := bweaken (bfirst (sGlobal13_hz95 hc) (sGlobal13_hz76 hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem sGlobal13_hz97 {c : ℝ} (hc : B (41 / 100) (83 / 200) c) : B (4232986251003356846707 / 1000000000000000000) (4276741070181440409899 / 1000000000000000000) ((s3Lam 12225 46 c)^2) := bsq (sGlobal13_hz94 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal13_hz98 {c : ℝ} (hc : B (41 / 100) (83 / 200) c) : B (61830416209267249 / 200000000000000000) (312694329142201391 / 1000000000000000000) ((s3c1 12225 46 c)^2) := bsq (sGlobal13_hz72 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal13_hz99 {c : ℝ} (hc : B (41 / 100) (83 / 200) c) : B (687305670857798609 / 1000000000000000000) (138169583790732751 / 200000000000000000) ((1 : ℝ) - ((s3c1 12225 46 c)^2)) := bsub (bpoint (1 : ℝ)) (sGlobal13_hz98 hc) (by norm_num) (by norm_num)

theorem sGlobal13_hz100 {c : ℝ} (hc : B (41 / 100) (83 / 200) c) : B (207259751106220363 / 250000000000000000) (415586308410678923 / 500000000000000000) (√((1 : ℝ) - ((s3c1 12225 46 c)^2))) := bsqrt (sGlobal13_hz99 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal13_hz101 {c : ℝ} (hc : B (41 / 100) (83 / 200) c) : B (2604502845840603659 / 1000000000000000000) (652801446717745503 / 250000000000000000) (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))) := bmul pi_mem (sGlobal13_hz100 hc) (by norm_num) (by norm_num)

theorem sGlobal13_hz102 {c : ℝ} (hc : B (41 / 100) (83 / 200) c) : B (1621084892001469035443 / 1000000000000000000) (410514148315426550179 / 250000000000000000) (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2))))) := bdiv (sGlobal13_hz97 hc) (sGlobal13_hz101 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal13_hz103 {c : ℝ} (hc : B (41 / 100) (83 / 200) c) : B (907895373848780314751 / 500000000000000000) (487302433545559145617 / 250000000000000000) ((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) := badd (sGlobal13_hz96 hc) (sGlobal13_hz102 hc) (by norm_num) (by norm_num)

theorem sGlobal13_hz104 : B (3762781186094069 / 250000000000000000) (376278118609407 / 25000000000000000) ((s3e0 12225 46)^2) := bsq sGlobal13_hz16 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal13_hz105 {c : ℝ} (hc : B (41 / 100) (83 / 200) c) : B (907902899411152502889 / 500000000000000000) (487306196326745239687 / 250000000000000000) (((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) := badd (sGlobal13_hz103 hc) sGlobal13_hz104 (by norm_num) (by norm_num)

theorem sGlobal13_hz106 {c : ℝ} (hc : B (41 / 100) (83 / 200) c) : B (1854302872273552275909 / 1000000000000000000) (496930464690276307191 / 250000000000000000) ((((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) + (s3rs 12225 46 maskSlack)) := badd (sGlobal13_hz105 hc) sGlobal13_hz29 (by norm_num) (by norm_num)

theorem sGlobal13_hz107 {c : ℝ} (hc : B (41 / 100) (83 / 200) c) : B (1854302872273552275909 / 1000000000000000000) (496930464690276307191 / 250000000000000000) (s3U 12225 46 maskSlack c) := by
    convert (sGlobal13_hz106 hc) using 1 <;>
      norm_num [s3U] <;> ring

theorem sGlobal13_hz108 {c : ℝ} (hc : B (41 / 100) (83 / 200) c) : B (2358848981471991077 / 10000000000000000) (73085294228746316641 / 250000000000000000) ((s3Cpp 12225 c) - (s3rpp 12225 46)) := bsub (sGlobal13_hz90 hc) sGlobal13_hz37 (by norm_num) (by norm_num)

theorem sGlobal13_hz109 {c : ℝ} (hc : B (41 / 100) (83 / 200) c) : B 0 0 (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ)) := bweaken (bmin (sGlobal13_hz108 hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem sGlobal13_hz110 {c : ℝ} (hc : B (41 / 100) (83 / 200) c) : B 0 0 ((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) := bmul (sGlobal13_hz76 hc) (sGlobal13_hz109 hc) (by norm_num) (by norm_num)

theorem sGlobal13_hz111 {c : ℝ} (hc : B (41 / 100) (83 / 200) c) : B (-376278118609407 / 25000000000000000) (-3762781186094069 / 250000000000000000) (((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) := bsub (sGlobal13_hz110 hc) sGlobal13_hz104 (by norm_num) (by norm_num)

theorem sGlobal13_hz112 {c : ℝ} (hc : B (41 / 100) (83 / 200) c) : B (-4814015572358580787 / 125000000000000000) (-38512124575991646407 / 1000000000000000000) ((((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) - (s3rs 12225 46 maskSlack)) := bsub (sGlobal13_hz111 hc) sGlobal13_hz29 (by norm_num) (by norm_num)

theorem sGlobal13_hz113 {c : ℝ} (hc : B (41 / 100) (83 / 200) c) : B (-4814015572358580787 / 125000000000000000) (-38512124575991646407 / 1000000000000000000) (s3L 12225 46 maskSlack c) := by
    convert (sGlobal13_hz112 hc) using 1 <;>
      norm_num [s3L] <;> ring

theorem sGlobal13_hz114 {c : ℝ} (hc : B (41 / 100) (83 / 200) c) : B 0 (496930464690276307191 / 250000000000000000) |(s3U 12225 46 maskSlack c)| := bweaken (babs (sGlobal13_hz107 hc)) (by norm_num) (by norm_num)

theorem sGlobal13_hz115 {c : ℝ} (hc : B (41 / 100) (83 / 200) c) : B 0 (4814015572358580787 / 125000000000000000) |(s3L 12225 46 maskSlack c)| := bweaken (babs (sGlobal13_hz113 hc)) (by norm_num) (by norm_num)

theorem sGlobal13_hz116 {c : ℝ} (hc : B (41 / 100) (83 / 200) c) : B 0 (496930464690276307191 / 250000000000000000) (max |(s3U 12225 46 maskSlack c)| |(s3L 12225 46 maskSlack c)|) := bweaken (bmax (sGlobal13_hz114 hc) (sGlobal13_hz115 hc)) (by norm_num) (by norm_num)

theorem sGlobal13_hz117 {c : ℝ} (hc : B (41 / 100) (83 / 200) c) : B 0 (496930464690276307191 / 250000000000000000) (s3nks 12225 46 maskSlack c) := by
    convert (sGlobal13_hz116 hc) using 1 <;>
      norm_num [s3nks] <;> ring

theorem sGlobal13 {c : ℝ} (hc : B (41 / 100) (83 / 200) c) :
    0 < s3am 12225 46 ∧ 0 ≤ s3dm 12225 46 c ∧
    s3dm 12225 46 c ^ 2 ≤ 2 * s3ap 12225 46 ^ 2 ∧ s3c1 12225 46 c < 1 ∧
    0 ≤ s3Cpa 12225 c - s3r1 12225 46 ∧
    s3e0 12225 46 ≤ (s3Cpa 12225 c - s3r1 12225 46) / s3ap 12225 46 ∧
    s3nks 12225 46 maskSlack c ≤ 12225 * (32519 / 200000) := by

  refine ⟨lt_of_lt_of_le (by norm_num) sGlobal13_hz14.1,
    le_trans (by norm_num) (sGlobal13_hz64 hc).1, ?_,
    lt_of_le_of_lt (sGlobal13_hz72 hc).2 (by norm_num), ?_, ?_,
    le_trans (sGlobal13_hz117 hc).2 (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (sGlobal13_hz64 hc).1) (sGlobal13_hz64 hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) sGlobal13_hz9.1 2
    nlinarith only [h1, h2]
  · linarith only [(sGlobal13_hz84 hc).1, sGlobal13_hz33.2]
  · have hap : 0 < s3ap 12225 46 := lt_of_lt_of_le (by norm_num) sGlobal13_hz9.1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul sGlobal13_hz16.2 sGlobal13_hz9.2 (le_trans (by norm_num) sGlobal13_hz9.1) (by norm_num)
    linarith only [h, (sGlobal13_hz84 hc).1, sGlobal13_hz33.2]

end BstLean.Part255
