import BstLean.Part255SGlobal10
import BstLean.Part255Numeric10
namespace BstLean.Part255
open Real BstLean.Part130 BstLean.Part182 BstLean.Part197 BstLean.Part246
theorem sGlobal14_hz0 : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal14_hz1 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) ((√(23 : ℝ)) / (12225 : ℝ)) := bdiv sGlobal14_hz0 (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal14_hz2 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) maskSlack := by
    convert sGlobal14_hz1 using 1 <;>
      norm_num [maskSlack] <;> ring

theorem sGlobal14_hz3 : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal14_hz4 : B (6395294793910793 / 500000000000000000) (12790589587821587 / 1000000000000000000) (√((2 / 12225) : ℝ)) := bsqrt (bpoint ((2 / 12225) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal14_hz5 : B (7230130686979 / 62500000000000000) (23136418198333 / 200000000000000000) (√((2 / 149450625) : ℝ)) := bsqrt (bpoint ((2 / 149450625) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal14_hz6 : B (2211334438749598093 / 20000000000000000) (110566721937479904651 / 1000000000000000000) (√(12225 : ℝ)) := bsqrt (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal14_hz7 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))) := bmul sGlobal14_hz3 sGlobal14_hz4 (by norm_num) (by norm_num)

theorem sGlobal14_hz8 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) ((√(12225 : ℝ)) + ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := badd sGlobal14_hz6 sGlobal14_hz7 (by norm_num) (by norm_num)

theorem sGlobal14_hz9 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) (s3ap 12225 46) := by
    convert sGlobal14_hz8 using 1 <;>
      norm_num [s3ap, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal14_hz10 : B (163599182004089 / 1000000000000000000) (16359918200409 / 100000000000000000) ((2 : ℝ) / (12225 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal14_hz11 : B (1222499983640081799591 / 100000000000000000) (12224999836400817995911 / 1000000000000000000) ((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ))) := bsub (bpoint (12225 : ℝ)) sGlobal14_hz10 (by norm_num) (by norm_num)

theorem sGlobal14_hz12 : B (110566721197658827907 / 1000000000000000000) (27641680299414706977 / 250000000000000000) (√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) := bsqrt sGlobal14_hz11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal14_hz13 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) ((√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) - ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bsub sGlobal14_hz12 sGlobal14_hz7 (by norm_num) (by norm_num)

theorem sGlobal14_hz14 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) (s3am 12225 46) := by
    convert sGlobal14_hz13 using 1 <;>
      norm_num [s3am, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal14_hz15 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√((2 / 12225) : ℝ)) * (√(92 : ℝ))) := bmul sGlobal14_hz4 sGlobal14_hz3 (by norm_num) (by norm_num)

theorem sGlobal14_hz16 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) (s3e0 12225 46) := by
    convert sGlobal14_hz15 using 1 <;>
      norm_num [s3e0, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal14_hz17 : B (250196148528560847 / 500000000000000000) (100078459411424339 / 200000000000000000) (((1 / 2) : ℝ) + maskSlack) := badd (bpoint ((1 / 2) : ℝ)) sGlobal14_hz2 (by norm_num) (by norm_num)

theorem sGlobal14_hz18 : B (59827153232297998295487 / 800000000000000) (23930861292919199366019 / 320000000000000) ((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack)) := bmul (bpoint (149450625 : ℝ)) sGlobal14_hz17 (by norm_num) (by norm_num)

theorem sGlobal14_hz19 : B (1729554180017180009583 / 200000000000000000) (8647770900085900056557 / 1000000000000000000) (√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) := bsqrt sGlobal14_hz18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal14_hz20 : B (4328681281566262743499 / 500000000000000000) (8657362563132525495641 / 1000000000000000000) ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))) := badd sGlobal14_hz19 sGlobal14_hz3 (by norm_num) (by norm_num)

theorem sGlobal14_hz21 : B (110732771457999278473 / 1000000000000000000) (55366385728999643621 / 500000000000000000) ((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ)))) := bmul sGlobal14_hz4 sGlobal14_hz20 (by norm_num) (by norm_num)

theorem sGlobal14_hz22 : B (209099159 / 15625000000000000) (13382346177 / 1000000000000000000) ((2 : ℝ) / (149450625 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (149450625 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal14_hz23 : B (2452349334953899930479 / 200000000000000000) (12261746674769501594427 / 1000000000000000000) (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2) := bsq sGlobal14_hz21 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal14_hz24 : B (82045469362091 / 500000000000000000) (32818187747289 / 200000000000000000) (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2)) := bmul sGlobal14_hz22 sGlobal14_hz23 (by norm_num) (by norm_num)

theorem sGlobal14_hz25 : B (82045469362091 / 250000000000000000) (32818187747289 / 100000000000000000) ((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) := bmul (bpoint (2 : ℝ)) sGlobal14_hz24 (by norm_num) (by norm_num)

theorem sGlobal14_hz26 : B (117258080744995992792057 / 1000000000000000000) (58629040372497996396029 / 500000000000000000) (√(13749457500 : ℝ)) := bsqrt (bpoint (13749457500 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal14_hz27 : B (117304080744995992792057 / 1000000000000000000) (58652040372497996396029 / 500000000000000000) ((√(13749457500 : ℝ)) + (46 : ℝ)) := badd sGlobal14_hz26 (bpoint (46 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal14_hz28 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal14_hz25 sGlobal14_hz27 (by norm_num) (by norm_num)

theorem sGlobal14_hz29 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (s3rs 12225 46 maskSlack) := by
    convert sGlobal14_hz28 using 1 <;>
      norm_num [s3rs, s3pp, s3K, mA, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal14_hz30 : B (490797546012267 / 1000000000000000000) (49079754601227 / 100000000000000000) ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (3 : ℝ)) sGlobal14_hz10 (by norm_num) (by norm_num)

theorem sGlobal14_hz31 : B (490797546012267 / 500000000000000000) (49079754601227 / 50000000000000000) ((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal14_hz30 (by norm_num) (by norm_num)

theorem sGlobal14_hz32 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal14_hz31 sGlobal14_hz27 (by norm_num) (by norm_num)

theorem sGlobal14_hz33 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (s3r1 12225 46) := by
    convert sGlobal14_hz32 using 1 <;>
      norm_num [s3r1, mA] <;> ring

theorem sGlobal14_hz34 : B (163599182004089 / 500000000000000000) (16359918200409 / 50000000000000000) ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (2 : ℝ)) sGlobal14_hz10 (by norm_num) (by norm_num)

theorem sGlobal14_hz35 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal14_hz34 (by norm_num) (by norm_num)

theorem sGlobal14_hz36 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal14_hz35 sGlobal14_hz27 (by norm_num) (by norm_num)

theorem sGlobal14_hz37 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (s3rpp 12225 46) := by
    convert sGlobal14_hz36 using 1 <;>
      norm_num [s3rpp, mA] <;> ring

theorem sGlobal14_hz38 {c : ℝ} (hc : B (83 / 200) (21 / 50) c) : B (83 / 200) (21 / 50) c := hc

theorem sGlobal14_hz39 : B (318109212453096469 / 500000000000000000) (25448736996663207 / 40000000000000000) (kdot ((83 / 200))) := by
    constructor
    · apply bkdot_lower (q := (321491664681005311 / 500000000000000000)) (a := (285713380956506991 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (642983329362010621 / 1000000000000000000)) (a := (571426761896697749 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal14_hz40 : B (6889 / 40000) (6889 / 40000) (((83 / 200) : ℝ)^2) := bsq (bpoint ((83 / 200) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal14_hz41 : B (33111 / 40000) (33111 / 40000) ((1 : ℝ) - (((83 / 200) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal14_hz40 (by norm_num) (by norm_num)

theorem sGlobal14_hz42 : B (909821411047245029 / 1000000000000000000) (90982141104724503 / 100000000000000000) (√((1 : ℝ) - (((83 / 200) : ℝ)^2))) := bsqrt sGlobal14_hz41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal14_hz43 : B (289605149798024393 / 1000000000000000000) (57921029959604879 / 200000000000000000) ((√((1 : ℝ) - (((83 / 200) : ℝ)^2))) / Real.pi) := bdiv sGlobal14_hz42 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal14_hz44 : B (264030646336070069 / 1000000000000000000) (264030646340380773 / 1000000000000000000) (((83 / 200) : ℝ) * (kdot ((83 / 200)))) := bmul (bpoint ((83 / 200) : ℝ)) sGlobal14_hz39 (by norm_num) (by norm_num)

theorem sGlobal14_hz45 : B (276817898067047231 / 500000000000000000) (34602237258650323 / 62500000000000000) (((√((1 : ℝ) - (((83 / 200) : ℝ)^2))) / Real.pi) + (((83 / 200) : ℝ) * (kdot ((83 / 200))))) := badd sGlobal14_hz43 sGlobal14_hz44 (by norm_num) (by norm_num)

theorem sGlobal14_hz46 : B (276817898067047231 / 500000000000000000) (34602237258650323 / 62500000000000000) (kappa ((83 / 200))) := by rw [kappa_eq]; exact sGlobal14_hz45

theorem sGlobal14_hz47 : B (12759398609945091 / 20000000000000000) (318984965252487437 / 500000000000000000) (kdot ((21 / 50))) := by
    constructor
    · apply bkdot_lower (q := (127820296389165381 / 200000000000000000)) (a := (284337751682106839 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (79887685243228363 / 125000000000000000)) (a := (284337751676043311 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal14_hz48 : B (441 / 2500) (441 / 2500) (((21 / 50) : ℝ)^2) := bsq (bpoint ((21 / 50) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal14_hz49 : B (2059 / 2500) (2059 / 2500) ((1 : ℝ) - (((21 / 50) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal14_hz48 (by norm_num) (by norm_num)

theorem sGlobal14_hz50 : B (226881026090768551 / 250000000000000000) (181504820872614841 / 200000000000000000) (√((1 : ℝ) - (((21 / 50) : ℝ)^2))) := bsqrt sGlobal14_hz49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal14_hz51 : B (288873894368856717 / 1000000000000000000) (144436947184428359 / 500000000000000000) ((√((1 : ℝ) - (((21 / 50) : ℝ)^2))) / Real.pi) := bdiv sGlobal14_hz50 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal14_hz52 : B (267947370808846911 / 1000000000000000000) (33493421351511181 / 125000000000000000) (((21 / 50) : ℝ) * (kdot ((21 / 50)))) := bmul (bpoint ((21 / 50) : ℝ)) sGlobal14_hz47 (by norm_num) (by norm_num)

theorem sGlobal14_hz53 : B (139205316294425907 / 250000000000000000) (278410632590473083 / 500000000000000000) (((√((1 : ℝ) - (((21 / 50) : ℝ)^2))) / Real.pi) + (((21 / 50) : ℝ) * (kdot ((21 / 50))))) := badd sGlobal14_hz51 sGlobal14_hz52 (by norm_num) (by norm_num)

theorem sGlobal14_hz54 : B (139205316294425907 / 250000000000000000) (278410632590473083 / 500000000000000000) (kappa ((21 / 50))) := by rw [kappa_eq]; exact sGlobal14_hz53

theorem sGlobal14_hz55 {c : ℝ} (hc : B (83 / 200) (21 / 50) c) : B (276817898067047231 / 500000000000000000) (278410632590473083 / 500000000000000000) (kappa c) := bkappa (sGlobal14_hz38 hc) (by norm_num) (by norm_num) sGlobal14_hz46.1 sGlobal14_hz54.2

theorem sGlobal14_hz56 : B 24450 24450 ((2 : ℝ) * (12225 : ℝ)) := bmul (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal14_hz57 {c : ℝ} (hc : B (83 / 200) (21 / 50) c) : B (221589367409526917 / 500000000000000000) (223182101932952769 / 500000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (sGlobal14_hz55 hc) (by norm_num) (by norm_num)

theorem sGlobal14_hz58 {c : ℝ} (hc : B (83 / 200) (21 / 50) c) : B (108357200663258662413 / 10000000000000000) (109136047845213904041 / 10000000000000000) (((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) := bmul sGlobal14_hz56 (sGlobal14_hz57 hc) (by norm_num) (by norm_num)

theorem sGlobal14_hz59 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (4 : ℝ)) sGlobal14_hz10 (by norm_num) (by norm_num)

theorem sGlobal14_hz60 {c : ℝ} (hc : B (83 / 200) (21 / 50) c) : B (541785970596456911247 / 50000000000000000) (341050129066395699617 / 31250000000000000) ((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bsub (sGlobal14_hz58 hc) sGlobal14_hz59 (by norm_num) (by norm_num)

theorem sGlobal14_hz61 {c : ℝ} (hc : B (83 / 200) (21 / 50) c) : B (20818952338606415307 / 200000000000000000) (417872786960331503 / 4000000000000000) (√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) := bsqrt (sGlobal14_hz60 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal14_hz62 : B (30670756373515103 / 125000000000000000) (122683025494060423 / 500000000000000000) ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal14_hz7 (by norm_num) (by norm_num)

theorem sGlobal14_hz63 {c : ℝ} (hc : B (83 / 200) (21 / 50) c) : B (103849395642043955689 / 1000000000000000000) (52111415344547377463 / 500000000000000000) ((√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) - ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))))) := bsub (sGlobal14_hz61 hc) sGlobal14_hz62 (by norm_num) (by norm_num)

theorem sGlobal14_hz64 {c : ℝ} (hc : B (83 / 200) (21 / 50) c) : B (103849395642043955689 / 1000000000000000000) (52111415344547377463 / 500000000000000000) (s3dm 12225 46 c) := by
    convert (sGlobal14_hz63 hc) using 1 <;>
      norm_num [s3dm, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal14_hz65 : B (6126072185528622723889 / 500000000000000000) (2450428874211449090087 / 200000000000000000) ((s3ap 12225 46)^2) := bsq sGlobal14_hz9 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal14_hz66 : B (6126072185528622723889 / 250000000000000000) (2450428874211449090087 / 100000000000000000) ((2 : ℝ) * ((s3ap 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal14_hz65 (by norm_num) (by norm_num)

theorem sGlobal14_hz67 {c : ℝ} (hc : B (83 / 200) (21 / 50) c) : B (10784696975217778135639 / 1000000000000000000) (543119921842385573397 / 50000000000000000) ((s3dm 12225 46 c)^2) := bsq (sGlobal14_hz64 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal14_hz68 {c : ℝ} (hc : B (83 / 200) (21 / 50) c) : B (426309072039586857113 / 31250000000000000) (13719591766896712765231 / 1000000000000000000) (((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) := bsub sGlobal14_hz66 (sGlobal14_hz67 hc) (by norm_num) (by norm_num)

theorem sGlobal14_hz69 : B (1524735695971823534271 / 125000000000000000) (609894278388729413841 / 50000000000000000) ((s3am 12225 46)^2) := bsq sGlobal14_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal14_hz70 : B (1524735695971823534271 / 62500000000000000) (609894278388729413841 / 25000000000000000) ((2 : ℝ) * ((s3am 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal14_hz69 (by norm_num) (by norm_num)

theorem sGlobal14_hz71 {c : ℝ} (hc : B (83 / 200) (21 / 50) c) : B (27959539031311881 / 50000000000000000) (112475163754137007 / 200000000000000000) ((((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) / ((2 : ℝ) * ((s3am 12225 46)^2))) := bdiv (sGlobal14_hz68 hc) sGlobal14_hz70 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal14_hz72 {c : ℝ} (hc : B (83 / 200) (21 / 50) c) : B (27959539031311881 / 50000000000000000) (112475163754137007 / 200000000000000000) (s3c1 12225 46 c) := by
    convert (sGlobal14_hz71 hc) using 1 <;>
      norm_num [s3c1] <;> ring

theorem sGlobal14_hz73 {c : ℝ} (hc : B (83 / 200) (21 / 50) c) : B (318109212453096469 / 500000000000000000) (318984965252487437 / 500000000000000000) (kdot c) := bkdot (sGlobal14_hz38 hc) sGlobal14_hz39.1 sGlobal14_hz47.2

theorem sGlobal14_hz74 : B (172222018455278169 / 250000000000000000) (688888073821113617 / 1000000000000000000) (kdot ((27959539031311881 / 50000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (531711073929523357 / 1000000000000000000)) (a := (97738694172776249 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (132927768482380839 / 250000000000000000)) (a := (61086683857984971 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal14_hz75 : B (172528140554601707 / 250000000000000000) (345056281109203789 / 500000000000000000) (kdot ((112475163754137007 / 200000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (529246386240596829 / 1000000000000000000)) (a := (486770048987208621 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (132311596560149207 / 250000000000000000)) (a := (121692512246801861 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal14_hz76 {c : ℝ} (hc : B (83 / 200) (21 / 50) c) : B (172222018455278169 / 250000000000000000) (345056281109203789 / 500000000000000000) (kdot (s3c1 12225 46 c)) := bkdot (sGlobal14_hz72 hc) sGlobal14_hz74.1 sGlobal14_hz75.2

theorem sGlobal14_hz77 {c : ℝ} (hc : B (83 / 200) (21 / 50) c) : B (6889 / 40000) (441 / 2500) (c^2) := bsq (sGlobal14_hz38 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal14_hz78 {c : ℝ} (hc : B (83 / 200) (21 / 50) c) : B (2059 / 2500) (33111 / 40000) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (sGlobal14_hz77 hc) (by norm_num) (by norm_num)

theorem sGlobal14_hz79 {c : ℝ} (hc : B (83 / 200) (21 / 50) c) : B (226881026090768551 / 250000000000000000) (90982141104724503 / 100000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (sGlobal14_hz78 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal14_hz80 : B (39119999999999765769 / 1600000000000000) (3912000000000000489 / 160000000000000) ((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (149450625 : ℝ)) sGlobal14_hz10 (by norm_num) (by norm_num)

theorem sGlobal14_hz81 {c : ℝ} (hc : B (83 / 200) (21 / 50) c) : B (4510809033142801 / 7812500000000000) (580438702377749091 / 1000000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (sGlobal14_hz79 hc) (sGlobal14_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal14_hz82 {c : ℝ} (hc : B (83 / 200) (21 / 50) c) : B (2823405590024725096779 / 200000000000000000) (3547931568283991762229 / 250000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) := bmul sGlobal14_hz80 (sGlobal14_hz81 hc) (by norm_num) (by norm_num)

theorem sGlobal14_hz83 {c : ℝ} (hc : B (83 / 200) (21 / 50) c) : B (7058513975061812741947 / 1000000000000000000) (3547931568283991762229 / 500000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) / (2 : ℝ)) := bdiv (sGlobal14_hz82 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal14_hz84 {c : ℝ} (hc : B (83 / 200) (21 / 50) c) : B (7058513975061812741947 / 1000000000000000000) (3547931568283991762229 / 500000000000000000) (s3Cpa 12225 c) := by
    convert (sGlobal14_hz83 hc) using 1 <;>
      norm_num [s3Cpa, mA] <;> ring

theorem sGlobal14_hz85 {c : ℝ} (hc : B (83 / 200) (21 / 50) c) : B (288873894368856717 / 1000000000000000000) (57921029959604879 / 200000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (sGlobal14_hz79 hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal14_hz86 {c : ℝ} (hc : B (83 / 200) (21 / 50) c) : B (264030646336070069 / 1000000000000000000) (33493421351511181 / 125000000000000000) (c * (kdot c)) := bmul (sGlobal14_hz38 hc) (sGlobal14_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal14_hz87 {c : ℝ} (hc : B (83 / 200) (21 / 50) c) : B (20926523556767269 / 1000000000000000000) (12787251730977163 / 500000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (sGlobal14_hz85 hc) (sGlobal14_hz86 hc) (by norm_num) (by norm_num)

theorem sGlobal14_hz88 {c : ℝ} (hc : B (83 / 200) (21 / 50) c) : B (127913375240739165881 / 250000000000000000) (625296609644783348863 / 1000000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) := bmul sGlobal14_hz80 (sGlobal14_hz87 hc) (by norm_num) (by norm_num)

theorem sGlobal14_hz89 {c : ℝ} (hc : B (83 / 200) (21 / 50) c) : B (127913375240739165881 / 500000000000000000) (4885129762849869913 / 15625000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) / (2 : ℝ)) := bdiv (sGlobal14_hz88 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal14_hz90 {c : ℝ} (hc : B (83 / 200) (21 / 50) c) : B (127913375240739165881 / 500000000000000000) (4885129762849869913 / 15625000000000000) (s3Cpp 12225 c) := by
    convert (sGlobal14_hz89 hc) using 1 <;>
      norm_num [s3Cpp, mA] <;> ring

theorem sGlobal14_hz91 {c : ℝ} (hc : B (83 / 200) (21 / 50) c) : B (1793414771248887612587 / 250000000000000000) (1802752061625430484171 / 250000000000000000) ((s3Cpa 12225 c) + (s3r1 12225 46)) := badd (sGlobal14_hz84 hc) sGlobal14_hz33 (by norm_num) (by norm_num)

theorem sGlobal14_hz92 {c : ℝ} (hc : B (83 / 200) (21 / 50) c) : B (64952886581464468311 / 1000000000000000000) (65291059307890407739 / 1000000000000000000) (((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) := bdiv (sGlobal14_hz91 hc) sGlobal14_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal14_hz93 {c : ℝ} (hc : B (83 / 200) (21 / 50) c) : B (65075569606958528723 / 1000000000000000000) (32706871166692234081 / 500000000000000000) ((((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) + (s3e0 12225 46)) := badd (sGlobal14_hz92 hc) sGlobal14_hz16 (by norm_num) (by norm_num)

theorem sGlobal14_hz94 {c : ℝ} (hc : B (83 / 200) (21 / 50) c) : B (65075569606958528723 / 1000000000000000000) (32706871166692234081 / 500000000000000000) (s3Lam 12225 46 c) := by
    convert (sGlobal14_hz93 hc) using 1 <;>
      norm_num [s3Lam] <;> ring

theorem sGlobal14_hz95 {c : ℝ} (hc : B (83 / 200) (21 / 50) c) : B (166295078551985068681 / 500000000000000000) (1557646845779535797 / 4000000000000000) ((s3Cpp 12225 c) + (s3rpp 12225 46)) := badd (sGlobal14_hz90 hc) sGlobal14_hz37 (by norm_num) (by norm_num)

theorem sGlobal14_hz96 {c : ℝ} (hc : B (83 / 200) (21 / 50) c) : B (166295078551985068681 / 1000000000000000000) (16796119621442753297 / 62500000000000000) (if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) := bweaken (bfirst (sGlobal14_hz95 hc) (sGlobal14_hz76 hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem sGlobal14_hz97 {c : ℝ} (hc : B (83 / 200) (21 / 50) c) : B (2117414879835052300251 / 500000000000000000) (2139478843029207642729 / 500000000000000000) ((s3Lam 12225 46 c)^2) := bsq (sGlobal14_hz94 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal14_hz98 {c : ℝ} (hc : B (83 / 200) (21 / 50) c) : B (156347164568690503 / 500000000000000000) (316266561537998379 / 1000000000000000000) ((s3c1 12225 46 c)^2) := bsq (sGlobal14_hz72 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal14_hz99 {c : ℝ} (hc : B (83 / 200) (21 / 50) c) : B (683733438462001621 / 1000000000000000000) (343652835431309497 / 500000000000000000) ((1 : ℝ) - ((s3c1 12225 46 c)^2)) := bsub (bpoint (1 : ℝ)) (sGlobal14_hz98 hc) (by norm_num) (by norm_num)

theorem sGlobal14_hz100 {c : ℝ} (hc : B (83 / 200) (21 / 50) c) : B (206720439008519671 / 250000000000000000) (414519502213894333 / 500000000000000000) (√((1 : ℝ) - ((s3c1 12225 46 c)^2))) := bsqrt (sGlobal14_hz99 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal14_hz101 {c : ℝ} (hc : B (83 / 200) (21 / 50) c) : B (2597725650144089279 / 1000000000000000000) (1302251422924868471 / 500000000000000000) (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))) := bmul pi_mem (sGlobal14_hz100 hc) (by norm_num) (by norm_num)

theorem sGlobal14_hz102 {c : ℝ} (hc : B (83 / 200) (21 / 50) c) : B (812982363681860809269 / 500000000000000000) (1647193838895601740253 / 1000000000000000000) (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2))))) := bdiv (sGlobal14_hz97 hc) (sGlobal14_hz101 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal14_hz103 {c : ℝ} (hc : B (83 / 200) (21 / 50) c) : B (1792259805915706687219 / 1000000000000000000) (383186350567737158601 / 200000000000000000) ((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) := badd (sGlobal14_hz96 hc) (sGlobal14_hz102 hc) (by norm_num) (by norm_num)

theorem sGlobal14_hz104 : B (3762781186094069 / 250000000000000000) (376278118609407 / 25000000000000000) ((s3e0 12225 46)^2) := bsq sGlobal14_hz16 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal14_hz105 {c : ℝ} (hc : B (83 / 200) (21 / 50) c) : B (358454971408090212699 / 200000000000000000) (383189360792686033857 / 200000000000000000) (((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) := badd (sGlobal14_hz103 hc) sGlobal14_hz104 (by norm_num) (by norm_num)

theorem sGlobal14_hz106 {c : ℝ} (hc : B (83 / 200) (21 / 50) c) : B (915385965245849166813 / 500000000000000000) (1954443877417554439301 / 1000000000000000000) ((((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) + (s3rs 12225 46 maskSlack)) := badd (sGlobal14_hz105 hc) sGlobal14_hz29 (by norm_num) (by norm_num)

theorem sGlobal14_hz107 {c : ℝ} (hc : B (83 / 200) (21 / 50) c) : B (915385965245849166813 / 500000000000000000) (1954443877417554439301 / 1000000000000000000) (s3U 12225 46 maskSlack c) := by
    convert (sGlobal14_hz106 hc) using 1 <;>
      norm_num [s3U] <;> ring

theorem sGlobal14_hz108 {c : ℝ} (hc : B (83 / 200) (21 / 50) c) : B (11191458991186628559 / 62500000000000000) (7371403068746870901 / 31250000000000000) ((s3Cpp 12225 c) - (s3rpp 12225 46)) := bsub (sGlobal14_hz90 hc) sGlobal14_hz37 (by norm_num) (by norm_num)

theorem sGlobal14_hz109 {c : ℝ} (hc : B (83 / 200) (21 / 50) c) : B 0 0 (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ)) := bweaken (bmin (sGlobal14_hz108 hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem sGlobal14_hz110 {c : ℝ} (hc : B (83 / 200) (21 / 50) c) : B 0 0 ((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) := bmul (sGlobal14_hz76 hc) (sGlobal14_hz109 hc) (by norm_num) (by norm_num)

theorem sGlobal14_hz111 {c : ℝ} (hc : B (83 / 200) (21 / 50) c) : B (-376278118609407 / 25000000000000000) (-3762781186094069 / 250000000000000000) (((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) := bsub (sGlobal14_hz110 hc) sGlobal14_hz104 (by norm_num) (by norm_num)

theorem sGlobal14_hz112 {c : ℝ} (hc : B (83 / 200) (21 / 50) c) : B (-4814015572358580787 / 125000000000000000) (-38512124575991646407 / 1000000000000000000) ((((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) - (s3rs 12225 46 maskSlack)) := bsub (sGlobal14_hz111 hc) sGlobal14_hz29 (by norm_num) (by norm_num)

theorem sGlobal14_hz113 {c : ℝ} (hc : B (83 / 200) (21 / 50) c) : B (-4814015572358580787 / 125000000000000000) (-38512124575991646407 / 1000000000000000000) (s3L 12225 46 maskSlack c) := by
    convert (sGlobal14_hz112 hc) using 1 <;>
      norm_num [s3L] <;> ring

theorem sGlobal14_hz114 {c : ℝ} (hc : B (83 / 200) (21 / 50) c) : B 0 (1954443877417554439301 / 1000000000000000000) |(s3U 12225 46 maskSlack c)| := bweaken (babs (sGlobal14_hz107 hc)) (by norm_num) (by norm_num)

theorem sGlobal14_hz115 {c : ℝ} (hc : B (83 / 200) (21 / 50) c) : B 0 (4814015572358580787 / 125000000000000000) |(s3L 12225 46 maskSlack c)| := bweaken (babs (sGlobal14_hz113 hc)) (by norm_num) (by norm_num)

theorem sGlobal14_hz116 {c : ℝ} (hc : B (83 / 200) (21 / 50) c) : B 0 (1954443877417554439301 / 1000000000000000000) (max |(s3U 12225 46 maskSlack c)| |(s3L 12225 46 maskSlack c)|) := bweaken (bmax (sGlobal14_hz114 hc) (sGlobal14_hz115 hc)) (by norm_num) (by norm_num)

theorem sGlobal14_hz117 {c : ℝ} (hc : B (83 / 200) (21 / 50) c) : B 0 (1954443877417554439301 / 1000000000000000000) (s3nks 12225 46 maskSlack c) := by
    convert (sGlobal14_hz116 hc) using 1 <;>
      norm_num [s3nks] <;> ring

theorem sGlobal14 {c : ℝ} (hc : B (83 / 200) (21 / 50) c) :
    0 < s3am 12225 46 ∧ 0 ≤ s3dm 12225 46 c ∧
    s3dm 12225 46 c ^ 2 ≤ 2 * s3ap 12225 46 ^ 2 ∧ s3c1 12225 46 c < 1 ∧
    0 ≤ s3Cpa 12225 c - s3r1 12225 46 ∧
    s3e0 12225 46 ≤ (s3Cpa 12225 c - s3r1 12225 46) / s3ap 12225 46 ∧
    s3nks 12225 46 maskSlack c ≤ 12225 * (159873 / 1000000) := by

  refine ⟨lt_of_lt_of_le (by norm_num) sGlobal14_hz14.1,
    le_trans (by norm_num) (sGlobal14_hz64 hc).1, ?_,
    lt_of_le_of_lt (sGlobal14_hz72 hc).2 (by norm_num), ?_, ?_,
    le_trans (sGlobal14_hz117 hc).2 (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (sGlobal14_hz64 hc).1) (sGlobal14_hz64 hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) sGlobal14_hz9.1 2
    nlinarith only [h1, h2]
  · linarith only [(sGlobal14_hz84 hc).1, sGlobal14_hz33.2]
  · have hap : 0 < s3ap 12225 46 := lt_of_lt_of_le (by norm_num) sGlobal14_hz9.1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul sGlobal14_hz16.2 sGlobal14_hz9.2 (le_trans (by norm_num) sGlobal14_hz9.1) (by norm_num)
    linarith only [h, (sGlobal14_hz84 hc).1, sGlobal14_hz33.2]

end BstLean.Part255
