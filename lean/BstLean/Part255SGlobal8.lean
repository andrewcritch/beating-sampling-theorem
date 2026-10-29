import BstLean.Part255SGlobal4
import BstLean.Part255Numeric10
namespace BstLean.Part255
open Real BstLean.Part130 BstLean.Part182 BstLean.Part197 BstLean.Part246
theorem sGlobal8_hz0 : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal8_hz1 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) ((√(23 : ℝ)) / (12225 : ℝ)) := bdiv sGlobal8_hz0 (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal8_hz2 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) maskSlack := by
    convert sGlobal8_hz1 using 1 <;>
      norm_num [maskSlack] <;> ring

theorem sGlobal8_hz3 : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal8_hz4 : B (6395294793910793 / 500000000000000000) (12790589587821587 / 1000000000000000000) (√((2 / 12225) : ℝ)) := bsqrt (bpoint ((2 / 12225) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal8_hz5 : B (7230130686979 / 62500000000000000) (23136418198333 / 200000000000000000) (√((2 / 149450625) : ℝ)) := bsqrt (bpoint ((2 / 149450625) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal8_hz6 : B (2211334438749598093 / 20000000000000000) (110566721937479904651 / 1000000000000000000) (√(12225 : ℝ)) := bsqrt (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal8_hz7 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))) := bmul sGlobal8_hz3 sGlobal8_hz4 (by norm_num) (by norm_num)

theorem sGlobal8_hz8 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) ((√(12225 : ℝ)) + ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := badd sGlobal8_hz6 sGlobal8_hz7 (by norm_num) (by norm_num)

theorem sGlobal8_hz9 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) (s3ap 12225 46) := by
    convert sGlobal8_hz8 using 1 <;>
      norm_num [s3ap, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal8_hz10 : B (163599182004089 / 1000000000000000000) (16359918200409 / 100000000000000000) ((2 : ℝ) / (12225 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal8_hz11 : B (1222499983640081799591 / 100000000000000000) (12224999836400817995911 / 1000000000000000000) ((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ))) := bsub (bpoint (12225 : ℝ)) sGlobal8_hz10 (by norm_num) (by norm_num)

theorem sGlobal8_hz12 : B (110566721197658827907 / 1000000000000000000) (27641680299414706977 / 250000000000000000) (√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) := bsqrt sGlobal8_hz11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal8_hz13 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) ((√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) - ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bsub sGlobal8_hz12 sGlobal8_hz7 (by norm_num) (by norm_num)

theorem sGlobal8_hz14 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) (s3am 12225 46) := by
    convert sGlobal8_hz13 using 1 <;>
      norm_num [s3am, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal8_hz15 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√((2 / 12225) : ℝ)) * (√(92 : ℝ))) := bmul sGlobal8_hz4 sGlobal8_hz3 (by norm_num) (by norm_num)

theorem sGlobal8_hz16 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) (s3e0 12225 46) := by
    convert sGlobal8_hz15 using 1 <;>
      norm_num [s3e0, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal8_hz17 : B (250196148528560847 / 500000000000000000) (100078459411424339 / 200000000000000000) (((1 / 2) : ℝ) + maskSlack) := badd (bpoint ((1 / 2) : ℝ)) sGlobal8_hz2 (by norm_num) (by norm_num)

theorem sGlobal8_hz18 : B (59827153232297998295487 / 800000000000000) (23930861292919199366019 / 320000000000000) ((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack)) := bmul (bpoint (149450625 : ℝ)) sGlobal8_hz17 (by norm_num) (by norm_num)

theorem sGlobal8_hz19 : B (1729554180017180009583 / 200000000000000000) (8647770900085900056557 / 1000000000000000000) (√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) := bsqrt sGlobal8_hz18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal8_hz20 : B (4328681281566262743499 / 500000000000000000) (8657362563132525495641 / 1000000000000000000) ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))) := badd sGlobal8_hz19 sGlobal8_hz3 (by norm_num) (by norm_num)

theorem sGlobal8_hz21 : B (110732771457999278473 / 1000000000000000000) (55366385728999643621 / 500000000000000000) ((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ)))) := bmul sGlobal8_hz4 sGlobal8_hz20 (by norm_num) (by norm_num)

theorem sGlobal8_hz22 : B (209099159 / 15625000000000000) (13382346177 / 1000000000000000000) ((2 : ℝ) / (149450625 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (149450625 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal8_hz23 : B (2452349334953899930479 / 200000000000000000) (12261746674769501594427 / 1000000000000000000) (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2) := bsq sGlobal8_hz21 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal8_hz24 : B (82045469362091 / 500000000000000000) (32818187747289 / 200000000000000000) (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2)) := bmul sGlobal8_hz22 sGlobal8_hz23 (by norm_num) (by norm_num)

theorem sGlobal8_hz25 : B (82045469362091 / 250000000000000000) (32818187747289 / 100000000000000000) ((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) := bmul (bpoint (2 : ℝ)) sGlobal8_hz24 (by norm_num) (by norm_num)

theorem sGlobal8_hz26 : B (117258080744995992792057 / 1000000000000000000) (58629040372497996396029 / 500000000000000000) (√(13749457500 : ℝ)) := bsqrt (bpoint (13749457500 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal8_hz27 : B (117304080744995992792057 / 1000000000000000000) (58652040372497996396029 / 500000000000000000) ((√(13749457500 : ℝ)) + (46 : ℝ)) := badd sGlobal8_hz26 (bpoint (46 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal8_hz28 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal8_hz25 sGlobal8_hz27 (by norm_num) (by norm_num)

theorem sGlobal8_hz29 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (s3rs 12225 46 maskSlack) := by
    convert sGlobal8_hz28 using 1 <;>
      norm_num [s3rs, s3pp, s3K, mA, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal8_hz30 : B (490797546012267 / 1000000000000000000) (49079754601227 / 100000000000000000) ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (3 : ℝ)) sGlobal8_hz10 (by norm_num) (by norm_num)

theorem sGlobal8_hz31 : B (490797546012267 / 500000000000000000) (49079754601227 / 50000000000000000) ((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal8_hz30 (by norm_num) (by norm_num)

theorem sGlobal8_hz32 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal8_hz31 sGlobal8_hz27 (by norm_num) (by norm_num)

theorem sGlobal8_hz33 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (s3r1 12225 46) := by
    convert sGlobal8_hz32 using 1 <;>
      norm_num [s3r1, mA] <;> ring

theorem sGlobal8_hz34 : B (163599182004089 / 500000000000000000) (16359918200409 / 50000000000000000) ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (2 : ℝ)) sGlobal8_hz10 (by norm_num) (by norm_num)

theorem sGlobal8_hz35 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal8_hz34 (by norm_num) (by norm_num)

theorem sGlobal8_hz36 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal8_hz35 sGlobal8_hz27 (by norm_num) (by norm_num)

theorem sGlobal8_hz37 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (s3rpp 12225 46) := by
    convert sGlobal8_hz36 using 1 <;>
      norm_num [s3rpp, mA] <;> ring

theorem sGlobal8_hz38 {c : ℝ} (hc : B (77 / 200) (39 / 100) c) : B (77 / 200) (39 / 100) c := hc

theorem sGlobal8_hz39 : B (625798557007091147 / 1000000000000000000) (312899278533441013 / 500000000000000000) (kdot ((77 / 200))) := by
    constructor
    · apply bkdot_lower (q := (666365756397820153 / 1000000000000000000)) (a := (146948563033652783 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (83295719549727519 / 125000000000000000)) (a := (918428518813581 / 1562500000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal8_hz40 : B (5929 / 40000) (5929 / 40000) (((77 / 200) : ℝ)^2) := bsq (bpoint ((77 / 200) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal8_hz41 : B (34071 / 40000) (34071 / 40000) ((1 : ℝ) - (((77 / 200) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal8_hz40 (by norm_num) (by norm_num)

theorem sGlobal8_hz42 : B (92291657261098091 / 100000000000000000) (922916572610980911 / 1000000000000000000) (√((1 : ℝ) - (((77 / 200) : ℝ)^2))) := bsqrt sGlobal8_hz41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal8_hz43 : B (36721683648116939 / 125000000000000000) (293773469184935513 / 1000000000000000000) ((√((1 : ℝ) - (((77 / 200) : ℝ)^2))) / Real.pi) := bdiv sGlobal8_hz42 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal8_hz44 : B (240932444447730091 / 1000000000000000000) (240932444470749581 / 1000000000000000000) (((77 / 200) : ℝ) * (kdot ((77 / 200)))) := bmul (bpoint ((77 / 200) : ℝ)) sGlobal8_hz39 (by norm_num) (by norm_num)

theorem sGlobal8_hz45 : B (534705913632665603 / 1000000000000000000) (267352956827842547 / 500000000000000000) (((√((1 : ℝ) - (((77 / 200) : ℝ)^2))) / Real.pi) + (((77 / 200) : ℝ) * (kdot ((77 / 200))))) := badd sGlobal8_hz43 sGlobal8_hz44 (by norm_num) (by norm_num)

theorem sGlobal8_hz46 : B (534705913632665603 / 1000000000000000000) (267352956827842547 / 500000000000000000) (kappa ((77 / 200))) := by rw [kappa_eq]; exact sGlobal8_hz45

theorem sGlobal8_hz47 : B (627524996667760753 / 1000000000000000000) (627524996712576683 / 1000000000000000000) (kdot ((39 / 100))) := by
    constructor
    · apply bkdot_lower (q := (331228365657030253 / 500000000000000000)) (a := (585082367057198287 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (132491346262812101 / 200000000000000000)) (a := (58508236698680159 / 100000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal8_hz48 : B (1521 / 10000) (1521 / 10000) (((39 / 100) : ℝ)^2) := bsq (bpoint ((39 / 100) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal8_hz49 : B (8479 / 10000) (8479 / 10000) ((1 : ℝ) - (((39 / 100) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal8_hz48 (by norm_num) (by norm_num)

theorem sGlobal8_hz50 : B (460407428263272051 / 500000000000000000) (920814856526544103 / 1000000000000000000) (√((1 : ℝ) - (((39 / 100) : ℝ)^2))) := bsqrt sGlobal8_hz49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal8_hz51 : B (293104472177307789 / 1000000000000000000) (293104472177307791 / 1000000000000000000) ((√((1 : ℝ) - (((39 / 100) : ℝ)^2))) / Real.pi) := bdiv sGlobal8_hz50 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal8_hz52 : B (244734748700426693 / 1000000000000000000) (244734748717904907 / 1000000000000000000) (((39 / 100) : ℝ) * (kdot ((39 / 100)))) := bmul (bpoint ((39 / 100) : ℝ)) sGlobal8_hz47 (by norm_num) (by norm_num)

theorem sGlobal8_hz53 : B (268919610438867241 / 500000000000000000) (268919610447606349 / 500000000000000000) (((√((1 : ℝ) - (((39 / 100) : ℝ)^2))) / Real.pi) + (((39 / 100) : ℝ) * (kdot ((39 / 100))))) := badd sGlobal8_hz51 sGlobal8_hz52 (by norm_num) (by norm_num)

theorem sGlobal8_hz54 : B (268919610438867241 / 500000000000000000) (268919610447606349 / 500000000000000000) (kappa ((39 / 100))) := by rw [kappa_eq]; exact sGlobal8_hz53

theorem sGlobal8_hz55 {c : ℝ} (hc : B (77 / 200) (39 / 100) c) : B (534705913632665603 / 1000000000000000000) (268919610447606349 / 500000000000000000) (kappa c) := bkappa (sGlobal8_hz38 hc) (by norm_num) (by norm_num) sGlobal8_hz46.1 sGlobal8_hz54.2

theorem sGlobal8_hz56 : B 24450 24450 ((2 : ℝ) * (12225 : ℝ)) := bmul (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal8_hz57 {c : ℝ} (hc : B (77 / 200) (39 / 100) c) : B (231080389552393651 / 500000000000000000) (465294086367334397 / 1000000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (sGlobal8_hz55 hc) (by norm_num) (by norm_num)

theorem sGlobal8_hz58 {c : ℝ} (hc : B (77 / 200) (39 / 100) c) : B (112998310491120495339 / 10000000000000000) (227528808233626520133 / 20000000000000000) (((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) := bmul sGlobal8_hz56 (sGlobal8_hz57 hc) (by norm_num) (by norm_num)

theorem sGlobal8_hz59 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (4 : ℝ)) sGlobal8_hz10 (by norm_num) (by norm_num)

theorem sGlobal8_hz60 {c : ℝ} (hc : B (77 / 200) (39 / 100) c) : B (564991519735766075877 / 50000000000000000) (5688219878642298995147 / 500000000000000000) ((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bsub (sGlobal8_hz58 hc) sGlobal8_hz59 (by norm_num) (by norm_num)

theorem sGlobal8_hz61 {c : ℝ} (hc : B (77 / 200) (39 / 100) c) : B (53150330184099800937 / 500000000000000000) (53330197255599472399 / 500000000000000000) (√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) := bsqrt (sGlobal8_hz60 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal8_hz62 : B (30670756373515103 / 125000000000000000) (122683025494060423 / 500000000000000000) ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal8_hz7 (by norm_num) (by norm_num)

theorem sGlobal8_hz63 {c : ℝ} (hc : B (77 / 200) (39 / 100) c) : B (26513823579302870257 / 250000000000000000) (53207514230105411987 / 500000000000000000) ((√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) - ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))))) := bsub (sGlobal8_hz61 hc) sGlobal8_hz62 (by norm_num) (by norm_num)

theorem sGlobal8_hz64 {c : ℝ} (hc : B (77 / 200) (39 / 100) c) : B (26513823579302870257 / 250000000000000000) (53207514230105411987 / 500000000000000000) (s3dm 12225 46 c) := by
    convert (sGlobal8_hz63 hc) using 1 <;>
      norm_num [s3dm, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal8_hz65 : B (6126072185528622723889 / 500000000000000000) (2450428874211449090087 / 200000000000000000) ((s3ap 12225 46)^2) := bsq sGlobal8_hz9 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal8_hz66 : B (6126072185528622723889 / 250000000000000000) (2450428874211449090087 / 100000000000000000) ((2 : ℝ) * ((s3ap 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal8_hz65 (by norm_num) (by norm_num)

theorem sGlobal8_hz67 {c : ℝ} (hc : B (77 / 200) (39 / 100) c) : B (11247725452710349861823 / 1000000000000000000) (11324158282187479649987 / 1000000000000000000) ((s3dm 12225 46 c)^2) := bsq (sGlobal8_hz64 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal8_hz68 {c : ℝ} (hc : B (77 / 200) (39 / 100) c) : B (13180130459927011245569 / 1000000000000000000) (13256563289404141039047 / 1000000000000000000) (((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) := bsub sGlobal8_hz66 (sGlobal8_hz67 hc) (by norm_num) (by norm_num)

theorem sGlobal8_hz69 : B (1524735695971823534271 / 125000000000000000) (609894278388729413841 / 50000000000000000) ((s3am 12225 46)^2) := bsq sGlobal8_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal8_hz70 : B (1524735695971823534271 / 62500000000000000) (609894278388729413841 / 25000000000000000) ((2 : ℝ) * ((s3am 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal8_hz69 (by norm_num) (by norm_num)

theorem sGlobal8_hz71 {c : ℝ} (hc : B (77 / 200) (39 / 100) c) : B (108052583266950799 / 200000000000000000) (16981123510796281 / 31250000000000000) ((((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) / ((2 : ℝ) * ((s3am 12225 46)^2))) := bdiv (sGlobal8_hz68 hc) sGlobal8_hz70 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal8_hz72 {c : ℝ} (hc : B (77 / 200) (39 / 100) c) : B (108052583266950799 / 200000000000000000) (16981123510796281 / 31250000000000000) (s3c1 12225 46 c) := by
    convert (sGlobal8_hz71 hc) using 1 <;>
      norm_num [s3c1] <;> ring

theorem sGlobal8_hz73 {c : ℝ} (hc : B (77 / 200) (39 / 100) c) : B (625798557007091147 / 1000000000000000000) (627524996712576683 / 1000000000000000000) (kdot c) := bkdot (sGlobal8_hz38 hc) sGlobal8_hz39.1 sGlobal8_hz47.2

theorem sGlobal8_hz74 : B (340837606924861039 / 500000000000000000) (170418803462431407 / 250000000000000000) (kdot ((108052583266950799 / 200000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (273166440063655611 / 500000000000000000)) (a := (25001170240631377 / 50000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (546332880127311221 / 1000000000000000000)) (a := (125005851203155491 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal8_hz75 : B (682861759140656019 / 1000000000000000000) (682861759140658877 / 1000000000000000000) (kdot ((16981123510796281 / 31250000000000000))) := by
    constructor
    · apply bkdot_lower (q := (271957602804515119 / 500000000000000000)) (a := (498159583828052723 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (543915205609030237 / 1000000000000000000)) (a := (99631916765609647 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal8_hz76 {c : ℝ} (hc : B (77 / 200) (39 / 100) c) : B (340837606924861039 / 500000000000000000) (682861759140658877 / 1000000000000000000) (kdot (s3c1 12225 46 c)) := bkdot (sGlobal8_hz72 hc) sGlobal8_hz74.1 sGlobal8_hz75.2

theorem sGlobal8_hz77 {c : ℝ} (hc : B (77 / 200) (39 / 100) c) : B (5929 / 40000) (1521 / 10000) (c^2) := bsq (sGlobal8_hz38 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal8_hz78 {c : ℝ} (hc : B (77 / 200) (39 / 100) c) : B (8479 / 10000) (34071 / 40000) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (sGlobal8_hz77 hc) (by norm_num) (by norm_num)

theorem sGlobal8_hz79 {c : ℝ} (hc : B (77 / 200) (39 / 100) c) : B (460407428263272051 / 500000000000000000) (922916572610980911 / 1000000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (sGlobal8_hz78 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal8_hz80 : B (39119999999999765769 / 1600000000000000) (3912000000000000489 / 160000000000000) ((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (149450625 : ℝ)) sGlobal8_hz10 (by norm_num) (by norm_num)

theorem sGlobal8_hz81 {c : ℝ} (hc : B (77 / 200) (39 / 100) c) : B (144061152121250741 / 250000000000000000) (36197076199605521 / 62500000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (sGlobal8_hz79 hc) (sGlobal8_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal8_hz82 {c : ℝ} (hc : B (77 / 200) (39 / 100) c) : B (1408918067745823811083 / 100000000000000000) (7080148104642840792619 / 500000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) := bmul sGlobal8_hz80 (sGlobal8_hz81 hc) (by norm_num) (by norm_num)

theorem sGlobal8_hz83 {c : ℝ} (hc : B (77 / 200) (39 / 100) c) : B (1408918067745823811083 / 200000000000000000) (7080148104642840792619 / 1000000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) / (2 : ℝ)) := bdiv (sGlobal8_hz82 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal8_hz84 {c : ℝ} (hc : B (77 / 200) (39 / 100) c) : B (1408918067745823811083 / 200000000000000000) (7080148104642840792619 / 1000000000000000000) (s3Cpa 12225 c) := by
    convert (sGlobal8_hz83 hc) using 1 <;>
      norm_num [s3Cpa, mA] <;> ring

theorem sGlobal8_hz85 {c : ℝ} (hc : B (77 / 200) (39 / 100) c) : B (293104472177307789 / 1000000000000000000) (293773469184935513 / 1000000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (sGlobal8_hz79 hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal8_hz86 {c : ℝ} (hc : B (77 / 200) (39 / 100) c) : B (240932444447730091 / 1000000000000000000) (244734748717904907 / 1000000000000000000) (c * (kdot c)) := bmul (sGlobal8_hz38 hc) (sGlobal8_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal8_hz87 {c : ℝ} (hc : B (77 / 200) (39 / 100) c) : B (24184861729701441 / 500000000000000000) (26420512368602711 / 500000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (sGlobal8_hz85 hc) (sGlobal8_hz86 hc) (by norm_num) (by norm_num)

theorem sGlobal8_hz88 {c : ℝ} (hc : B (77 / 200) (39 / 100) c) : B (295659934645598345961 / 250000000000000000) (322990763706168182349 / 250000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) := bmul sGlobal8_hz80 (sGlobal8_hz87 hc) (by norm_num) (by norm_num)

theorem sGlobal8_hz89 {c : ℝ} (hc : B (77 / 200) (39 / 100) c) : B (295659934645598345961 / 500000000000000000) (322990763706168182349 / 500000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) / (2 : ℝ)) := bdiv (sGlobal8_hz88 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal8_hz90 {c : ℝ} (hc : B (77 / 200) (39 / 100) c) : B (295659934645598345961 / 500000000000000000) (322990763706168182349 / 500000000000000000) (s3Cpp 12225 c) := by
    convert (sGlobal8_hz89 hc) using 1 <;>
      norm_num [s3Cpp, mA] <;> ring

theorem sGlobal8_hz91 {c : ℝ} (hc : B (77 / 200) (39 / 100) c) : B (894966931082857095477 / 125000000000000000) (1439058642915315840969 / 200000000000000000) ((s3Cpa 12225 c) + (s3r1 12225 46)) := badd (sGlobal8_hz84 hc) sGlobal8_hz33 (by norm_num) (by norm_num)

theorem sGlobal8_hz92 {c : ℝ} (hc : B (77 / 200) (39 / 100) c) : B (12965363395173876007 / 200000000000000000) (32574384881510111061 / 500000000000000000) (((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) := bdiv (sGlobal8_hz91 hc) sGlobal8_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal8_hz93 {c : ℝ} (hc : B (77 / 200) (39 / 100) c) : B (64949500001363440447 / 1000000000000000000) (13054290557702856509 / 200000000000000000) ((((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) + (s3e0 12225 46)) := badd (sGlobal8_hz92 hc) sGlobal8_hz16 (by norm_num) (by norm_num)

theorem sGlobal8_hz94 {c : ℝ} (hc : B (77 / 200) (39 / 100) c) : B (64949500001363440447 / 1000000000000000000) (13054290557702856509 / 200000000000000000) (s3Lam 12225 46 c) := by
    convert (sGlobal8_hz93 hc) using 1 <;>
      norm_num [s3Lam] <;> ring

theorem sGlobal8_hz95 {c : ℝ} (hc : B (77 / 200) (39 / 100) c) : B (334041637956844248761 / 500000000000000000) (180686233508707159879 / 250000000000000000) ((s3Cpp 12225 c) + (s3rpp 12225 46)) := badd (sGlobal8_hz90 hc) sGlobal8_hz37 (by norm_num) (by norm_num)

theorem sGlobal8_hz96 {c : ℝ} (hc : B (77 / 200) (39 / 100) c) : B (334041637956844248761 / 1000000000000000000) (493534877065022542823 / 1000000000000000000) (if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) := bweaken (bfirst (sGlobal8_hz95 hc) (sGlobal8_hz76 hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem sGlobal8_hz97 {c : ℝ} (hc : B (77 / 200) (39 / 100) c) : B (2109218775213554775313 / 500000000000000000) (66568164830050764229 / 15625000000000000) ((s3Lam 12225 46 c)^2) := bsq (sGlobal8_hz94 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal8_hz98 {c : ℝ} (hc : B (77 / 200) (39 / 100) c) : B (58376803753306679 / 200000000000000000) (1181116644101809 / 4000000000000000) ((s3c1 12225 46 c)^2) := bsq (sGlobal8_hz72 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal8_hz99 {c : ℝ} (hc : B (77 / 200) (39 / 100) c) : B (2818883355898191 / 4000000000000000) (141623196246693321 / 200000000000000000) ((1 : ℝ) - ((s3c1 12225 46 c)^2)) := bsub (bpoint (1 : ℝ)) (sGlobal8_hz98 hc) (by norm_num) (by norm_num)

theorem sGlobal8_hz100 {c : ℝ} (hc : B (77 / 200) (39 / 100) c) : B (839476526756137327 / 1000000000000000000) (841496275234457949 / 1000000000000000000) (√((1 : ℝ) - ((s3c1 12225 46 c)^2))) := bsqrt (sGlobal8_hz99 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal8_hz101 {c : ℝ} (hc : B (77 / 200) (39 / 100) c) : B (164830830582384783 / 62500000000000000) (2643638516299747759 / 1000000000000000000) (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))) := bmul pi_mem (sGlobal8_hz100 hc) (by norm_num) (by norm_num)

theorem sGlobal8_hz102 {c : ℝ} (hc : B (77 / 200) (39 / 100) c) : B (1595693785068459002017 / 1000000000000000000) (1615429943411686029067 / 1000000000000000000) (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2))))) := bdiv (sGlobal8_hz97 hc) (sGlobal8_hz101 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal8_hz103 {c : ℝ} (hc : B (77 / 200) (39 / 100) c) : B (964867711512651625389 / 500000000000000000) (210896482047670857189 / 100000000000000000) ((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) := badd (sGlobal8_hz96 hc) (sGlobal8_hz102 hc) (by norm_num) (by norm_num)

theorem sGlobal8_hz104 : B (3762781186094069 / 250000000000000000) (376278118609407 / 25000000000000000) ((s3e0 12225 46)^2) := bsq sGlobal8_hz16 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal8_hz105 {c : ℝ} (hc : B (77 / 200) (39 / 100) c) : B (964875237075023813527 / 500000000000000000) (210897987160145294817 / 100000000000000000) (((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) := badd (sGlobal8_hz103 hc) sGlobal8_hz104 (by norm_num) (by norm_num)

theorem sGlobal8_hz106 {c : ℝ} (hc : B (77 / 200) (39 / 100) c) : B (393649509520258979437 / 200000000000000000) (1073738472527788609093 / 500000000000000000) ((((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) + (s3rs 12225 46 maskSlack)) := badd (sGlobal8_hz105 hc) sGlobal8_hz29 (by norm_num) (by norm_num)

theorem sGlobal8_hz107 {c : ℝ} (hc : B (77 / 200) (39 / 100) c) : B (393649509520258979437 / 200000000000000000) (1073738472527788609093 / 500000000000000000) (s3U 12225 46 maskSlack c) := by
    convert (sGlobal8_hz106 hc) using 1 <;>
      norm_num [s3U] <;> ring

theorem sGlobal8_hz108 {c : ℝ} (hc : B (77 / 200) (39 / 100) c) : B (32159778916794026069 / 62500000000000000) (284609060394922279549 / 500000000000000000) ((s3Cpp 12225 c) - (s3rpp 12225 46)) := bsub (sGlobal8_hz90 hc) sGlobal8_hz37 (by norm_num) (by norm_num)

theorem sGlobal8_hz109 {c : ℝ} (hc : B (77 / 200) (39 / 100) c) : B 0 0 (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ)) := bweaken (bmin (sGlobal8_hz108 hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem sGlobal8_hz110 {c : ℝ} (hc : B (77 / 200) (39 / 100) c) : B 0 0 ((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) := bmul (sGlobal8_hz76 hc) (sGlobal8_hz109 hc) (by norm_num) (by norm_num)

theorem sGlobal8_hz111 {c : ℝ} (hc : B (77 / 200) (39 / 100) c) : B (-376278118609407 / 25000000000000000) (-3762781186094069 / 250000000000000000) (((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) := bsub (sGlobal8_hz110 hc) sGlobal8_hz104 (by norm_num) (by norm_num)

theorem sGlobal8_hz112 {c : ℝ} (hc : B (77 / 200) (39 / 100) c) : B (-4814015572358580787 / 125000000000000000) (-38512124575991646407 / 1000000000000000000) ((((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) - (s3rs 12225 46 maskSlack)) := bsub (sGlobal8_hz111 hc) sGlobal8_hz29 (by norm_num) (by norm_num)

theorem sGlobal8_hz113 {c : ℝ} (hc : B (77 / 200) (39 / 100) c) : B (-4814015572358580787 / 125000000000000000) (-38512124575991646407 / 1000000000000000000) (s3L 12225 46 maskSlack c) := by
    convert (sGlobal8_hz112 hc) using 1 <;>
      norm_num [s3L] <;> ring

theorem sGlobal8_hz114 {c : ℝ} (hc : B (77 / 200) (39 / 100) c) : B 0 (1073738472527788609093 / 500000000000000000) |(s3U 12225 46 maskSlack c)| := bweaken (babs (sGlobal8_hz107 hc)) (by norm_num) (by norm_num)

theorem sGlobal8_hz115 {c : ℝ} (hc : B (77 / 200) (39 / 100) c) : B 0 (4814015572358580787 / 125000000000000000) |(s3L 12225 46 maskSlack c)| := bweaken (babs (sGlobal8_hz113 hc)) (by norm_num) (by norm_num)

theorem sGlobal8_hz116 {c : ℝ} (hc : B (77 / 200) (39 / 100) c) : B 0 (1073738472527788609093 / 500000000000000000) (max |(s3U 12225 46 maskSlack c)| |(s3L 12225 46 maskSlack c)|) := bweaken (bmax (sGlobal8_hz114 hc) (sGlobal8_hz115 hc)) (by norm_num) (by norm_num)

theorem sGlobal8_hz117 {c : ℝ} (hc : B (77 / 200) (39 / 100) c) : B 0 (1073738472527788609093 / 500000000000000000) (s3nks 12225 46 maskSlack c) := by
    convert (sGlobal8_hz116 hc) using 1 <;>
      norm_num [s3nks] <;> ring

theorem sGlobal8 {c : ℝ} (hc : B (77 / 200) (39 / 100) c) :
    0 < s3am 12225 46 ∧ 0 ≤ s3dm 12225 46 c ∧
    s3dm 12225 46 c ^ 2 ≤ 2 * s3ap 12225 46 ^ 2 ∧ s3c1 12225 46 c < 1 ∧
    0 ≤ s3Cpa 12225 c - s3r1 12225 46 ∧
    s3e0 12225 46 ≤ (s3Cpa 12225 c - s3r1 12225 46) / s3ap 12225 46 ∧
    s3nks 12225 46 maskSlack c ≤ 12225 * (175663 / 1000000) := by

  refine ⟨lt_of_lt_of_le (by norm_num) sGlobal8_hz14.1,
    le_trans (by norm_num) (sGlobal8_hz64 hc).1, ?_,
    lt_of_le_of_lt (sGlobal8_hz72 hc).2 (by norm_num), ?_, ?_,
    le_trans (sGlobal8_hz117 hc).2 (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (sGlobal8_hz64 hc).1) (sGlobal8_hz64 hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) sGlobal8_hz9.1 2
    nlinarith only [h1, h2]
  · linarith only [(sGlobal8_hz84 hc).1, sGlobal8_hz33.2]
  · have hap : 0 < s3ap 12225 46 := lt_of_lt_of_le (by norm_num) sGlobal8_hz9.1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul sGlobal8_hz16.2 sGlobal8_hz9.2 (le_trans (by norm_num) sGlobal8_hz9.1) (by norm_num)
    linarith only [h, (sGlobal8_hz84 hc).1, sGlobal8_hz33.2]

end BstLean.Part255
