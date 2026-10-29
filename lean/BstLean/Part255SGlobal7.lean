import BstLean.Part255SGlobal3
import BstLean.Part255Numeric10
namespace BstLean.Part255
open Real BstLean.Part130 BstLean.Part182 BstLean.Part197 BstLean.Part246
theorem sGlobal7_hz0 : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal7_hz1 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) ((√(23 : ℝ)) / (12225 : ℝ)) := bdiv sGlobal7_hz0 (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal7_hz2 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) maskSlack := by
    convert sGlobal7_hz1 using 1 <;>
      norm_num [maskSlack] <;> ring

theorem sGlobal7_hz3 : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal7_hz4 : B (6395294793910793 / 500000000000000000) (12790589587821587 / 1000000000000000000) (√((2 / 12225) : ℝ)) := bsqrt (bpoint ((2 / 12225) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal7_hz5 : B (7230130686979 / 62500000000000000) (23136418198333 / 200000000000000000) (√((2 / 149450625) : ℝ)) := bsqrt (bpoint ((2 / 149450625) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal7_hz6 : B (2211334438749598093 / 20000000000000000) (110566721937479904651 / 1000000000000000000) (√(12225 : ℝ)) := bsqrt (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal7_hz7 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))) := bmul sGlobal7_hz3 sGlobal7_hz4 (by norm_num) (by norm_num)

theorem sGlobal7_hz8 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) ((√(12225 : ℝ)) + ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := badd sGlobal7_hz6 sGlobal7_hz7 (by norm_num) (by norm_num)

theorem sGlobal7_hz9 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) (s3ap 12225 46) := by
    convert sGlobal7_hz8 using 1 <;>
      norm_num [s3ap, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal7_hz10 : B (163599182004089 / 1000000000000000000) (16359918200409 / 100000000000000000) ((2 : ℝ) / (12225 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal7_hz11 : B (1222499983640081799591 / 100000000000000000) (12224999836400817995911 / 1000000000000000000) ((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ))) := bsub (bpoint (12225 : ℝ)) sGlobal7_hz10 (by norm_num) (by norm_num)

theorem sGlobal7_hz12 : B (110566721197658827907 / 1000000000000000000) (27641680299414706977 / 250000000000000000) (√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) := bsqrt sGlobal7_hz11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal7_hz13 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) ((√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) - ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bsub sGlobal7_hz12 sGlobal7_hz7 (by norm_num) (by norm_num)

theorem sGlobal7_hz14 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) (s3am 12225 46) := by
    convert sGlobal7_hz13 using 1 <;>
      norm_num [s3am, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal7_hz15 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√((2 / 12225) : ℝ)) * (√(92 : ℝ))) := bmul sGlobal7_hz4 sGlobal7_hz3 (by norm_num) (by norm_num)

theorem sGlobal7_hz16 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) (s3e0 12225 46) := by
    convert sGlobal7_hz15 using 1 <;>
      norm_num [s3e0, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal7_hz17 : B (250196148528560847 / 500000000000000000) (100078459411424339 / 200000000000000000) (((1 / 2) : ℝ) + maskSlack) := badd (bpoint ((1 / 2) : ℝ)) sGlobal7_hz2 (by norm_num) (by norm_num)

theorem sGlobal7_hz18 : B (59827153232297998295487 / 800000000000000) (23930861292919199366019 / 320000000000000) ((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack)) := bmul (bpoint (149450625 : ℝ)) sGlobal7_hz17 (by norm_num) (by norm_num)

theorem sGlobal7_hz19 : B (1729554180017180009583 / 200000000000000000) (8647770900085900056557 / 1000000000000000000) (√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) := bsqrt sGlobal7_hz18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal7_hz20 : B (4328681281566262743499 / 500000000000000000) (8657362563132525495641 / 1000000000000000000) ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))) := badd sGlobal7_hz19 sGlobal7_hz3 (by norm_num) (by norm_num)

theorem sGlobal7_hz21 : B (110732771457999278473 / 1000000000000000000) (55366385728999643621 / 500000000000000000) ((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ)))) := bmul sGlobal7_hz4 sGlobal7_hz20 (by norm_num) (by norm_num)

theorem sGlobal7_hz22 : B (209099159 / 15625000000000000) (13382346177 / 1000000000000000000) ((2 : ℝ) / (149450625 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (149450625 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal7_hz23 : B (2452349334953899930479 / 200000000000000000) (12261746674769501594427 / 1000000000000000000) (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2) := bsq sGlobal7_hz21 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal7_hz24 : B (82045469362091 / 500000000000000000) (32818187747289 / 200000000000000000) (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2)) := bmul sGlobal7_hz22 sGlobal7_hz23 (by norm_num) (by norm_num)

theorem sGlobal7_hz25 : B (82045469362091 / 250000000000000000) (32818187747289 / 100000000000000000) ((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) := bmul (bpoint (2 : ℝ)) sGlobal7_hz24 (by norm_num) (by norm_num)

theorem sGlobal7_hz26 : B (117258080744995992792057 / 1000000000000000000) (58629040372497996396029 / 500000000000000000) (√(13749457500 : ℝ)) := bsqrt (bpoint (13749457500 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal7_hz27 : B (117304080744995992792057 / 1000000000000000000) (58652040372497996396029 / 500000000000000000) ((√(13749457500 : ℝ)) + (46 : ℝ)) := badd sGlobal7_hz26 (bpoint (46 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal7_hz28 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal7_hz25 sGlobal7_hz27 (by norm_num) (by norm_num)

theorem sGlobal7_hz29 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (s3rs 12225 46 maskSlack) := by
    convert sGlobal7_hz28 using 1 <;>
      norm_num [s3rs, s3pp, s3K, mA, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal7_hz30 : B (490797546012267 / 1000000000000000000) (49079754601227 / 100000000000000000) ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (3 : ℝ)) sGlobal7_hz10 (by norm_num) (by norm_num)

theorem sGlobal7_hz31 : B (490797546012267 / 500000000000000000) (49079754601227 / 50000000000000000) ((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal7_hz30 (by norm_num) (by norm_num)

theorem sGlobal7_hz32 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal7_hz31 sGlobal7_hz27 (by norm_num) (by norm_num)

theorem sGlobal7_hz33 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (s3r1 12225 46) := by
    convert sGlobal7_hz32 using 1 <;>
      norm_num [s3r1, mA] <;> ring

theorem sGlobal7_hz34 : B (163599182004089 / 500000000000000000) (16359918200409 / 50000000000000000) ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (2 : ℝ)) sGlobal7_hz10 (by norm_num) (by norm_num)

theorem sGlobal7_hz35 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal7_hz34 (by norm_num) (by norm_num)

theorem sGlobal7_hz36 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal7_hz35 sGlobal7_hz27 (by norm_num) (by norm_num)

theorem sGlobal7_hz37 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (s3rpp 12225 46) := by
    convert sGlobal7_hz36 using 1 <;>
      norm_num [s3rpp, mA] <;> ring

theorem sGlobal7_hz38 {c : ℝ} (hc : B (19 / 50) (77 / 200) c) : B (19 / 50) (77 / 200) c := hc

theorem sGlobal7_hz39 : B (312038007376789501 / 500000000000000000) (78009501854155621 / 125000000000000000) (kdot ((19 / 50))) := by
    constructor
    · apply bkdot_lower (q := (670280062599836383 / 1000000000000000000)) (a := (590500015179177013 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (335140031299918191 / 500000000000000000)) (a := (73812501881754751 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal7_hz40 : B (361 / 2500) (361 / 2500) (((19 / 50) : ℝ)^2) := bsq (bpoint ((19 / 50) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal7_hz41 : B (2139 / 2500) (2139 / 2500) ((1 : ℝ) - (((19 / 50) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal7_hz40 (by norm_num) (by norm_num)

theorem sGlobal7_hz42 : B (924986486387774207 / 1000000000000000000) (3613228462452243 / 3906250000000000) (√((1 : ℝ) - (((19 / 50) : ℝ)^2))) := bsqrt sGlobal7_hz41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal7_hz43 : B (294432343203636847 / 1000000000000000000) (18402021450227303 / 62500000000000000) ((√((1 : ℝ) - (((19 / 50) : ℝ)^2))) / Real.pi) := bdiv sGlobal7_hz42 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal7_hz44 : B (11857444280318001 / 50000000000000000) (463181417259049 / 1953125000000000) (((19 / 50) : ℝ) * (kdot ((19 / 50)))) := bmul (bpoint ((19 / 50) : ℝ)) sGlobal7_hz39 (by norm_num) (by norm_num)

theorem sGlobal7_hz45 : B (531581228809996867 / 1000000000000000000) (33223826802516871 / 62500000000000000) (((√((1 : ℝ) - (((19 / 50) : ℝ)^2))) / Real.pi) + (((19 / 50) : ℝ) * (kdot ((19 / 50))))) := badd sGlobal7_hz43 sGlobal7_hz44 (by norm_num) (by norm_num)

theorem sGlobal7_hz46 : B (531581228809996867 / 1000000000000000000) (33223826802516871 / 62500000000000000) (kappa ((19 / 50))) := by rw [kappa_eq]; exact sGlobal7_hz45

theorem sGlobal7_hz47 : B (625798557007091147 / 1000000000000000000) (312899278533441013 / 500000000000000000) (kdot ((77 / 200))) := by
    constructor
    · apply bkdot_lower (q := (666365756397820153 / 1000000000000000000)) (a := (146948563033652783 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (83295719549727519 / 125000000000000000)) (a := (918428518813581 / 1562500000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal7_hz48 : B (5929 / 40000) (5929 / 40000) (((77 / 200) : ℝ)^2) := bsq (bpoint ((77 / 200) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal7_hz49 : B (34071 / 40000) (34071 / 40000) ((1 : ℝ) - (((77 / 200) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal7_hz48 (by norm_num) (by norm_num)

theorem sGlobal7_hz50 : B (92291657261098091 / 100000000000000000) (922916572610980911 / 1000000000000000000) (√((1 : ℝ) - (((77 / 200) : ℝ)^2))) := bsqrt sGlobal7_hz49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal7_hz51 : B (36721683648116939 / 125000000000000000) (293773469184935513 / 1000000000000000000) ((√((1 : ℝ) - (((77 / 200) : ℝ)^2))) / Real.pi) := bdiv sGlobal7_hz50 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal7_hz52 : B (240932444447730091 / 1000000000000000000) (240932444470749581 / 1000000000000000000) (((77 / 200) : ℝ) * (kdot ((77 / 200)))) := bmul (bpoint ((77 / 200) : ℝ)) sGlobal7_hz47 (by norm_num) (by norm_num)

theorem sGlobal7_hz53 : B (534705913632665603 / 1000000000000000000) (267352956827842547 / 500000000000000000) (((√((1 : ℝ) - (((77 / 200) : ℝ)^2))) / Real.pi) + (((77 / 200) : ℝ) * (kdot ((77 / 200))))) := badd sGlobal7_hz51 sGlobal7_hz52 (by norm_num) (by norm_num)

theorem sGlobal7_hz54 : B (534705913632665603 / 1000000000000000000) (267352956827842547 / 500000000000000000) (kappa ((77 / 200))) := by rw [kappa_eq]; exact sGlobal7_hz53

theorem sGlobal7_hz55 {c : ℝ} (hc : B (19 / 50) (77 / 200) c) : B (531581228809996867 / 1000000000000000000) (267352956827842547 / 500000000000000000) (kappa c) := bkappa (sGlobal7_hz38 hc) (by norm_num) (by norm_num) sGlobal7_hz46.1 sGlobal7_hz54.2

theorem sGlobal7_hz56 : B 24450 24450 ((2 : ℝ) * (12225 : ℝ)) := bmul (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal7_hz57 {c : ℝ} (hc : B (19 / 50) (77 / 200) c) : B (232647043172157453 / 500000000000000000) (468418771190003133 / 1000000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (sGlobal7_hz55 hc) (by norm_num) (by norm_num)

theorem sGlobal7_hz58 {c : ℝ} (hc : B (19 / 50) (77 / 200) c) : B (113764404111184994517 / 10000000000000000) (229056779111911532037 / 20000000000000000) (((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) := bmul sGlobal7_hz56 (sGlobal7_hz57 hc) (by norm_num) (by norm_num)

theorem sGlobal7_hz59 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (4 : ℝ)) sGlobal7_hz10 (by norm_num) (by norm_num)

theorem sGlobal7_hz60 {c : ℝ} (hc : B (19 / 50) (77 / 200) c) : B (568821987836088571767 / 50000000000000000) (5726419150599424292747 / 500000000000000000) ((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bsub (sGlobal7_hz58 hc) sGlobal7_hz59 (by norm_num) (by norm_num)

theorem sGlobal7_hz61 {c : ℝ} (hc : B (19 / 50) (77 / 200) c) : B (106660394508560540179 / 1000000000000000000) (107017934483893159213 / 1000000000000000000) (√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) := bsqrt (sGlobal7_hz60 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal7_hz62 : B (30670756373515103 / 125000000000000000) (122683025494060423 / 500000000000000000) ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal7_hz7 (by norm_num) (by norm_num)

theorem sGlobal7_hz63 {c : ℝ} (hc : B (19 / 50) (77 / 200) c) : B (106415028457572419333 / 1000000000000000000) (106772568432905038389 / 1000000000000000000) ((√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) - ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))))) := bsub (sGlobal7_hz61 hc) sGlobal7_hz62 (by norm_num) (by norm_num)

theorem sGlobal7_hz64 {c : ℝ} (hc : B (19 / 50) (77 / 200) c) : B (106415028457572419333 / 1000000000000000000) (106772568432905038389 / 1000000000000000000) (s3dm 12225 46 c) := by
    convert (sGlobal7_hz63 hc) using 1 <;>
      norm_num [s3dm, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal7_hz65 : B (6126072185528622723889 / 500000000000000000) (2450428874211449090087 / 200000000000000000) ((s3ap 12225 46)^2) := bsq sGlobal7_hz9 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal7_hz66 : B (6126072185528622723889 / 250000000000000000) (2450428874211449090087 / 100000000000000000) ((2 : ℝ) * ((s3ap 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal7_hz65 (by norm_num) (by norm_num)

theorem sGlobal7_hz67 {c : ℝ} (hc : B (19 / 50) (77 / 200) c) : B (1132415828162594784007 / 100000000000000000) (11400381369759389485271 / 1000000000000000000) ((s3dm 12225 46 c)^2) := bsq (sGlobal7_hz64 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal7_hz68 {c : ℝ} (hc : B (19 / 50) (77 / 200) c) : B (2620781474471020282057 / 200000000000000000) (8237581537805339413 / 625000000000000) (((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) := bsub sGlobal7_hz66 (sGlobal7_hz67 hc) (by norm_num) (by norm_num)

theorem sGlobal7_hz69 : B (1524735695971823534271 / 125000000000000000) (609894278388729413841 / 50000000000000000) ((s3am 12225 46)^2) := bsq sGlobal7_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal7_hz70 : B (1524735695971823534271 / 62500000000000000) (609894278388729413841 / 25000000000000000) ((2 : ℝ) * ((s3am 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal7_hz69 (by norm_num) (by norm_num)

theorem sGlobal7_hz71 {c : ℝ} (hc : B (19 / 50) (77 / 200) c) : B (537138477793812011 / 1000000000000000000) (8441608068090181 / 15625000000000000) ((((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) / ((2 : ℝ) * ((s3am 12225 46)^2))) := bdiv (sGlobal7_hz68 hc) sGlobal7_hz70 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal7_hz72 {c : ℝ} (hc : B (19 / 50) (77 / 200) c) : B (537138477793812011 / 1000000000000000000) (8441608068090181 / 15625000000000000) (s3c1 12225 46 c) := by
    convert (sGlobal7_hz71 hc) using 1 <;>
      norm_num [s3c1] <;> ring

theorem sGlobal7_hz73 {c : ℝ} (hc : B (19 / 50) (77 / 200) c) : B (312038007376789501 / 500000000000000000) (312899278533441013 / 500000000000000000) (kdot c) := bkdot (sGlobal7_hz38 hc) sGlobal7_hz39.1 sGlobal7_hz47.2

theorem sGlobal7_hz74 : B (680494745918883147 / 1000000000000000000) (680494745918887553 / 1000000000000000000) (kdot ((537138477793812011 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (68592882801825443 / 125000000000000000)) (a := (62734709937786063 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (548743062414603543 / 1000000000000000000)) (a := (100375535900456317 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal7_hz75 : B (681675213858428861 / 1000000000000000000) (170418803464608103 / 250000000000000000) (kdot ((8441608068090181 / 15625000000000000))) := by
    constructor
    · apply bkdot_lower (q := (546332880109552457 / 1000000000000000000)) (a := (500023404798950957 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (68291610013694057 / 125000000000000000)) (a := (25001170239947269 / 50000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal7_hz76 {c : ℝ} (hc : B (19 / 50) (77 / 200) c) : B (680494745918883147 / 1000000000000000000) (170418803464608103 / 250000000000000000) (kdot (s3c1 12225 46 c)) := bkdot (sGlobal7_hz72 hc) sGlobal7_hz74.1 sGlobal7_hz75.2

theorem sGlobal7_hz77 {c : ℝ} (hc : B (19 / 50) (77 / 200) c) : B (361 / 2500) (5929 / 40000) (c^2) := bsq (sGlobal7_hz38 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal7_hz78 {c : ℝ} (hc : B (19 / 50) (77 / 200) c) : B (34071 / 40000) (2139 / 2500) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (sGlobal7_hz77 hc) (by norm_num) (by norm_num)

theorem sGlobal7_hz79 {c : ℝ} (hc : B (19 / 50) (77 / 200) c) : B (92291657261098091 / 100000000000000000) (3613228462452243 / 3906250000000000) (√((1 : ℝ) - (c^2))) := bsqrt (sGlobal7_hz78 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal7_hz80 : B (39119999999999765769 / 1600000000000000) (3912000000000000489 / 160000000000000) ((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (149450625 : ℝ)) sGlobal7_hz10 (by norm_num) (by norm_num)

theorem sGlobal7_hz81 {c : ℝ} (hc : B (19 / 50) (77 / 200) c) : B (17999065518284159 / 31250000000000000) (578855208487834213 / 1000000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (sGlobal7_hz79 hc) (sGlobal7_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal7_hz82 {c : ℝ} (hc : B (19 / 50) (77 / 200) c) : B (14082468861505441682817 / 1000000000000000000) (14153009847527548276977 / 1000000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) := bmul sGlobal7_hz80 (sGlobal7_hz81 hc) (by norm_num) (by norm_num)

theorem sGlobal7_hz83 {c : ℝ} (hc : B (19 / 50) (77 / 200) c) : B (110019287980511263147 / 15625000000000000) (7076504923763774138489 / 1000000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) / (2 : ℝ)) := bdiv (sGlobal7_hz82 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal7_hz84 {c : ℝ} (hc : B (19 / 50) (77 / 200) c) : B (110019287980511263147 / 15625000000000000) (7076504923763774138489 / 1000000000000000000) (s3Cpa 12225 c) := by
    convert (sGlobal7_hz83 hc) using 1 <;>
      norm_num [s3Cpa, mA] <;> ring

theorem sGlobal7_hz85 {c : ℝ} (hc : B (19 / 50) (77 / 200) c) : B (36721683648116939 / 125000000000000000) (18402021450227303 / 62500000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (sGlobal7_hz79 hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal7_hz86 {c : ℝ} (hc : B (19 / 50) (77 / 200) c) : B (11857444280318001 / 50000000000000000) (240932444470749581 / 1000000000000000000) (c * (kdot c)) := bmul (sGlobal7_hz38 hc) (sGlobal7_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal7_hz87 {c : ℝ} (hc : B (19 / 50) (77 / 200) c) : B (52841024714185931 / 1000000000000000000) (14320864399319207 / 250000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (sGlobal7_hz85 hc) (sGlobal7_hz86 hc) (by norm_num) (by norm_num)

theorem sGlobal7_hz88 {c : ℝ} (hc : B (19 / 50) (77 / 200) c) : B (1291963054261838277321 / 1000000000000000000) (1400580538253418619673 / 1000000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) := bmul sGlobal7_hz80 (sGlobal7_hz87 hc) (by norm_num) (by norm_num)

theorem sGlobal7_hz89 {c : ℝ} (hc : B (19 / 50) (77 / 200) c) : B (32299076356545956933 / 50000000000000000) (700290269126709309837 / 1000000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) / (2 : ℝ)) := bdiv (sGlobal7_hz88 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal7_hz90 {c : ℝ} (hc : B (19 / 50) (77 / 200) c) : B (32299076356545956933 / 50000000000000000) (700290269126709309837 / 1000000000000000000) (s3Cpp 12225 c) := by
    convert (sGlobal7_hz89 hc) using 1 <;>
      norm_num [s3Cpp, mA] <;> ring

theorem sGlobal7_hz91 {c : ℝ} (hc : B (19 / 50) (77 / 200) c) : B (7156379540686458549809 / 1000000000000000000) (1438330006739502510143 / 200000000000000000) ((s3Cpa 12225 c) + (s3r1 12225 46)) := badd (sGlobal7_hz84 hc) sGlobal7_hz33 (by norm_num) (by norm_num)

theorem sGlobal7_hz92 {c : ℝ} (hc : B (19 / 50) (77 / 200) c) : B (64796431379399547187 / 1000000000000000000) (65115783094483279349 / 1000000000000000000) (((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) := bdiv (sGlobal7_hz91 hc) sGlobal7_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal7_hz93 {c : ℝ} (hc : B (19 / 50) (77 / 200) c) : B (64919114404893607599 / 1000000000000000000) (16309616529994334943 / 250000000000000000) ((((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) + (s3e0 12225 46)) := badd (sGlobal7_hz92 hc) sGlobal7_hz16 (by norm_num) (by norm_num)

theorem sGlobal7_hz94 {c : ℝ} (hc : B (19 / 50) (77 / 200) c) : B (64919114404893607599 / 1000000000000000000) (16309616529994334943 / 250000000000000000) (s3Lam 12225 46 c) := by
    convert (sGlobal7_hz93 hc) using 1 <;>
      norm_num [s3Lam] <;> ring

theorem sGlobal7_hz95 {c : ℝ} (hc : B (19 / 50) (77 / 200) c) : B (36137246687670547213 / 50000000000000000) (155410735149840316931 / 200000000000000000) ((s3Cpp 12225 c) + (s3rpp 12225 46)) := badd (sGlobal7_hz90 hc) sGlobal7_hz37 (by norm_num) (by norm_num)

theorem sGlobal7_hz96 {c : ℝ} (hc : B (19 / 50) (77 / 200) c) : B (36137246687670547213 / 100000000000000000) (529698230595817985927 / 1000000000000000000) (if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) := bweaken (bfirst (sGlobal7_hz95 hc) (sGlobal7_hz76 hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem sGlobal7_hz97 {c : ℝ} (hc : B (19 / 50) (77 / 200) c) : B (52681142688945808789 / 12500000000000000) (4256057461687431217367 / 1000000000000000000) ((s3Lam 12225 46 c)^2) := bsq (sGlobal7_hz94 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal7_hz98 {c : ℝ} (hc : B (19 / 50) (77 / 200) c) : B (144258872163326739 / 500000000000000000) (58376803758280899 / 200000000000000000) ((s3c1 12225 46 c)^2) := bsq (sGlobal7_hz72 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal7_hz99 {c : ℝ} (hc : B (19 / 50) (77 / 200) c) : B (141623196241719101 / 200000000000000000) (355741127836673261 / 500000000000000000) ((1 : ℝ) - ((s3c1 12225 46 c)^2)) := bsub (bpoint (1 : ℝ)) (sGlobal7_hz98 hc) (by norm_num) (by norm_num)

theorem sGlobal7_hz100 {c : ℝ} (hc : B (19 / 50) (77 / 200) c) : B (168299255043936009 / 200000000000000000) (843494075659898469 / 1000000000000000000) (√((1 : ℝ) - ((s3c1 12225 46 c)^2))) := bsqrt (sGlobal7_hz99 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal7_hz101 {c : ℝ} (hc : B (19 / 50) (77 / 200) c) : B (2643638516253321603 / 1000000000000000000) (132495739571982513 / 50000000000000000) (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))) := bmul pi_mem (sGlobal7_hz100 hc) (by norm_num) (by norm_num)

theorem sGlobal7_hz102 {c : ℝ} (hc : B (19 / 50) (77 / 200) c) : B (7952126288607960423 / 5000000000000000) (402481034710382719909 / 250000000000000000) (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2))))) := bdiv (sGlobal7_hz97 hc) (sGlobal7_hz101 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal7_hz103 {c : ℝ} (hc : B (19 / 50) (77 / 200) c) : B (195179772459829755673 / 100000000000000000) (2139622369437348865563 / 1000000000000000000) ((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) := badd (sGlobal7_hz96 hc) (sGlobal7_hz102 hc) (by norm_num) (by norm_num)

theorem sGlobal7_hz104 : B (3762781186094069 / 250000000000000000) (376278118609407 / 25000000000000000) ((s3e0 12225 46)^2) := bsq sGlobal7_hz16 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal7_hz105 {c : ℝ} (hc : B (19 / 50) (77 / 200) c) : B (975906387861520966503 / 500000000000000000) (2139637420562093241843 / 1000000000000000000) (((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) := badd (sGlobal7_hz103 hc) sGlobal7_hz104 (by norm_num) (by norm_num)

theorem sGlobal7_hz106 {c : ℝ} (hc : B (19 / 50) (77 / 200) c) : B (1990309849174289203137 / 1000000000000000000) (2178134494016217511859 / 1000000000000000000) ((((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) + (s3rs 12225 46 maskSlack)) := badd (sGlobal7_hz105 hc) sGlobal7_hz29 (by norm_num) (by norm_num)

theorem sGlobal7_hz107 {c : ℝ} (hc : B (19 / 50) (77 / 200) c) : B (1990309849174289203137 / 1000000000000000000) (2178134494016217511859 / 1000000000000000000) (s3U 12225 46 maskSlack c) := by
    convert (sGlobal7_hz106 hc) using 1 <;>
      norm_num [s3U] <;> ring

theorem sGlobal7_hz108 {c : ℝ} (hc : B (19 / 50) (77 / 200) c) : B (284609060254213431921 / 500000000000000000) (623526862504217504237 / 1000000000000000000) ((s3Cpp 12225 c) - (s3rpp 12225 46)) := bsub (sGlobal7_hz90 hc) sGlobal7_hz37 (by norm_num) (by norm_num)

theorem sGlobal7_hz109 {c : ℝ} (hc : B (19 / 50) (77 / 200) c) : B 0 0 (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ)) := bweaken (bmin (sGlobal7_hz108 hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem sGlobal7_hz110 {c : ℝ} (hc : B (19 / 50) (77 / 200) c) : B 0 0 ((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) := bmul (sGlobal7_hz76 hc) (sGlobal7_hz109 hc) (by norm_num) (by norm_num)

theorem sGlobal7_hz111 {c : ℝ} (hc : B (19 / 50) (77 / 200) c) : B (-376278118609407 / 25000000000000000) (-3762781186094069 / 250000000000000000) (((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) := bsub (sGlobal7_hz110 hc) sGlobal7_hz104 (by norm_num) (by norm_num)

theorem sGlobal7_hz112 {c : ℝ} (hc : B (19 / 50) (77 / 200) c) : B (-4814015572358580787 / 125000000000000000) (-38512124575991646407 / 1000000000000000000) ((((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) - (s3rs 12225 46 maskSlack)) := bsub (sGlobal7_hz111 hc) sGlobal7_hz29 (by norm_num) (by norm_num)

theorem sGlobal7_hz113 {c : ℝ} (hc : B (19 / 50) (77 / 200) c) : B (-4814015572358580787 / 125000000000000000) (-38512124575991646407 / 1000000000000000000) (s3L 12225 46 maskSlack c) := by
    convert (sGlobal7_hz112 hc) using 1 <;>
      norm_num [s3L] <;> ring

theorem sGlobal7_hz114 {c : ℝ} (hc : B (19 / 50) (77 / 200) c) : B 0 (2178134494016217511859 / 1000000000000000000) |(s3U 12225 46 maskSlack c)| := bweaken (babs (sGlobal7_hz107 hc)) (by norm_num) (by norm_num)

theorem sGlobal7_hz115 {c : ℝ} (hc : B (19 / 50) (77 / 200) c) : B 0 (4814015572358580787 / 125000000000000000) |(s3L 12225 46 maskSlack c)| := bweaken (babs (sGlobal7_hz113 hc)) (by norm_num) (by norm_num)

theorem sGlobal7_hz116 {c : ℝ} (hc : B (19 / 50) (77 / 200) c) : B 0 (2178134494016217511859 / 1000000000000000000) (max |(s3U 12225 46 maskSlack c)| |(s3L 12225 46 maskSlack c)|) := bweaken (bmax (sGlobal7_hz114 hc) (sGlobal7_hz115 hc)) (by norm_num) (by norm_num)

theorem sGlobal7_hz117 {c : ℝ} (hc : B (19 / 50) (77 / 200) c) : B 0 (2178134494016217511859 / 1000000000000000000) (s3nks 12225 46 maskSlack c) := by
    convert (sGlobal7_hz116 hc) using 1 <;>
      norm_num [s3nks] <;> ring

theorem sGlobal7 {c : ℝ} (hc : B (19 / 50) (77 / 200) c) :
    0 < s3am 12225 46 ∧ 0 ≤ s3dm 12225 46 c ∧
    s3dm 12225 46 c ^ 2 ≤ 2 * s3ap 12225 46 ^ 2 ∧ s3c1 12225 46 c < 1 ∧
    0 ≤ s3Cpa 12225 c - s3r1 12225 46 ∧
    s3e0 12225 46 ≤ (s3Cpa 12225 c - s3r1 12225 46) / s3ap 12225 46 ∧
    s3nks 12225 46 maskSlack c ≤ 12225 * (178171 / 1000000) := by

  refine ⟨lt_of_lt_of_le (by norm_num) sGlobal7_hz14.1,
    le_trans (by norm_num) (sGlobal7_hz64 hc).1, ?_,
    lt_of_le_of_lt (sGlobal7_hz72 hc).2 (by norm_num), ?_, ?_,
    le_trans (sGlobal7_hz117 hc).2 (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (sGlobal7_hz64 hc).1) (sGlobal7_hz64 hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) sGlobal7_hz9.1 2
    nlinarith only [h1, h2]
  · linarith only [(sGlobal7_hz84 hc).1, sGlobal7_hz33.2]
  · have hap : 0 < s3ap 12225 46 := lt_of_lt_of_le (by norm_num) sGlobal7_hz9.1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul sGlobal7_hz16.2 sGlobal7_hz9.2 (le_trans (by norm_num) sGlobal7_hz9.1) (by norm_num)
    linarith only [h, (sGlobal7_hz84 hc).1, sGlobal7_hz33.2]

end BstLean.Part255
