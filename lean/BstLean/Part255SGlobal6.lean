import BstLean.Part255SGlobal2
import BstLean.Part255Numeric10
namespace BstLean.Part255
open Real BstLean.Part130 BstLean.Part182 BstLean.Part197 BstLean.Part246
theorem sGlobal6_hz0 : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal6_hz1 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) ((√(23 : ℝ)) / (12225 : ℝ)) := bdiv sGlobal6_hz0 (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal6_hz2 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) maskSlack := by
    convert sGlobal6_hz1 using 1 <;>
      norm_num [maskSlack] <;> ring

theorem sGlobal6_hz3 : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal6_hz4 : B (6395294793910793 / 500000000000000000) (12790589587821587 / 1000000000000000000) (√((2 / 12225) : ℝ)) := bsqrt (bpoint ((2 / 12225) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal6_hz5 : B (7230130686979 / 62500000000000000) (23136418198333 / 200000000000000000) (√((2 / 149450625) : ℝ)) := bsqrt (bpoint ((2 / 149450625) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal6_hz6 : B (2211334438749598093 / 20000000000000000) (110566721937479904651 / 1000000000000000000) (√(12225 : ℝ)) := bsqrt (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal6_hz7 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))) := bmul sGlobal6_hz3 sGlobal6_hz4 (by norm_num) (by norm_num)

theorem sGlobal6_hz8 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) ((√(12225 : ℝ)) + ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := badd sGlobal6_hz6 sGlobal6_hz7 (by norm_num) (by norm_num)

theorem sGlobal6_hz9 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) (s3ap 12225 46) := by
    convert sGlobal6_hz8 using 1 <;>
      norm_num [s3ap, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal6_hz10 : B (163599182004089 / 1000000000000000000) (16359918200409 / 100000000000000000) ((2 : ℝ) / (12225 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal6_hz11 : B (1222499983640081799591 / 100000000000000000) (12224999836400817995911 / 1000000000000000000) ((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ))) := bsub (bpoint (12225 : ℝ)) sGlobal6_hz10 (by norm_num) (by norm_num)

theorem sGlobal6_hz12 : B (110566721197658827907 / 1000000000000000000) (27641680299414706977 / 250000000000000000) (√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) := bsqrt sGlobal6_hz11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal6_hz13 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) ((√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) - ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bsub sGlobal6_hz12 sGlobal6_hz7 (by norm_num) (by norm_num)

theorem sGlobal6_hz14 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) (s3am 12225 46) := by
    convert sGlobal6_hz13 using 1 <;>
      norm_num [s3am, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal6_hz15 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√((2 / 12225) : ℝ)) * (√(92 : ℝ))) := bmul sGlobal6_hz4 sGlobal6_hz3 (by norm_num) (by norm_num)

theorem sGlobal6_hz16 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) (s3e0 12225 46) := by
    convert sGlobal6_hz15 using 1 <;>
      norm_num [s3e0, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal6_hz17 : B (250196148528560847 / 500000000000000000) (100078459411424339 / 200000000000000000) (((1 / 2) : ℝ) + maskSlack) := badd (bpoint ((1 / 2) : ℝ)) sGlobal6_hz2 (by norm_num) (by norm_num)

theorem sGlobal6_hz18 : B (59827153232297998295487 / 800000000000000) (23930861292919199366019 / 320000000000000) ((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack)) := bmul (bpoint (149450625 : ℝ)) sGlobal6_hz17 (by norm_num) (by norm_num)

theorem sGlobal6_hz19 : B (1729554180017180009583 / 200000000000000000) (8647770900085900056557 / 1000000000000000000) (√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) := bsqrt sGlobal6_hz18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal6_hz20 : B (4328681281566262743499 / 500000000000000000) (8657362563132525495641 / 1000000000000000000) ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))) := badd sGlobal6_hz19 sGlobal6_hz3 (by norm_num) (by norm_num)

theorem sGlobal6_hz21 : B (110732771457999278473 / 1000000000000000000) (55366385728999643621 / 500000000000000000) ((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ)))) := bmul sGlobal6_hz4 sGlobal6_hz20 (by norm_num) (by norm_num)

theorem sGlobal6_hz22 : B (209099159 / 15625000000000000) (13382346177 / 1000000000000000000) ((2 : ℝ) / (149450625 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (149450625 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal6_hz23 : B (2452349334953899930479 / 200000000000000000) (12261746674769501594427 / 1000000000000000000) (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2) := bsq sGlobal6_hz21 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal6_hz24 : B (82045469362091 / 500000000000000000) (32818187747289 / 200000000000000000) (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2)) := bmul sGlobal6_hz22 sGlobal6_hz23 (by norm_num) (by norm_num)

theorem sGlobal6_hz25 : B (82045469362091 / 250000000000000000) (32818187747289 / 100000000000000000) ((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) := bmul (bpoint (2 : ℝ)) sGlobal6_hz24 (by norm_num) (by norm_num)

theorem sGlobal6_hz26 : B (117258080744995992792057 / 1000000000000000000) (58629040372497996396029 / 500000000000000000) (√(13749457500 : ℝ)) := bsqrt (bpoint (13749457500 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal6_hz27 : B (117304080744995992792057 / 1000000000000000000) (58652040372497996396029 / 500000000000000000) ((√(13749457500 : ℝ)) + (46 : ℝ)) := badd sGlobal6_hz26 (bpoint (46 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal6_hz28 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal6_hz25 sGlobal6_hz27 (by norm_num) (by norm_num)

theorem sGlobal6_hz29 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (s3rs 12225 46 maskSlack) := by
    convert sGlobal6_hz28 using 1 <;>
      norm_num [s3rs, s3pp, s3K, mA, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal6_hz30 : B (490797546012267 / 1000000000000000000) (49079754601227 / 100000000000000000) ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (3 : ℝ)) sGlobal6_hz10 (by norm_num) (by norm_num)

theorem sGlobal6_hz31 : B (490797546012267 / 500000000000000000) (49079754601227 / 50000000000000000) ((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal6_hz30 (by norm_num) (by norm_num)

theorem sGlobal6_hz32 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal6_hz31 sGlobal6_hz27 (by norm_num) (by norm_num)

theorem sGlobal6_hz33 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (s3r1 12225 46) := by
    convert sGlobal6_hz32 using 1 <;>
      norm_num [s3r1, mA] <;> ring

theorem sGlobal6_hz34 : B (163599182004089 / 500000000000000000) (16359918200409 / 50000000000000000) ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (2 : ℝ)) sGlobal6_hz10 (by norm_num) (by norm_num)

theorem sGlobal6_hz35 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal6_hz34 (by norm_num) (by norm_num)

theorem sGlobal6_hz36 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal6_hz35 sGlobal6_hz27 (by norm_num) (by norm_num)

theorem sGlobal6_hz37 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (s3rpp 12225 46) := by
    convert sGlobal6_hz36 using 1 <;>
      norm_num [s3rpp, mA] <;> ring

theorem sGlobal6_hz38 {c : ℝ} (hc : B (3 / 8) (19 / 50) c) : B (3 / 8) (19 / 50) c := hc

theorem sGlobal6_hz39 : B (622357293523016123 / 1000000000000000000) (311178646814514469 / 500000000000000000) (kdot ((3 / 8))) := by
    constructor
    · apply bkdot_lower (q := (674199862463242087 / 1000000000000000000)) (a := (148299944043732397 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (337099931231621043 / 500000000000000000)) (a := (593199776008405049 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal6_hz40 : B (9 / 64) (9 / 64) (((3 / 8) : ℝ)^2) := bsq (bpoint ((3 / 8) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal6_hz41 : B (55 / 64) (55 / 64) ((1 : ℝ) - (((3 / 8) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal6_hz40 (by norm_num) (by norm_num)

theorem sGlobal6_hz42 : B (231756202721739467 / 250000000000000000) (927024810886957869 / 1000000000000000000) (√((1 : ℝ) - (((3 / 8) : ℝ)^2))) := bsqrt sGlobal6_hz41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal6_hz43 : B (29508116204297763 / 100000000000000000) (295081162042977631 / 1000000000000000000) ((√((1 : ℝ) - (((3 / 8) : ℝ)^2))) / Real.pi) := bdiv sGlobal6_hz42 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal6_hz44 : B (116691992535565523 / 500000000000000000) (58345996277721463 / 250000000000000000) (((3 / 8) : ℝ) * (kdot ((3 / 8)))) := bmul (bpoint ((3 / 8) : ℝ)) sGlobal6_hz39 (by norm_num) (by norm_num)

theorem sGlobal6_hz45 : B (132116286778527169 / 250000000000000000) (528465147153863483 / 1000000000000000000) (((√((1 : ℝ) - (((3 / 8) : ℝ)^2))) / Real.pi) + (((3 / 8) : ℝ) * (kdot ((3 / 8))))) := badd sGlobal6_hz43 sGlobal6_hz44 (by norm_num) (by norm_num)

theorem sGlobal6_hz46 : B (132116286778527169 / 250000000000000000) (528465147153863483 / 1000000000000000000) (kappa ((3 / 8))) := by rw [kappa_eq]; exact sGlobal6_hz45

theorem sGlobal6_hz47 : B (312038007376789501 / 500000000000000000) (78009501854155621 / 125000000000000000) (kdot ((19 / 50))) := by
    constructor
    · apply bkdot_lower (q := (670280062599836383 / 1000000000000000000)) (a := (590500015179177013 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (335140031299918191 / 500000000000000000)) (a := (73812501881754751 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal6_hz48 : B (361 / 2500) (361 / 2500) (((19 / 50) : ℝ)^2) := bsq (bpoint ((19 / 50) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal6_hz49 : B (2139 / 2500) (2139 / 2500) ((1 : ℝ) - (((19 / 50) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal6_hz48 (by norm_num) (by norm_num)

theorem sGlobal6_hz50 : B (924986486387774207 / 1000000000000000000) (3613228462452243 / 3906250000000000) (√((1 : ℝ) - (((19 / 50) : ℝ)^2))) := bsqrt sGlobal6_hz49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal6_hz51 : B (294432343203636847 / 1000000000000000000) (18402021450227303 / 62500000000000000) ((√((1 : ℝ) - (((19 / 50) : ℝ)^2))) / Real.pi) := bdiv sGlobal6_hz50 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal6_hz52 : B (11857444280318001 / 50000000000000000) (463181417259049 / 1953125000000000) (((19 / 50) : ℝ) * (kdot ((19 / 50)))) := bmul (bpoint ((19 / 50) : ℝ)) sGlobal6_hz47 (by norm_num) (by norm_num)

theorem sGlobal6_hz53 : B (531581228809996867 / 1000000000000000000) (33223826802516871 / 62500000000000000) (((√((1 : ℝ) - (((19 / 50) : ℝ)^2))) / Real.pi) + (((19 / 50) : ℝ) * (kdot ((19 / 50))))) := badd sGlobal6_hz51 sGlobal6_hz52 (by norm_num) (by norm_num)

theorem sGlobal6_hz54 : B (531581228809996867 / 1000000000000000000) (33223826802516871 / 62500000000000000) (kappa ((19 / 50))) := by rw [kappa_eq]; exact sGlobal6_hz53

theorem sGlobal6_hz55 {c : ℝ} (hc : B (3 / 8) (19 / 50) c) : B (132116286778527169 / 250000000000000000) (33223826802516871 / 62500000000000000) (kappa c) := bkappa (sGlobal6_hz38 hc) (by norm_num) (by norm_num) sGlobal6_hz46.1 sGlobal6_hz54.2

theorem sGlobal6_hz56 : B 24450 24450 ((2 : ℝ) * (12225 : ℝ)) := bmul (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal6_hz57 {c : ℝ} (hc : B (3 / 8) (19 / 50) c) : B (29276173197483129 / 62500000000000000) (117883713221472831 / 250000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (sGlobal6_hz55 hc) (by norm_num) (by norm_num)

theorem sGlobal6_hz58 {c : ℝ} (hc : B (3 / 8) (19 / 50) c) : B (14316048693569250081 / 1250000000000000) (57645135765300214359 / 5000000000000000) (((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) := bmul sGlobal6_hz56 (sGlobal6_hz57 hc) (by norm_num) (by norm_num)

theorem sGlobal6_hz59 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (4 : ℝ)) sGlobal6_hz10 (by norm_num) (by norm_num)

theorem sGlobal6_hz60 {c : ℝ} (hc : B (3 / 8) (19 / 50) c) : B (286320957511466801211 / 25000000000000000) (2882256624665828713861 / 250000000000000000) ((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bsub (sGlobal6_hz58 hc) sGlobal6_hz59 (by norm_num) (by norm_num)

theorem sGlobal6_hz61 {c : ℝ} (hc : B (3 / 8) (19 / 50) c) : B (107017934480434969981 / 1000000000000000000) (53686652202068147899 / 500000000000000000) (√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) := bsqrt (sGlobal6_hz60 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal6_hz62 : B (30670756373515103 / 125000000000000000) (122683025494060423 / 500000000000000000) ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal6_hz7 (by norm_num) (by norm_num)

theorem sGlobal6_hz63 {c : ℝ} (hc : B (3 / 8) (19 / 50) c) : B (21354513685889369827 / 200000000000000000) (53563969176574087487 / 500000000000000000) ((√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) - ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))))) := bsub (sGlobal6_hz61 hc) sGlobal6_hz62 (by norm_num) (by norm_num)

theorem sGlobal6_hz64 {c : ℝ} (hc : B (3 / 8) (19 / 50) c) : B (21354513685889369827 / 200000000000000000) (53563969176574087487 / 500000000000000000) (s3dm 12225 46 c) := by
    convert (sGlobal6_hz63 hc) using 1 <;>
      norm_num [s3dm, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal6_hz65 : B (6126072185528622723889 / 500000000000000000) (2450428874211449090087 / 200000000000000000) ((s3ap 12225 46)^2) := bsq sGlobal6_hz9 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal6_hz66 : B (6126072185528622723889 / 250000000000000000) (2450428874211449090087 / 100000000000000000) ((2 : ℝ) * ((s3ap 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal6_hz65 (by norm_num) (by norm_num)

theorem sGlobal6_hz67 {c : ℝ} (hc : B (3 / 8) (19 / 50) c) : B (11400381369020909987729 / 1000000000000000000) (1147639517579591571157 / 100000000000000000) ((s3dm 12225 46 c)^2) := bsq (sGlobal6_hz64 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal6_hz68 {c : ℝ} (hc : B (3 / 8) (19 / 50) c) : B (6513946783159287591993 / 500000000000000000) (13103907373093580913141 / 1000000000000000000) (((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) := bsub sGlobal6_hz66 (sGlobal6_hz67 hc) (by norm_num) (by norm_num)

theorem sGlobal6_hz69 : B (1524735695971823534271 / 125000000000000000) (609894278388729413841 / 50000000000000000) ((s3am 12225 46)^2) := bsq sGlobal6_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal6_hz70 : B (1524735695971823534271 / 62500000000000000) (609894278388729413841 / 25000000000000000) ((2 : ℝ) * ((s3am 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal6_hz69 (by norm_num) (by norm_num)

theorem sGlobal6_hz71 {c : ℝ} (hc : B (3 / 8) (19 / 50) c) : B (133505654462942051 / 250000000000000000) (134284619456020703 / 250000000000000000) ((((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) / ((2 : ℝ) * ((s3am 12225 46)^2))) := bdiv (sGlobal6_hz68 hc) sGlobal6_hz70 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal6_hz72 {c : ℝ} (hc : B (3 / 8) (19 / 50) c) : B (133505654462942051 / 250000000000000000) (134284619456020703 / 250000000000000000) (s3c1 12225 46 c) := by
    convert (sGlobal6_hz71 hc) using 1 <;>
      norm_num [s3c1] <;> ring

theorem sGlobal6_hz73 {c : ℝ} (hc : B (3 / 8) (19 / 50) c) : B (622357293523016123 / 1000000000000000000) (78009501854155621 / 125000000000000000) (kdot c) := bkdot (sGlobal6_hz38 hc) sGlobal6_hz39.1 sGlobal6_hz47.2

theorem sGlobal6_hz74 : B (339660144491673679 / 500000000000000000) (135864057796670563 / 200000000000000000) (kdot ((133505654462942051 / 250000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (551145844275761547 / 1000000000000000000)) (a := (7870664252228233 / 15625000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (275572922137880773 / 500000000000000000)) (a := (251861256071299171 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal6_hz75 : B (340247372965153229 / 500000000000000000) (680494745930310863 / 1000000000000000000) (kdot ((134284619456020703 / 250000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (548743062391256663 / 1000000000000000000)) (a := (50187767948434481 / 100000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (274371531195628331 / 500000000000000000)) (a := (501877679484337891 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal6_hz76 {c : ℝ} (hc : B (3 / 8) (19 / 50) c) : B (339660144491673679 / 500000000000000000) (680494745930310863 / 1000000000000000000) (kdot (s3c1 12225 46 c)) := bkdot (sGlobal6_hz72 hc) sGlobal6_hz74.1 sGlobal6_hz75.2

theorem sGlobal6_hz77 {c : ℝ} (hc : B (3 / 8) (19 / 50) c) : B (9 / 64) (361 / 2500) (c^2) := bsq (sGlobal6_hz38 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal6_hz78 {c : ℝ} (hc : B (3 / 8) (19 / 50) c) : B (2139 / 2500) (55 / 64) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (sGlobal6_hz77 hc) (by norm_num) (by norm_num)

theorem sGlobal6_hz79 {c : ℝ} (hc : B (3 / 8) (19 / 50) c) : B (924986486387774207 / 1000000000000000000) (927024810886957869 / 1000000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (sGlobal6_hz78 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal6_hz80 : B (39119999999999765769 / 1600000000000000) (3912000000000000489 / 160000000000000) ((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (149450625 : ℝ)) sGlobal6_hz10 (by norm_num) (by norm_num)

theorem sGlobal6_hz81 {c : ℝ} (hc : B (3 / 8) (19 / 50) c) : B (575672086213659349 / 1000000000000000000) (578533949629875231 / 1000000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (sGlobal6_hz79 hc) (sGlobal6_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal6_hz82 {c : ℝ} (hc : B (3 / 8) (19 / 50) c) : B (7037591253961943403947 / 500000000000000000) (2829031013690090233219 / 200000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) := bmul sGlobal6_hz80 (sGlobal6_hz81 hc) (by norm_num) (by norm_num)

theorem sGlobal6_hz83 {c : ℝ} (hc : B (3 / 8) (19 / 50) c) : B (7037591253961943403947 / 1000000000000000000) (884072191778153197881 / 125000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) / (2 : ℝ)) := bdiv (sGlobal6_hz82 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal6_hz84 {c : ℝ} (hc : B (3 / 8) (19 / 50) c) : B (7037591253961943403947 / 1000000000000000000) (884072191778153197881 / 125000000000000000) (s3Cpa 12225 c) := by
    convert (sGlobal6_hz83 hc) using 1 <;>
      norm_num [s3Cpa, mA] <;> ring

theorem sGlobal6_hz85 {c : ℝ} (hc : B (3 / 8) (19 / 50) c) : B (294432343203636847 / 1000000000000000000) (295081162042977631 / 1000000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (sGlobal6_hz79 hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal6_hz86 {c : ℝ} (hc : B (3 / 8) (19 / 50) c) : B (116691992535565523 / 500000000000000000) (463181417259049 / 1953125000000000) (c * (kdot c)) := bmul (sGlobal6_hz38 hc) (sGlobal6_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal6_hz87 {c : ℝ} (hc : B (3 / 8) (19 / 50) c) : B (57283457567003759 / 1000000000000000000) (12339435394369317 / 200000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (sGlobal6_hz85 hc) (sGlobal6_hz86 hc) (by norm_num) (by norm_num)

theorem sGlobal6_hz88 {c : ℝ} (hc : B (3 / 8) (19 / 50) c) : B (700290268756616760787 / 500000000000000000) (377123994240412297953 / 250000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) := bmul sGlobal6_hz80 (sGlobal6_hz87 hc) (by norm_num) (by norm_num)

theorem sGlobal6_hz89 {c : ℝ} (hc : B (3 / 8) (19 / 50) c) : B (700290268756616760787 / 1000000000000000000) (377123994240412297953 / 500000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) / (2 : ℝ)) := bdiv (sGlobal6_hz88 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal6_hz90 {c : ℝ} (hc : B (3 / 8) (19 / 50) c) : B (700290268756616760787 / 1000000000000000000) (377123994240412297953 / 500000000000000000) (s3Cpp 12225 c) := by
    convert (sGlobal6_hz89 hc) using 1 <;>
      norm_num [s3Cpp, mA] <;> ring

theorem sGlobal6_hz91 {c : ℝ} (hc : B (3 / 8) (19 / 50) c) : B (1788184090973920278087 / 250000000000000000) (3593861322079481997637 / 500000000000000000) ((s3Cpa 12225 c) + (s3r1 12225 46)) := badd (sGlobal6_hz84 hc) sGlobal6_hz33 (by norm_num) (by norm_num)

theorem sGlobal6_hz92 {c : ℝ} (hc : B (3 / 8) (19 / 50) c) : B (64763444747879443751 / 1000000000000000000) (65080223098637904907 / 1000000000000000000) (((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) := bdiv (sGlobal6_hz91 hc) sGlobal6_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal6_hz93 {c : ℝ} (hc : B (3 / 8) (19 / 50) c) : B (64886127773373504163 / 1000000000000000000) (6520290612413196533 / 100000000000000000) ((((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) + (s3e0 12225 46)) := badd (sGlobal6_hz92 hc) sGlobal6_hz16 (by norm_num) (by norm_num)

theorem sGlobal6_hz94 {c : ℝ} (hc : B (3 / 8) (19 / 50) c) : B (64886127773373504163 / 1000000000000000000) (6520290612413196533 / 100000000000000000) (s3Lam 12225 46 c) := by
    convert (sGlobal6_hz93 hc) using 1 <;>
      norm_num [s3Lam] <;> ring

theorem sGlobal6_hz95 {c : ℝ} (hc : B (3 / 8) (19 / 50) c) : B (777053675379108566387 / 1000000000000000000) (207752848775829217681 / 250000000000000000) ((s3Cpp 12225 c) + (s3rpp 12225 46)) := badd (sGlobal6_hz90 hc) sGlobal6_hz37 (by norm_num) (by norm_num)

theorem sGlobal6_hz96 {c : ℝ} (hc : B (3 / 8) (19 / 50) c) : B (388526837689554283193 / 1000000000000000000) (565498888176024790739 / 1000000000000000000) (if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) := bweaken (bfirst (sGlobal6_hz95 hc) (sGlobal6_hz76 hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem sGlobal6_hz97 {c : ℝ} (hc : B (3 / 8) (19 / 50) c) : B (4210209577422552417217 / 1000000000000000000) (265713685439522859339 / 62500000000000000) ((s3Lam 12225 46 c)^2) := bsq (sGlobal6_hz94 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal6_hz98 {c : ℝ} (hc : B (3 / 8) (19 / 50) c) : B (14259007818862783 / 50000000000000000) (288517744359172703 / 1000000000000000000) ((s3c1 12225 46 c)^2) := bsq (sGlobal6_hz72 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal6_hz99 {c : ℝ} (hc : B (3 / 8) (19 / 50) c) : B (711482255640827297 / 1000000000000000000) (35740992181137217 / 50000000000000000) ((1 : ℝ) - ((s3c1 12225 46 c)^2)) := bsub (bpoint (1 : ℝ)) (sGlobal6_hz98 hc) (by norm_num) (by norm_num)

theorem sGlobal6_hz100 {c : ℝ} (hc : B (3 / 8) (19 / 50) c) : B (843494075640621969 / 1000000000000000000) (52841886928376669 / 62500000000000000) (√((1 : ℝ) - ((s3c1 12225 46 c)^2))) := bsqrt (sGlobal6_hz99 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal6_hz101 {c : ℝ} (hc : B (3 / 8) (19 / 50) c) : B (662478697844772837 / 250000000000000000) (2656122940416170691 / 1000000000000000000) (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))) := bmul pi_mem (sGlobal6_hz100 hc) (by norm_num) (by norm_num)

theorem sGlobal6_hz102 {c : ℝ} (hc : B (3 / 8) (19 / 50) c) : B (1585095897994421132497 / 1000000000000000000) (802180315545128506569 / 500000000000000000) (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2))))) := bdiv (sGlobal6_hz97 hc) (sGlobal6_hz101 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal6_hz103 {c : ℝ} (hc : B (3 / 8) (19 / 50) c) : B (197362273568397541569 / 100000000000000000) (2169859519266281803877 / 1000000000000000000) ((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) := badd (sGlobal6_hz96 hc) (sGlobal6_hz102 hc) (by norm_num) (by norm_num)

theorem sGlobal6_hz104 : B (3762781186094069 / 250000000000000000) (376278118609407 / 25000000000000000) ((s3e0 12225 46)^2) := bsq sGlobal6_hz16 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal6_hz105 {c : ℝ} (hc : B (3 / 8) (19 / 50) c) : B (986818893404359895983 / 500000000000000000) (2169874570391026180157 / 1000000000000000000) (((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) := badd (sGlobal6_hz103 hc) sGlobal6_hz104 (by norm_num) (by norm_num)

theorem sGlobal6_hz106 {c : ℝ} (hc : B (3 / 8) (19 / 50) c) : B (2012134860259967062097 / 1000000000000000000) (2208371643845150450173 / 1000000000000000000) ((((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) + (s3rs 12225 46 maskSlack)) := badd (sGlobal6_hz105 hc) sGlobal6_hz29 (by norm_num) (by norm_num)

theorem sGlobal6_hz107 {c : ℝ} (hc : B (3 / 8) (19 / 50) c) : B (2012134860259967062097 / 1000000000000000000) (2208371643845150450173 / 1000000000000000000) (s3U 12225 46 maskSlack c) := by
    convert (sGlobal6_hz106 hc) using 1 <;>
      norm_num [s3U] <;> ring

theorem sGlobal6_hz108 {c : ℝ} (hc : B (3 / 8) (19 / 50) c) : B (623526862134124485969 / 1000000000000000000) (338742290929166395153 / 500000000000000000) ((s3Cpp 12225 c) - (s3rpp 12225 46)) := bsub (sGlobal6_hz90 hc) sGlobal6_hz37 (by norm_num) (by norm_num)

theorem sGlobal6_hz109 {c : ℝ} (hc : B (3 / 8) (19 / 50) c) : B 0 0 (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ)) := bweaken (bmin (sGlobal6_hz108 hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem sGlobal6_hz110 {c : ℝ} (hc : B (3 / 8) (19 / 50) c) : B 0 0 ((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) := bmul (sGlobal6_hz76 hc) (sGlobal6_hz109 hc) (by norm_num) (by norm_num)

theorem sGlobal6_hz111 {c : ℝ} (hc : B (3 / 8) (19 / 50) c) : B (-376278118609407 / 25000000000000000) (-3762781186094069 / 250000000000000000) (((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) := bsub (sGlobal6_hz110 hc) sGlobal6_hz104 (by norm_num) (by norm_num)

theorem sGlobal6_hz112 {c : ℝ} (hc : B (3 / 8) (19 / 50) c) : B (-4814015572358580787 / 125000000000000000) (-38512124575991646407 / 1000000000000000000) ((((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) - (s3rs 12225 46 maskSlack)) := bsub (sGlobal6_hz111 hc) sGlobal6_hz29 (by norm_num) (by norm_num)

theorem sGlobal6_hz113 {c : ℝ} (hc : B (3 / 8) (19 / 50) c) : B (-4814015572358580787 / 125000000000000000) (-38512124575991646407 / 1000000000000000000) (s3L 12225 46 maskSlack c) := by
    convert (sGlobal6_hz112 hc) using 1 <;>
      norm_num [s3L] <;> ring

theorem sGlobal6_hz114 {c : ℝ} (hc : B (3 / 8) (19 / 50) c) : B 0 (2208371643845150450173 / 1000000000000000000) |(s3U 12225 46 maskSlack c)| := bweaken (babs (sGlobal6_hz107 hc)) (by norm_num) (by norm_num)

theorem sGlobal6_hz115 {c : ℝ} (hc : B (3 / 8) (19 / 50) c) : B 0 (4814015572358580787 / 125000000000000000) |(s3L 12225 46 maskSlack c)| := bweaken (babs (sGlobal6_hz113 hc)) (by norm_num) (by norm_num)

theorem sGlobal6_hz116 {c : ℝ} (hc : B (3 / 8) (19 / 50) c) : B 0 (2208371643845150450173 / 1000000000000000000) (max |(s3U 12225 46 maskSlack c)| |(s3L 12225 46 maskSlack c)|) := bweaken (bmax (sGlobal6_hz114 hc) (sGlobal6_hz115 hc)) (by norm_num) (by norm_num)

theorem sGlobal6_hz117 {c : ℝ} (hc : B (3 / 8) (19 / 50) c) : B 0 (2208371643845150450173 / 1000000000000000000) (s3nks 12225 46 maskSlack c) := by
    convert (sGlobal6_hz116 hc) using 1 <;>
      norm_num [s3nks] <;> ring

theorem sGlobal6 {c : ℝ} (hc : B (3 / 8) (19 / 50) c) :
    0 < s3am 12225 46 ∧ 0 ≤ s3dm 12225 46 c ∧
    s3dm 12225 46 c ^ 2 ≤ 2 * s3ap 12225 46 ^ 2 ∧ s3c1 12225 46 c < 1 ∧
    0 ≤ s3Cpa 12225 c - s3r1 12225 46 ∧
    s3e0 12225 46 ≤ (s3Cpa 12225 c - s3r1 12225 46) / s3ap 12225 46 ∧
    s3nks 12225 46 maskSlack c ≤ 12225 * (45161 / 250000) := by

  refine ⟨lt_of_lt_of_le (by norm_num) sGlobal6_hz14.1,
    le_trans (by norm_num) (sGlobal6_hz64 hc).1, ?_,
    lt_of_le_of_lt (sGlobal6_hz72 hc).2 (by norm_num), ?_, ?_,
    le_trans (sGlobal6_hz117 hc).2 (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (sGlobal6_hz64 hc).1) (sGlobal6_hz64 hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) sGlobal6_hz9.1 2
    nlinarith only [h1, h2]
  · linarith only [(sGlobal6_hz84 hc).1, sGlobal6_hz33.2]
  · have hap : 0 < s3ap 12225 46 := lt_of_lt_of_le (by norm_num) sGlobal6_hz9.1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul sGlobal6_hz16.2 sGlobal6_hz9.2 (le_trans (by norm_num) sGlobal6_hz9.1) (by norm_num)
    linarith only [h, (sGlobal6_hz84 hc).1, sGlobal6_hz33.2]

end BstLean.Part255
