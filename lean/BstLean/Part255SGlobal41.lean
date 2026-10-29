import BstLean.Part255SGlobal37
import BstLean.Part255Numeric10
namespace BstLean.Part255
open Real BstLean.Part130 BstLean.Part182 BstLean.Part197 BstLean.Part246
theorem sGlobal41_hz0 : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal41_hz1 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) ((√(23 : ℝ)) / (12225 : ℝ)) := bdiv sGlobal41_hz0 (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal41_hz2 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) maskSlack := by
    convert sGlobal41_hz1 using 1 <;>
      norm_num [maskSlack] <;> ring

theorem sGlobal41_hz3 : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal41_hz4 : B (6395294793910793 / 500000000000000000) (12790589587821587 / 1000000000000000000) (√((2 / 12225) : ℝ)) := bsqrt (bpoint ((2 / 12225) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal41_hz5 : B (7230130686979 / 62500000000000000) (23136418198333 / 200000000000000000) (√((2 / 149450625) : ℝ)) := bsqrt (bpoint ((2 / 149450625) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal41_hz6 : B (2211334438749598093 / 20000000000000000) (110566721937479904651 / 1000000000000000000) (√(12225 : ℝ)) := bsqrt (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal41_hz7 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))) := bmul sGlobal41_hz3 sGlobal41_hz4 (by norm_num) (by norm_num)

theorem sGlobal41_hz8 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) ((√(12225 : ℝ)) + ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := badd sGlobal41_hz6 sGlobal41_hz7 (by norm_num) (by norm_num)

theorem sGlobal41_hz9 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) (s3ap 12225 46) := by
    convert sGlobal41_hz8 using 1 <;>
      norm_num [s3ap, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal41_hz10 : B (163599182004089 / 1000000000000000000) (16359918200409 / 100000000000000000) ((2 : ℝ) / (12225 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal41_hz11 : B (1222499983640081799591 / 100000000000000000) (12224999836400817995911 / 1000000000000000000) ((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ))) := bsub (bpoint (12225 : ℝ)) sGlobal41_hz10 (by norm_num) (by norm_num)

theorem sGlobal41_hz12 : B (110566721197658827907 / 1000000000000000000) (27641680299414706977 / 250000000000000000) (√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) := bsqrt sGlobal41_hz11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal41_hz13 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) ((√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) - ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bsub sGlobal41_hz12 sGlobal41_hz7 (by norm_num) (by norm_num)

theorem sGlobal41_hz14 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) (s3am 12225 46) := by
    convert sGlobal41_hz13 using 1 <;>
      norm_num [s3am, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal41_hz15 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√((2 / 12225) : ℝ)) * (√(92 : ℝ))) := bmul sGlobal41_hz4 sGlobal41_hz3 (by norm_num) (by norm_num)

theorem sGlobal41_hz16 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) (s3e0 12225 46) := by
    convert sGlobal41_hz15 using 1 <;>
      norm_num [s3e0, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal41_hz17 : B (250196148528560847 / 500000000000000000) (100078459411424339 / 200000000000000000) (((1 / 2) : ℝ) + maskSlack) := badd (bpoint ((1 / 2) : ℝ)) sGlobal41_hz2 (by norm_num) (by norm_num)

theorem sGlobal41_hz18 : B (59827153232297998295487 / 800000000000000) (23930861292919199366019 / 320000000000000) ((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack)) := bmul (bpoint (149450625 : ℝ)) sGlobal41_hz17 (by norm_num) (by norm_num)

theorem sGlobal41_hz19 : B (1729554180017180009583 / 200000000000000000) (8647770900085900056557 / 1000000000000000000) (√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) := bsqrt sGlobal41_hz18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal41_hz20 : B (4328681281566262743499 / 500000000000000000) (8657362563132525495641 / 1000000000000000000) ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))) := badd sGlobal41_hz19 sGlobal41_hz3 (by norm_num) (by norm_num)

theorem sGlobal41_hz21 : B (110732771457999278473 / 1000000000000000000) (55366385728999643621 / 500000000000000000) ((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ)))) := bmul sGlobal41_hz4 sGlobal41_hz20 (by norm_num) (by norm_num)

theorem sGlobal41_hz22 : B (209099159 / 15625000000000000) (13382346177 / 1000000000000000000) ((2 : ℝ) / (149450625 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (149450625 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal41_hz23 : B (2452349334953899930479 / 200000000000000000) (12261746674769501594427 / 1000000000000000000) (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2) := bsq sGlobal41_hz21 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal41_hz24 : B (82045469362091 / 500000000000000000) (32818187747289 / 200000000000000000) (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2)) := bmul sGlobal41_hz22 sGlobal41_hz23 (by norm_num) (by norm_num)

theorem sGlobal41_hz25 : B (82045469362091 / 250000000000000000) (32818187747289 / 100000000000000000) ((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) := bmul (bpoint (2 : ℝ)) sGlobal41_hz24 (by norm_num) (by norm_num)

theorem sGlobal41_hz26 : B (117258080744995992792057 / 1000000000000000000) (58629040372497996396029 / 500000000000000000) (√(13749457500 : ℝ)) := bsqrt (bpoint (13749457500 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal41_hz27 : B (117304080744995992792057 / 1000000000000000000) (58652040372497996396029 / 500000000000000000) ((√(13749457500 : ℝ)) + (46 : ℝ)) := badd sGlobal41_hz26 (bpoint (46 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal41_hz28 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal41_hz25 sGlobal41_hz27 (by norm_num) (by norm_num)

theorem sGlobal41_hz29 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (s3rs 12225 46 maskSlack) := by
    convert sGlobal41_hz28 using 1 <;>
      norm_num [s3rs, s3pp, s3K, mA, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal41_hz30 : B (490797546012267 / 1000000000000000000) (49079754601227 / 100000000000000000) ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (3 : ℝ)) sGlobal41_hz10 (by norm_num) (by norm_num)

theorem sGlobal41_hz31 : B (490797546012267 / 500000000000000000) (49079754601227 / 50000000000000000) ((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal41_hz30 (by norm_num) (by norm_num)

theorem sGlobal41_hz32 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal41_hz31 sGlobal41_hz27 (by norm_num) (by norm_num)

theorem sGlobal41_hz33 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (s3r1 12225 46) := by
    convert sGlobal41_hz32 using 1 <;>
      norm_num [s3r1, mA] <;> ring

theorem sGlobal41_hz34 : B (163599182004089 / 500000000000000000) (16359918200409 / 50000000000000000) ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (2 : ℝ)) sGlobal41_hz10 (by norm_num) (by norm_num)

theorem sGlobal41_hz35 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal41_hz34 (by norm_num) (by norm_num)

theorem sGlobal41_hz36 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal41_hz35 sGlobal41_hz27 (by norm_num) (by norm_num)

theorem sGlobal41_hz37 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (s3rpp 12225 46) := by
    convert sGlobal41_hz36 using 1 <;>
      norm_num [s3rpp, mA] <;> ring

theorem sGlobal41_hz38 {c : ℝ} (hc : B (11 / 20) (111 / 200) c) : B (11 / 20) (111 / 200) c := hc

theorem sGlobal41_hz39 : B (27414891770940381 / 40000000000000000) (685372294273511327 / 1000000000000000000) (kdot ((11 / 20))) := by
    constructor
    · apply bkdot_lower (q := (538815906080324703 / 1000000000000000000)) (a := (247108022231538449 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (269407953040162351 / 500000000000000000)) (a := (494216044463074069 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal41_hz40 : B (121 / 400) (121 / 400) (((11 / 20) : ℝ)^2) := bsq (bpoint ((11 / 20) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal41_hz41 : B (279 / 400) (279 / 400) ((1 : ℝ) - (((11 / 20) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal41_hz40 (by norm_num) (by norm_num)

theorem sGlobal41_hz42 : B (104395581803062911 / 125000000000000000) (835164654424503289 / 1000000000000000000) (√((1 : ℝ) - (((11 / 20) : ℝ)^2))) := bsqrt sGlobal41_hz41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal41_hz43 : B (265841166094588509 / 1000000000000000000) (265841166094588511 / 1000000000000000000) ((√((1 : ℝ) - (((11 / 20) : ℝ)^2))) / Real.pi) := bdiv sGlobal41_hz42 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal41_hz44 : B (188477380925215119 / 500000000000000000) (37695476185043123 / 100000000000000000) (((11 / 20) : ℝ) * (kdot ((11 / 20)))) := bmul (bpoint ((11 / 20) : ℝ)) sGlobal41_hz39 (by norm_num) (by norm_num)

theorem sGlobal41_hz45 : B (642795927945018747 / 1000000000000000000) (642795927945019741 / 1000000000000000000) (((√((1 : ℝ) - (((11 / 20) : ℝ)^2))) / Real.pi) + (((11 / 20) : ℝ) * (kdot ((11 / 20))))) := badd sGlobal41_hz43 sGlobal41_hz44 (by norm_num) (by norm_num)

theorem sGlobal41_hz46 : B (642795927945018747 / 1000000000000000000) (642795927945019741 / 1000000000000000000) (kappa ((11 / 20))) := by rw [kappa_eq]; exact sGlobal41_hz45

theorem sGlobal41_hz47 : B (85910218598212437 / 125000000000000000) (687281748785700763 / 1000000000000000000) (kdot ((111 / 200))) := by
    constructor
    · apply bkdot_lower (q := (33434499482226583 / 62500000000000000)) (a := (491216680329146951 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (534951991715625327 / 1000000000000000000)) (a := (245608340164572481 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal41_hz48 : B (12321 / 40000) (12321 / 40000) (((111 / 200) : ℝ)^2) := bsq (bpoint ((111 / 200) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal41_hz49 : B (27679 / 40000) (27679 / 40000) ((1 : ℝ) - (((111 / 200) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal41_hz48 (by norm_num) (by norm_num)

theorem sGlobal41_hz50 : B (103981293389724673 / 125000000000000000) (166370069423559477 / 200000000000000000) (√((1 : ℝ) - (((111 / 200) : ℝ)^2))) := bsqrt sGlobal41_hz49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal41_hz51 : B (264786189313012847 / 1000000000000000000) (264786189313012849 / 1000000000000000000) ((√((1 : ℝ) - (((111 / 200) : ℝ)^2))) / Real.pi) := bdiv sGlobal41_hz50 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal41_hz52 : B (19072068528803161 / 50000000000000000) (95360342644015981 / 250000000000000000) (((111 / 200) : ℝ) * (kdot ((111 / 200)))) := bmul (bpoint ((111 / 200) : ℝ)) sGlobal41_hz47 (by norm_num) (by norm_num)

theorem sGlobal41_hz53 : B (646227559889076067 / 1000000000000000000) (646227559889076773 / 1000000000000000000) (((√((1 : ℝ) - (((111 / 200) : ℝ)^2))) / Real.pi) + (((111 / 200) : ℝ) * (kdot ((111 / 200))))) := badd sGlobal41_hz51 sGlobal41_hz52 (by norm_num) (by norm_num)

theorem sGlobal41_hz54 : B (646227559889076067 / 1000000000000000000) (646227559889076773 / 1000000000000000000) (kappa ((111 / 200))) := by rw [kappa_eq]; exact sGlobal41_hz53

theorem sGlobal41_hz55 {c : ℝ} (hc : B (11 / 20) (111 / 200) c) : B (642795927945018747 / 1000000000000000000) (646227559889076773 / 1000000000000000000) (kappa c) := bkappa (sGlobal41_hz38 hc) (by norm_num) (by norm_num) sGlobal41_hz46.1 sGlobal41_hz54.2

theorem sGlobal41_hz56 : B 24450 24450 ((2 : ℝ) * (12225 : ℝ)) := bmul (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal41_hz57 {c : ℝ} (hc : B (11 / 20) (111 / 200) c) : B (353772440110923227 / 1000000000000000000) (357204072054981253 / 1000000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (sGlobal41_hz55 hc) (by norm_num) (by norm_num)

theorem sGlobal41_hz58 {c : ℝ} (hc : B (11 / 20) (111 / 200) c) : B (172994723214241458003 / 20000000000000000) (174672791234885832717 / 20000000000000000) (((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) := bmul sGlobal41_hz56 (sGlobal41_hz57 hc) (by norm_num) (by norm_num)

theorem sGlobal41_hz59 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (4 : ℝ)) sGlobal41_hz10 (by norm_num) (by norm_num)

theorem sGlobal41_hz60 {c : ℝ} (hc : B (11 / 20) (111 / 200) c) : B (864973550631534488379 / 100000000000000000) (4366819453673781809747 / 500000000000000000) ((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bsub (sGlobal41_hz58 hc) sGlobal41_hz59 (by norm_num) (by norm_num)

theorem sGlobal41_hz61 {c : ℝ} (hc : B (11 / 20) (111 / 200) c) : B (46501977125481839247 / 500000000000000000) (93453940031159540297 / 1000000000000000000) (√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) := bsqrt (sGlobal41_hz60 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal41_hz62 : B (30670756373515103 / 125000000000000000) (122683025494060423 / 500000000000000000) ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal41_hz7 (by norm_num) (by norm_num)

theorem sGlobal41_hz63 {c : ℝ} (hc : B (11 / 20) (111 / 200) c) : B (5797411762498472353 / 62500000000000000) (93208573980171419473 / 1000000000000000000) ((√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) - ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))))) := bsub (sGlobal41_hz61 hc) sGlobal41_hz62 (by norm_num) (by norm_num)

theorem sGlobal41_hz64 {c : ℝ} (hc : B (11 / 20) (111 / 200) c) : B (5797411762498472353 / 62500000000000000) (93208573980171419473 / 1000000000000000000) (s3dm 12225 46 c) := by
    convert (sGlobal41_hz63 hc) using 1 <;>
      norm_num [s3dm, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal41_hz65 : B (6126072185528622723889 / 500000000000000000) (2450428874211449090087 / 200000000000000000) ((s3ap 12225 46)^2) := bsq sGlobal41_hz9 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal41_hz66 : B (6126072185528622723889 / 250000000000000000) (2450428874211449090087 / 100000000000000000) ((2 : ℝ) * ((s3ap 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal41_hz65 (by norm_num) (by norm_num)

theorem sGlobal41_hz67 {c : ℝ} (hc : B (11 / 20) (111 / 200) c) : B (268879865151645148871 / 31250000000000000) (4343919131708544284831 / 500000000000000000) ((s3dm 12225 46 c)^2) := bsq (sGlobal41_hz64 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal41_hz68 {c : ℝ} (hc : B (11 / 20) (111 / 200) c) : B (7908225239348701162947 / 500000000000000000) (7950066528630923068499 / 500000000000000000) (((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) := bsub sGlobal41_hz66 (sGlobal41_hz67 hc) (by norm_num) (by norm_num)

theorem sGlobal41_hz69 : B (1524735695971823534271 / 125000000000000000) (609894278388729413841 / 50000000000000000) ((s3am 12225 46)^2) := bsq sGlobal41_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal41_hz70 : B (1524735695971823534271 / 62500000000000000) (609894278388729413841 / 25000000000000000) ((2 : ℝ) * ((s3am 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal41_hz69 (by norm_num) (by norm_num)

theorem sGlobal41_hz71 {c : ℝ} (hc : B (11 / 20) (111 / 200) c) : B (20260235870923511 / 31250000000000000) (651757756248680109 / 1000000000000000000) ((((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) / ((2 : ℝ) * ((s3am 12225 46)^2))) := bdiv (sGlobal41_hz68 hc) sGlobal41_hz70 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal41_hz72 {c : ℝ} (hc : B (11 / 20) (111 / 200) c) : B (20260235870923511 / 31250000000000000) (651757756248680109 / 1000000000000000000) (s3c1 12225 46 c) := by
    convert (sGlobal41_hz71 hc) using 1 <;>
      norm_num [s3c1] <;> ring

theorem sGlobal41_hz73 {c : ℝ} (hc : B (11 / 20) (111 / 200) c) : B (27414891770940381 / 40000000000000000) (687281748785700763 / 1000000000000000000) (kdot c) := bkdot (sGlobal41_hz38 hc) sGlobal41_hz39.1 sGlobal41_hz47.2

theorem sGlobal41_hz74 : B (724531247304300811 / 1000000000000000000) (362265623652150407 / 500000000000000000) (kdot ((20260235870923511 / 31250000000000000))) := by
    constructor
    · apply bkdot_lower (q := (18475976778067333 / 40000000000000000)) (a := (216352652440588031 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (115474854862920831 / 250000000000000000)) (a := (432705304881176059 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal41_hz75 : B (362984057308959203 / 500000000000000000) (725968114617918409 / 1000000000000000000) (kdot ((651757756248680109 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (14348865688951563 / 31250000000000000)) (a := (430448278982853893 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (91832740409290003 / 200000000000000000)) (a := (43044827898285389 / 100000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal41_hz76 {c : ℝ} (hc : B (11 / 20) (111 / 200) c) : B (724531247304300811 / 1000000000000000000) (725968114617918409 / 1000000000000000000) (kdot (s3c1 12225 46 c)) := bkdot (sGlobal41_hz72 hc) sGlobal41_hz74.1 sGlobal41_hz75.2

theorem sGlobal41_hz77 {c : ℝ} (hc : B (11 / 20) (111 / 200) c) : B (121 / 400) (12321 / 40000) (c^2) := bsq (sGlobal41_hz38 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal41_hz78 {c : ℝ} (hc : B (11 / 20) (111 / 200) c) : B (27679 / 40000) (279 / 400) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (sGlobal41_hz77 hc) (by norm_num) (by norm_num)

theorem sGlobal41_hz79 {c : ℝ} (hc : B (11 / 20) (111 / 200) c) : B (103981293389724673 / 125000000000000000) (835164654424503289 / 1000000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (sGlobal41_hz78 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal41_hz80 : B (39119999999999765769 / 1600000000000000) (3912000000000000489 / 160000000000000) ((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (149450625 : ℝ)) sGlobal41_hz10 (by norm_num) (by norm_num)

theorem sGlobal41_hz81 {c : ℝ} (hc : B (11 / 20) (111 / 200) c) : B (285063590448170037 / 500000000000000000) (573993424216878061 / 1000000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (sGlobal41_hz79 hc) (sGlobal41_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal41_hz82 {c : ℝ} (hc : B (11 / 20) (111 / 200) c) : B (13939609572915431345887 / 1000000000000000000) (7017069611051335172859 / 500000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) := bmul sGlobal41_hz80 (sGlobal41_hz81 hc) (by norm_num) (by norm_num)

theorem sGlobal41_hz83 {c : ℝ} (hc : B (11 / 20) (111 / 200) c) : B (6969804786457715672943 / 1000000000000000000) (7017069611051335172859 / 1000000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) / (2 : ℝ)) := bdiv (sGlobal41_hz82 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal41_hz84 {c : ℝ} (hc : B (11 / 20) (111 / 200) c) : B (6969804786457715672943 / 1000000000000000000) (7017069611051335172859 / 1000000000000000000) (s3Cpa 12225 c) := by
    convert (sGlobal41_hz83 hc) using 1 <;>
      norm_num [s3Cpa, mA] <;> ring

theorem sGlobal41_hz85 {c : ℝ} (hc : B (11 / 20) (111 / 200) c) : B (264786189313012847 / 1000000000000000000) (265841166094588511 / 1000000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (sGlobal41_hz79 hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal41_hz86 {c : ℝ} (hc : B (11 / 20) (111 / 200) c) : B (188477380925215119 / 500000000000000000) (95360342644015981 / 250000000000000000) (c * (kdot c)) := bmul (sGlobal41_hz38 hc) (sGlobal41_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal41_hz87 {c : ℝ} (hc : B (11 / 20) (111 / 200) c) : B (-116655181263051077 / 1000000000000000000) (-111113595755841727 / 1000000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (sGlobal41_hz85 hc) (sGlobal41_hz86 hc) (by norm_num) (by norm_num)

theorem sGlobal41_hz88 {c : ℝ} (hc : B (11 / 20) (111 / 200) c) : B (-1426109590940799594589 / 500000000000000000) (-339590927028789244843 / 125000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) := bmul sGlobal41_hz80 (sGlobal41_hz87 hc) (by norm_num) (by norm_num)

theorem sGlobal41_hz89 {c : ℝ} (hc : B (11 / 20) (111 / 200) c) : B (-1426109590940799594589 / 1000000000000000000) (-339590927028789244843 / 250000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) / (2 : ℝ)) := bdiv (sGlobal41_hz88 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal41_hz90 {c : ℝ} (hc : B (11 / 20) (111 / 200) c) : B (-1426109590940799594589 / 1000000000000000000) (-339590927028789244843 / 250000000000000000) (s3Cpp 12225 c) := by
    convert (sGlobal41_hz89 hc) using 1 <;>
      norm_num [s3Cpp, mA] <;> ring

theorem sGlobal41_hz91 {c : ℝ} (hc : B (11 / 20) (111 / 200) c) : B (221404684262232918167 / 31250000000000000) (1426442944197014717017 / 200000000000000000) ((s3Cpa 12225 c) + (s3r1 12225 46)) := badd (sGlobal41_hz84 hc) sGlobal41_hz33 (by norm_num) (by norm_num)

theorem sGlobal41_hz92 {c : ℝ} (hc : B (11 / 20) (111 / 200) c) : B (64149681717967776073 / 1000000000000000000) (32288817210156152433 / 500000000000000000) (((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) := bdiv (sGlobal41_hz91 hc) sGlobal41_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal41_hz93 {c : ℝ} (hc : B (11 / 20) (111 / 200) c) : B (12854472948692367297 / 200000000000000000) (64700317445806365289 / 1000000000000000000) ((((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) + (s3e0 12225 46)) := badd (sGlobal41_hz92 hc) sGlobal41_hz16 (by norm_num) (by norm_num)

theorem sGlobal41_hz94 {c : ℝ} (hc : B (11 / 20) (111 / 200) c) : B (12854472948692367297 / 200000000000000000) (64700317445806365289 / 1000000000000000000) (s3Lam 12225 46 c) := by
    convert (sGlobal41_hz93 hc) using 1 <;>
      norm_num [s3Lam] <;> ring

theorem sGlobal41_hz95 {c : ℝ} (hc : B (11 / 20) (111 / 200) c) : B (-1349346184318307788989 / 1000000000000000000) (-640800150746332352277 / 500000000000000000) ((s3Cpp 12225 c) + (s3rpp 12225 46)) := badd (sGlobal41_hz90 hc) sGlobal41_hz37 (by norm_num) (by norm_num)

theorem sGlobal41_hz96 {c : ℝ} (hc : B (11 / 20) (111 / 200) c) : B (-979582305396444128649 / 1000000000000000000) (-640800150746332352277 / 1000000000000000000) (if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) := bweaken (bfirst (sGlobal41_hz95 hc) (sGlobal41_hz76 hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem sGlobal41_hz97 {c : ℝ} (hc : B (11 / 20) (111 / 200) c) : B (12909177717864362819 / 3125000000000000) (523266384698514438547 / 125000000000000000) ((s3Lam 12225 46 c)^2) := bsq (sGlobal41_hz94 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal41_hz98 {c : ℝ} (hc : B (11 / 20) (111 / 200) c) : B (52541076165818337 / 125000000000000000) (106197043207578479 / 250000000000000000) ((s3c1 12225 46 c)^2) := bsq (sGlobal41_hz72 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal41_hz99 {c : ℝ} (hc : B (11 / 20) (111 / 200) c) : B (143802956792421521 / 250000000000000000) (72458923834181663 / 125000000000000000) ((1 : ℝ) - ((s3c1 12225 46 c)^2)) := bsub (bpoint (1 : ℝ)) (sGlobal41_hz98 hc) (by norm_num) (by norm_num)

theorem sGlobal41_hz100 {c : ℝ} (hc : B (11 / 20) (111 / 200) c) : B (151685441248616353 / 200000000000000000) (380680768713581493 / 500000000000000000) (√((1 : ℝ) - ((s3c1 12225 46 c)^2))) := bsqrt (sGlobal41_hz99 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal41_hz101 {c : ℝ} (hc : B (11 / 20) (111 / 200) c) : B (2382669339415896643 / 1000000000000000000) (2391887812707005647 / 1000000000000000000) (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))) := bmul pi_mem (sGlobal41_hz100 hc) (by norm_num) (by norm_num)

theorem sGlobal41_hz102 {c : ℝ} (hc : B (11 / 20) (111 / 200) c) : B (1727061297679104529801 / 1000000000000000000) (1756908106524899267533 / 1000000000000000000) (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2))))) := bdiv (sGlobal41_hz97 hc) (sGlobal41_hz101 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal41_hz103 {c : ℝ} (hc : B (11 / 20) (111 / 200) c) : B (182489988350258887 / 244140625000000) (139513494472320864407 / 125000000000000000) ((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) := badd (sGlobal41_hz96 hc) (sGlobal41_hz102 hc) (by norm_num) (by norm_num)

theorem sGlobal41_hz104 : B (3762781186094069 / 250000000000000000) (376278118609407 / 25000000000000000) ((s3e0 12225 46)^2) := bsq sGlobal41_hz16 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal41_hz105 {c : ℝ} (hc : B (11 / 20) (111 / 200) c) : B (186873510851851194357 / 250000000000000000) (69757687931456955721 / 62500000000000000) (((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) := badd (sGlobal41_hz103 hc) sGlobal41_hz104 (by norm_num) (by norm_num)

theorem sGlobal41_hz106 {c : ℝ} (hc : B (11 / 20) (111 / 200) c) : B (785991116858652047559 / 1000000000000000000) (72163755022339722597 / 62500000000000000) ((((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) + (s3rs 12225 46 maskSlack)) := badd (sGlobal41_hz105 hc) sGlobal41_hz29 (by norm_num) (by norm_num)

theorem sGlobal41_hz107 {c : ℝ} (hc : B (11 / 20) (111 / 200) c) : B (785991116858652047559 / 1000000000000000000) (72163755022339722597 / 62500000000000000) (s3U 12225 46 maskSlack c) := by
    convert (sGlobal41_hz106 hc) using 1 <;>
      norm_num [s3U] <;> ring

theorem sGlobal41_hz108 {c : ℝ} (hc : B (11 / 20) (111 / 200) c) : B (-1502872997563291869407 / 1000000000000000000) (-358781778684412196243 / 250000000000000000) ((s3Cpp 12225 c) - (s3rpp 12225 46)) := bsub (sGlobal41_hz90 hc) sGlobal41_hz37 (by norm_num) (by norm_num)

theorem sGlobal41_hz109 {c : ℝ} (hc : B (11 / 20) (111 / 200) c) : B (-1502872997563291869407 / 1000000000000000000) (-358781778684412196243 / 250000000000000000) (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ)) := bweaken (bmin (sGlobal41_hz108 hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem sGlobal41_hz110 {c : ℝ} (hc : B (11 / 20) (111 / 200) c) : B (-1091037876551202485649 / 1000000000000000000) (-519897219240545548463 / 500000000000000000) ((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) := bmul (sGlobal41_hz76 hc) (sGlobal41_hz109 hc) (by norm_num) (by norm_num)

theorem sGlobal41_hz111 {c : ℝ} (hc : B (11 / 20) (111 / 200) c) : B (-1091052927675946861929 / 1000000000000000000) (-519904744802917736601 / 500000000000000000) (((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) := bsub (sGlobal41_hz110 hc) sGlobal41_hz104 (by norm_num) (by norm_num)

theorem sGlobal41_hz112 {c : ℝ} (hc : B (11 / 20) (111 / 200) c) : B (-225910000226014226389 / 200000000000000000) (-1078306563057082743333 / 1000000000000000000) ((((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) - (s3rs 12225 46 maskSlack)) := bsub (sGlobal41_hz111 hc) sGlobal41_hz29 (by norm_num) (by norm_num)

theorem sGlobal41_hz113 {c : ℝ} (hc : B (11 / 20) (111 / 200) c) : B (-225910000226014226389 / 200000000000000000) (-1078306563057082743333 / 1000000000000000000) (s3L 12225 46 maskSlack c) := by
    convert (sGlobal41_hz112 hc) using 1 <;>
      norm_num [s3L] <;> ring

theorem sGlobal41_hz114 {c : ℝ} (hc : B (11 / 20) (111 / 200) c) : B 0 (72163755022339722597 / 62500000000000000) |(s3U 12225 46 maskSlack c)| := bweaken (babs (sGlobal41_hz107 hc)) (by norm_num) (by norm_num)

theorem sGlobal41_hz115 {c : ℝ} (hc : B (11 / 20) (111 / 200) c) : B 0 (225910000226014226389 / 200000000000000000) |(s3L 12225 46 maskSlack c)| := bweaken (babs (sGlobal41_hz113 hc)) (by norm_num) (by norm_num)

theorem sGlobal41_hz116 {c : ℝ} (hc : B (11 / 20) (111 / 200) c) : B 0 (72163755022339722597 / 62500000000000000) (max |(s3U 12225 46 maskSlack c)| |(s3L 12225 46 maskSlack c)|) := bweaken (bmax (sGlobal41_hz114 hc) (sGlobal41_hz115 hc)) (by norm_num) (by norm_num)

theorem sGlobal41_hz117 {c : ℝ} (hc : B (11 / 20) (111 / 200) c) : B 0 (72163755022339722597 / 62500000000000000) (s3nks 12225 46 maskSlack c) := by
    convert (sGlobal41_hz116 hc) using 1 <;>
      norm_num [s3nks] <;> ring

theorem sGlobal41 {c : ℝ} (hc : B (11 / 20) (111 / 200) c) :
    0 < s3am 12225 46 ∧ 0 ≤ s3dm 12225 46 c ∧
    s3dm 12225 46 c ^ 2 ≤ 2 * s3ap 12225 46 ^ 2 ∧ s3c1 12225 46 c < 1 ∧
    0 ≤ s3Cpa 12225 c - s3r1 12225 46 ∧
    s3e0 12225 46 ≤ (s3Cpa 12225 c - s3r1 12225 46) / s3ap 12225 46 ∧
    s3nks 12225 46 maskSlack c ≤ 12225 * (5903 / 62500) := by

  refine ⟨lt_of_lt_of_le (by norm_num) sGlobal41_hz14.1,
    le_trans (by norm_num) (sGlobal41_hz64 hc).1, ?_,
    lt_of_le_of_lt (sGlobal41_hz72 hc).2 (by norm_num), ?_, ?_,
    le_trans (sGlobal41_hz117 hc).2 (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (sGlobal41_hz64 hc).1) (sGlobal41_hz64 hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) sGlobal41_hz9.1 2
    nlinarith only [h1, h2]
  · linarith only [(sGlobal41_hz84 hc).1, sGlobal41_hz33.2]
  · have hap : 0 < s3ap 12225 46 := lt_of_lt_of_le (by norm_num) sGlobal41_hz9.1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul sGlobal41_hz16.2 sGlobal41_hz9.2 (le_trans (by norm_num) sGlobal41_hz9.1) (by norm_num)
    linarith only [h, (sGlobal41_hz84 hc).1, sGlobal41_hz33.2]

end BstLean.Part255
