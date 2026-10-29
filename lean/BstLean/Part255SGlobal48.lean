import BstLean.Part255SGlobal44
import BstLean.Part255Numeric10
namespace BstLean.Part255
open Real BstLean.Part130 BstLean.Part182 BstLean.Part197 BstLean.Part246
theorem sGlobal48_hz0 : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal48_hz1 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) ((√(23 : ℝ)) / (12225 : ℝ)) := bdiv sGlobal48_hz0 (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal48_hz2 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) maskSlack := by
    convert sGlobal48_hz1 using 1 <;>
      norm_num [maskSlack] <;> ring

theorem sGlobal48_hz3 : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal48_hz4 : B (6395294793910793 / 500000000000000000) (12790589587821587 / 1000000000000000000) (√((2 / 12225) : ℝ)) := bsqrt (bpoint ((2 / 12225) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal48_hz5 : B (7230130686979 / 62500000000000000) (23136418198333 / 200000000000000000) (√((2 / 149450625) : ℝ)) := bsqrt (bpoint ((2 / 149450625) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal48_hz6 : B (2211334438749598093 / 20000000000000000) (110566721937479904651 / 1000000000000000000) (√(12225 : ℝ)) := bsqrt (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal48_hz7 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))) := bmul sGlobal48_hz3 sGlobal48_hz4 (by norm_num) (by norm_num)

theorem sGlobal48_hz8 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) ((√(12225 : ℝ)) + ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := badd sGlobal48_hz6 sGlobal48_hz7 (by norm_num) (by norm_num)

theorem sGlobal48_hz9 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) (s3ap 12225 46) := by
    convert sGlobal48_hz8 using 1 <;>
      norm_num [s3ap, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal48_hz10 : B (163599182004089 / 1000000000000000000) (16359918200409 / 100000000000000000) ((2 : ℝ) / (12225 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal48_hz11 : B (1222499983640081799591 / 100000000000000000) (12224999836400817995911 / 1000000000000000000) ((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ))) := bsub (bpoint (12225 : ℝ)) sGlobal48_hz10 (by norm_num) (by norm_num)

theorem sGlobal48_hz12 : B (110566721197658827907 / 1000000000000000000) (27641680299414706977 / 250000000000000000) (√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) := bsqrt sGlobal48_hz11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal48_hz13 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) ((√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) - ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bsub sGlobal48_hz12 sGlobal48_hz7 (by norm_num) (by norm_num)

theorem sGlobal48_hz14 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) (s3am 12225 46) := by
    convert sGlobal48_hz13 using 1 <;>
      norm_num [s3am, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal48_hz15 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√((2 / 12225) : ℝ)) * (√(92 : ℝ))) := bmul sGlobal48_hz4 sGlobal48_hz3 (by norm_num) (by norm_num)

theorem sGlobal48_hz16 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) (s3e0 12225 46) := by
    convert sGlobal48_hz15 using 1 <;>
      norm_num [s3e0, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal48_hz17 : B (250196148528560847 / 500000000000000000) (100078459411424339 / 200000000000000000) (((1 / 2) : ℝ) + maskSlack) := badd (bpoint ((1 / 2) : ℝ)) sGlobal48_hz2 (by norm_num) (by norm_num)

theorem sGlobal48_hz18 : B (59827153232297998295487 / 800000000000000) (23930861292919199366019 / 320000000000000) ((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack)) := bmul (bpoint (149450625 : ℝ)) sGlobal48_hz17 (by norm_num) (by norm_num)

theorem sGlobal48_hz19 : B (1729554180017180009583 / 200000000000000000) (8647770900085900056557 / 1000000000000000000) (√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) := bsqrt sGlobal48_hz18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal48_hz20 : B (4328681281566262743499 / 500000000000000000) (8657362563132525495641 / 1000000000000000000) ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))) := badd sGlobal48_hz19 sGlobal48_hz3 (by norm_num) (by norm_num)

theorem sGlobal48_hz21 : B (110732771457999278473 / 1000000000000000000) (55366385728999643621 / 500000000000000000) ((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ)))) := bmul sGlobal48_hz4 sGlobal48_hz20 (by norm_num) (by norm_num)

theorem sGlobal48_hz22 : B (209099159 / 15625000000000000) (13382346177 / 1000000000000000000) ((2 : ℝ) / (149450625 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (149450625 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal48_hz23 : B (2452349334953899930479 / 200000000000000000) (12261746674769501594427 / 1000000000000000000) (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2) := bsq sGlobal48_hz21 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal48_hz24 : B (82045469362091 / 500000000000000000) (32818187747289 / 200000000000000000) (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2)) := bmul sGlobal48_hz22 sGlobal48_hz23 (by norm_num) (by norm_num)

theorem sGlobal48_hz25 : B (82045469362091 / 250000000000000000) (32818187747289 / 100000000000000000) ((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) := bmul (bpoint (2 : ℝ)) sGlobal48_hz24 (by norm_num) (by norm_num)

theorem sGlobal48_hz26 : B (117258080744995992792057 / 1000000000000000000) (58629040372497996396029 / 500000000000000000) (√(13749457500 : ℝ)) := bsqrt (bpoint (13749457500 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal48_hz27 : B (117304080744995992792057 / 1000000000000000000) (58652040372497996396029 / 500000000000000000) ((√(13749457500 : ℝ)) + (46 : ℝ)) := badd sGlobal48_hz26 (bpoint (46 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal48_hz28 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal48_hz25 sGlobal48_hz27 (by norm_num) (by norm_num)

theorem sGlobal48_hz29 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (s3rs 12225 46 maskSlack) := by
    convert sGlobal48_hz28 using 1 <;>
      norm_num [s3rs, s3pp, s3K, mA, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal48_hz30 : B (490797546012267 / 1000000000000000000) (49079754601227 / 100000000000000000) ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (3 : ℝ)) sGlobal48_hz10 (by norm_num) (by norm_num)

theorem sGlobal48_hz31 : B (490797546012267 / 500000000000000000) (49079754601227 / 50000000000000000) ((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal48_hz30 (by norm_num) (by norm_num)

theorem sGlobal48_hz32 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal48_hz31 sGlobal48_hz27 (by norm_num) (by norm_num)

theorem sGlobal48_hz33 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (s3r1 12225 46) := by
    convert sGlobal48_hz32 using 1 <;>
      norm_num [s3r1, mA] <;> ring

theorem sGlobal48_hz34 : B (163599182004089 / 500000000000000000) (16359918200409 / 50000000000000000) ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (2 : ℝ)) sGlobal48_hz10 (by norm_num) (by norm_num)

theorem sGlobal48_hz35 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal48_hz34 (by norm_num) (by norm_num)

theorem sGlobal48_hz36 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal48_hz35 sGlobal48_hz27 (by norm_num) (by norm_num)

theorem sGlobal48_hz37 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (s3rpp 12225 46) := by
    convert sGlobal48_hz36 using 1 <;>
      norm_num [s3rpp, mA] <;> ring

theorem sGlobal48_hz38 {c : ℝ} (hc : B (117 / 200) (59 / 100) c) : B (117 / 200) (59 / 100) c := hc

theorem sGlobal48_hz39 : B (698905500064522689 / 1000000000000000000) (139781100012904567 / 200000000000000000) (kdot ((117 / 200))) := by
    constructor
    · apply bkdot_lower (q := (511692928421768817 / 1000000000000000000)) (a := (118239533629198499 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (31980808026360551 / 62500000000000000)) (a := (472958134516793769 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal48_hz40 : B (13689 / 40000) (13689 / 40000) (((117 / 200) : ℝ)^2) := bsq (bpoint ((117 / 200) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal48_hz41 : B (26311 / 40000) (26311 / 40000) ((1 : ℝ) - (((117 / 200) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal48_hz40 (by norm_num) (by norm_num)

theorem sGlobal48_hz42 : B (405516645774251787 / 500000000000000000) (32441331661940143 / 40000000000000000) (√((1 : ℝ) - (((117 / 200) : ℝ)^2))) := bsqrt sGlobal48_hz41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal48_hz43 : B (258159914724069289 / 1000000000000000000) (25815991472406929 / 100000000000000000) ((√((1 : ℝ) - (((117 / 200) : ℝ)^2))) / Real.pi) := bdiv sGlobal48_hz42 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal48_hz44 : B (408859717537745773 / 1000000000000000000) (408859717537745859 / 1000000000000000000) (((117 / 200) : ℝ) * (kdot ((117 / 200)))) := bmul (bpoint ((117 / 200) : ℝ)) sGlobal48_hz39 (by norm_num) (by norm_num)

theorem sGlobal48_hz45 : B (333509816130907531 / 500000000000000000) (667019632261815149 / 1000000000000000000) (((√((1 : ℝ) - (((117 / 200) : ℝ)^2))) / Real.pi) + (((117 / 200) : ℝ) * (kdot ((117 / 200))))) := badd sGlobal48_hz43 sGlobal48_hz44 (by norm_num) (by norm_num)

theorem sGlobal48_hz46 : B (333509816130907531 / 500000000000000000) (667019632261815149 / 1000000000000000000) (kappa ((117 / 200))) := by rw [kappa_eq]; exact sGlobal48_hz45

theorem sGlobal48_hz47 : B (350436133891663427 / 500000000000000000) (140174453556665391 / 200000000000000000) (kdot ((59 / 100))) := by
    constructor
    · apply bkdot_lower (q := (253900391502320151 / 500000000000000000)) (a := (117467185752109409 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (507800783004640301 / 1000000000000000000)) (a := (469868743008437479 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal48_hz48 : B (3481 / 10000) (3481 / 10000) (((59 / 100) : ℝ)^2) := bsq (bpoint ((59 / 100) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal48_hz49 : B (6519 / 10000) (6519 / 10000) ((1 : ℝ) - (((59 / 100) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal48_hz48 (by norm_num) (by norm_num)

theorem sGlobal48_hz50 : B (403701622488689039 / 500000000000000000) (807403244977378079 / 1000000000000000000) (√((1 : ℝ) - (((59 / 100) : ℝ)^2))) := bsqrt sGlobal48_hz49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal48_hz51 : B (257004435013172473 / 1000000000000000000) (128502217506586237 / 500000000000000000) ((√((1 : ℝ) - (((59 / 100) : ℝ)^2))) / Real.pi) := bdiv sGlobal48_hz50 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal48_hz52 : B (413514637992162843 / 1000000000000000000) (51689329749020363 / 125000000000000000) (((59 / 100) : ℝ) * (kdot ((59 / 100)))) := bmul (bpoint ((59 / 100) : ℝ)) sGlobal48_hz47 (by norm_num) (by norm_num)

theorem sGlobal48_hz53 : B (167629768251333829 / 250000000000000000) (335259536502667689 / 500000000000000000) (((√((1 : ℝ) - (((59 / 100) : ℝ)^2))) / Real.pi) + (((59 / 100) : ℝ) * (kdot ((59 / 100))))) := badd sGlobal48_hz51 sGlobal48_hz52 (by norm_num) (by norm_num)

theorem sGlobal48_hz54 : B (167629768251333829 / 250000000000000000) (335259536502667689 / 500000000000000000) (kappa ((59 / 100))) := by rw [kappa_eq]; exact sGlobal48_hz53

theorem sGlobal48_hz55 {c : ℝ} (hc : B (117 / 200) (59 / 100) c) : B (333509816130907531 / 500000000000000000) (335259536502667689 / 500000000000000000) (kappa c) := bkappa (sGlobal48_hz38 hc) (by norm_num) (by norm_num) sGlobal48_hz46.1 sGlobal48_hz54.2

theorem sGlobal48_hz56 : B 24450 24450 ((2 : ℝ) * (12225 : ℝ)) := bmul (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal48_hz57 {c : ℝ} (hc : B (117 / 200) (59 / 100) c) : B (164740463497332311 / 500000000000000000) (166490183869092469 / 500000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (sGlobal48_hz55 hc) (by norm_num) (by norm_num)

theorem sGlobal48_hz58 {c : ℝ} (hc : B (117 / 200) (59 / 100) c) : B (80558086650195500079 / 10000000000000000) (81413699911986217341 / 10000000000000000) (((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) := bmul sGlobal48_hz56 (sGlobal48_hz57 hc) (by norm_num) (by norm_num)

theorem sGlobal48_hz59 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (4 : ℝ)) sGlobal48_hz10 (by norm_num) (by norm_num)

theorem sGlobal48_hz60 {c : ℝ} (hc : B (117 / 200) (59 / 100) c) : B (402790400531141099577 / 50000000000000000) (508835583550118357359 / 62500000000000000) ((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bsub (sGlobal48_hz58 hc) sGlobal48_hz59 (by norm_num) (by norm_num)

theorem sGlobal48_hz61 {c : ℝ} (hc : B (117 / 200) (59 / 100) c) : B (89754153166429139851 / 1000000000000000000) (90229536942189245161 / 1000000000000000000) (√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) := bsqrt (sGlobal48_hz60 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal48_hz62 : B (30670756373515103 / 125000000000000000) (122683025494060423 / 500000000000000000) ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal48_hz7 (by norm_num) (by norm_num)

theorem sGlobal48_hz63 {c : ℝ} (hc : B (117 / 200) (59 / 100) c) : B (17901757423088203801 / 200000000000000000) (89984170891201124337 / 1000000000000000000) ((√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) - ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))))) := bsub (sGlobal48_hz61 hc) sGlobal48_hz62 (by norm_num) (by norm_num)

theorem sGlobal48_hz64 {c : ℝ} (hc : B (117 / 200) (59 / 100) c) : B (17901757423088203801 / 200000000000000000) (89984170891201124337 / 1000000000000000000) (s3dm 12225 46 c) := by
    convert (sGlobal48_hz63 hc) using 1 <;>
      norm_num [s3dm, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal48_hz65 : B (6126072185528622723889 / 500000000000000000) (2450428874211449090087 / 200000000000000000) ((s3ap 12225 46)^2) := bsq sGlobal48_hz9 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal48_hz66 : B (6126072185528622723889 / 250000000000000000) (2450428874211449090087 / 100000000000000000) ((2 : ℝ) * ((s3ap 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal48_hz65 (by norm_num) (by norm_num)

theorem sGlobal48_hz67 {c : ℝ} (hc : B (117 / 200) (59 / 100) c) : B (8011822970877340175689 / 1000000000000000000) (8097151010976887747303 / 1000000000000000000) ((s3dm 12225 46 c)^2) := bsq (sGlobal48_hz64 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal48_hz68 {c : ℝ} (hc : B (117 / 200) (59 / 100) c) : B (16407137731137603148253 / 1000000000000000000) (16492465771237150725181 / 1000000000000000000) (((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) := bsub sGlobal48_hz66 (sGlobal48_hz67 hc) (by norm_num) (by norm_num)

theorem sGlobal48_hz69 : B (1524735695971823534271 / 125000000000000000) (609894278388729413841 / 50000000000000000) ((s3am 12225 46)^2) := bsq sGlobal48_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal48_hz70 : B (1524735695971823534271 / 62500000000000000) (609894278388729413841 / 25000000000000000) ((2 : ℝ) * ((s3am 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal48_hz69 (by norm_num) (by norm_num)

theorem sGlobal48_hz71 {c : ℝ} (hc : B (117 / 200) (59 / 100) c) : B (672540238223064467 / 1000000000000000000) (676037895240153333 / 1000000000000000000) ((((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) / ((2 : ℝ) * ((s3am 12225 46)^2))) := bdiv (sGlobal48_hz68 hc) sGlobal48_hz70 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal48_hz72 {c : ℝ} (hc : B (117 / 200) (59 / 100) c) : B (672540238223064467 / 1000000000000000000) (676037895240153333 / 1000000000000000000) (s3c1 12225 46 c) := by
    convert (sGlobal48_hz71 hc) using 1 <;>
      norm_num [s3c1] <;> ring

theorem sGlobal48_hz73 {c : ℝ} (hc : B (117 / 200) (59 / 100) c) : B (698905500064522689 / 1000000000000000000) (140174453556665391 / 200000000000000000) (kdot c) := bkdot (sGlobal48_hz38 hc) sGlobal48_hz39.1 sGlobal48_hz47.2

theorem sGlobal48_hz74 : B (183699202292431047 / 250000000000000000) (73479680916972419 / 100000000000000000) (kdot ((672540238223064467 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (3456851422246203 / 7812500000000000)) (a := (208290099005241627 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (442476982047513983 / 1000000000000000000)) (a := (104145049502620813 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal48_hz75 : B (736304448225708941 / 1000000000000000000) (736304448225708943 / 1000000000000000000) (kdot ((676037895240153333 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (439648088260175573 / 1000000000000000000)) (a := (414212004119209879 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (109912022065043893 / 250000000000000000)) (a := (414212004119209877 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal48_hz76 {c : ℝ} (hc : B (117 / 200) (59 / 100) c) : B (183699202292431047 / 250000000000000000) (736304448225708943 / 1000000000000000000) (kdot (s3c1 12225 46 c)) := bkdot (sGlobal48_hz72 hc) sGlobal48_hz74.1 sGlobal48_hz75.2

theorem sGlobal48_hz77 {c : ℝ} (hc : B (117 / 200) (59 / 100) c) : B (13689 / 40000) (3481 / 10000) (c^2) := bsq (sGlobal48_hz38 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal48_hz78 {c : ℝ} (hc : B (117 / 200) (59 / 100) c) : B (6519 / 10000) (26311 / 40000) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (sGlobal48_hz77 hc) (by norm_num) (by norm_num)

theorem sGlobal48_hz79 {c : ℝ} (hc : B (117 / 200) (59 / 100) c) : B (403701622488689039 / 500000000000000000) (32441331661940143 / 40000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (sGlobal48_hz78 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal48_hz80 : B (39119999999999765769 / 1600000000000000) (3912000000000000489 / 160000000000000) ((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (149450625 : ℝ)) sGlobal48_hz10 (by norm_num) (by norm_num)

theorem sGlobal48_hz81 {c : ℝ} (hc : B (117 / 200) (59 / 100) c) : B (282149284342316371 / 500000000000000000) (14210768557384397 / 25000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (sGlobal48_hz79 hc) (sGlobal48_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal48_hz82 {c : ℝ} (hc : B (117 / 200) (59 / 100) c) : B (13797100004339187931763 / 1000000000000000000) (13898131649121942003267 / 1000000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) := bmul sGlobal48_hz80 (sGlobal48_hz81 hc) (by norm_num) (by norm_num)

theorem sGlobal48_hz83 {c : ℝ} (hc : B (117 / 200) (59 / 100) c) : B (6898550002169593965881 / 1000000000000000000) (3474532912280485500817 / 500000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) / (2 : ℝ)) := bdiv (sGlobal48_hz82 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal48_hz84 {c : ℝ} (hc : B (117 / 200) (59 / 100) c) : B (6898550002169593965881 / 1000000000000000000) (3474532912280485500817 / 500000000000000000) (s3Cpa 12225 c) := by
    convert (sGlobal48_hz83 hc) using 1 <;>
      norm_num [s3Cpa, mA] <;> ring

theorem sGlobal48_hz85 {c : ℝ} (hc : B (117 / 200) (59 / 100) c) : B (257004435013172473 / 1000000000000000000) (25815991472406929 / 100000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (sGlobal48_hz79 hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal48_hz86 {c : ℝ} (hc : B (117 / 200) (59 / 100) c) : B (408859717537745773 / 1000000000000000000) (51689329749020363 / 125000000000000000) (c * (kdot c)) := bmul (sGlobal48_hz38 hc) (sGlobal48_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal48_hz87 {c : ℝ} (hc : B (117 / 200) (59 / 100) c) : B (-156510202978990431 / 1000000000000000000) (-150699802813676483 / 1000000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (sGlobal48_hz85 hc) (sGlobal48_hz86 hc) (by norm_num) (by norm_num)

theorem sGlobal48_hz88 {c : ℝ} (hc : B (117 / 200) (59 / 100) c) : B (-765334892567263303257 / 200000000000000000) (-1842305089397183973873 / 500000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) := bmul sGlobal48_hz80 (sGlobal48_hz87 hc) (by norm_num) (by norm_num)

theorem sGlobal48_hz89 {c : ℝ} (hc : B (117 / 200) (59 / 100) c) : B (-1913337231418158258143 / 1000000000000000000) (-1842305089397183973873 / 1000000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) / (2 : ℝ)) := bdiv (sGlobal48_hz88 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal48_hz90 {c : ℝ} (hc : B (117 / 200) (59 / 100) c) : B (-1913337231418158258143 / 1000000000000000000) (-1842305089397183973873 / 1000000000000000000) (s3Cpp 12225 c) := by
    convert (sGlobal48_hz89 hc) using 1 <;>
      norm_num [s3Cpp, mA] <;> ring

theorem sGlobal48_hz91 {c : ℝ} (hc : B (117 / 200) (59 / 100) c) : B (3506847556051665837141 / 500000000000000000) (353210546724735470693 / 50000000000000000) ((s3Cpa 12225 c) + (s3r1 12225 46)) := badd (sGlobal48_hz84 hc) sGlobal48_hz33 (by norm_num) (by norm_num)

theorem sGlobal48_hz92 {c : ℝ} (hc : B (117 / 200) (59 / 100) c) : B (63504515301858951973 / 1000000000000000000) (639619037062256193 / 10000000000000000) (((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) := bdiv (sGlobal48_hz91 hc) sGlobal48_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal48_hz93 {c : ℝ} (hc : B (117 / 200) (59 / 100) c) : B (12725439665470602477 / 200000000000000000) (64084586731719679723 / 1000000000000000000) ((((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) + (s3e0 12225 46)) := badd (sGlobal48_hz92 hc) sGlobal48_hz16 (by norm_num) (by norm_num)

theorem sGlobal48_hz94 {c : ℝ} (hc : B (117 / 200) (59 / 100) c) : B (12725439665470602477 / 200000000000000000) (64084586731719679723 / 1000000000000000000) (s3Lam 12225 46 c) := by
    convert (sGlobal48_hz93 hc) using 1 <;>
      norm_num [s3Lam] <;> ring

theorem sGlobal48_hz95 {c : ℝ} (hc : B (117 / 200) (59 / 100) c) : B (-1836573824795666452543 / 1000000000000000000) (-353108336554938339811 / 200000000000000000) ((s3Cpp 12225 c) + (s3rpp 12225 46)) := badd (sGlobal48_hz90 hc) sGlobal48_hz37 (by norm_num) (by norm_num)

theorem sGlobal48_hz96 {c : ℝ} (hc : B (117 / 200) (59 / 100) c) : B (-338069369172988259217 / 250000000000000000) (-882770841387345849527 / 1000000000000000000) (if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) := bweaken (bfirst (sGlobal48_hz95 hc) (sGlobal48_hz76 hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem sGlobal48_hz97 {c : ℝ} (hc : B (117 / 200) (59 / 100) c) : B (4048420366988313976993 / 1000000000000000000) (256677141035956376351 / 62500000000000000) ((s3Lam 12225 46 c)^2) := bsq (sGlobal48_hz94 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal48_hz98 {c : ℝ} (hc : B (117 / 200) (59 / 100) c) : B (452310372029136303 / 1000000000000000000) (457027235800736533 / 1000000000000000000) ((s3c1 12225 46 c)^2) := bsq (sGlobal48_hz72 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal48_hz99 {c : ℝ} (hc : B (117 / 200) (59 / 100) c) : B (542972764199263467 / 1000000000000000000) (547689627970863697 / 1000000000000000000) ((1 : ℝ) - ((s3c1 12225 46 c)^2)) := bsub (bpoint (1 : ℝ)) (sGlobal48_hz98 hc) (by norm_num) (by norm_num)

theorem sGlobal48_hz100 {c : ℝ} (hc : B (117 / 200) (59 / 100) c) : B (92108357061742729 / 125000000000000000) (370030278480985829 / 500000000000000000) (√((1 : ℝ) - ((s3c1 12225 46 c)^2))) := bsqrt (sGlobal48_hz99 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal48_hz101 {c : ℝ} (hc : B (117 / 200) (59 / 100) c) : B (289366937879396511 / 125000000000000000) (1162484404481650437 / 500000000000000000) (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))) := bmul pi_mem (sGlobal48_hz100 hc) (by norm_num) (by norm_num)

theorem sGlobal48_hz102 {c : ℝ} (hc : B (117 / 200) (59 / 100) c) : B (174127943195655035141 / 100000000000000000) (221757488015903948413 / 125000000000000000) (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2))))) := bdiv (sGlobal48_hz97 hc) (sGlobal48_hz101 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal48_hz103 {c : ℝ} (hc : B (117 / 200) (59 / 100) c) : B (194500977632298657271 / 500000000000000000) (891289062739885737777 / 1000000000000000000) ((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) := badd (sGlobal48_hz96 hc) (sGlobal48_hz102 hc) (by norm_num) (by norm_num)

theorem sGlobal48_hz104 : B (3762781186094069 / 250000000000000000) (376278118609407 / 25000000000000000) ((s3e0 12225 46)^2) := bsq sGlobal48_hz16 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal48_hz105 {c : ℝ} (hc : B (117 / 200) (59 / 100) c) : B (194508503194670845409 / 500000000000000000) (891304113864630114057 / 1000000000000000000) (((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) := badd (sGlobal48_hz103 hc) sGlobal48_hz104 (by norm_num) (by norm_num)

theorem sGlobal48_hz106 {c : ℝ} (hc : B (117 / 200) (59 / 100) c) : B (427514079840588960949 / 1000000000000000000) (929801187318754384073 / 1000000000000000000) ((((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) + (s3rs 12225 46 maskSlack)) := badd (sGlobal48_hz105 hc) sGlobal48_hz29 (by norm_num) (by norm_num)

theorem sGlobal48_hz107 {c : ℝ} (hc : B (117 / 200) (59 / 100) c) : B (427514079840588960949 / 1000000000000000000) (929801187318754384073 / 1000000000000000000) (s3U 12225 46 maskSlack c) := by
    convert (sGlobal48_hz106 hc) using 1 <;>
      norm_num [s3U] <;> ring

theorem sGlobal48_hz108 {c : ℝ} (hc : B (117 / 200) (59 / 100) c) : B (-1990100638040650532961 / 1000000000000000000) (-1919068496019675779473 / 1000000000000000000) ((s3Cpp 12225 c) - (s3rpp 12225 46)) := bsub (sGlobal48_hz90 hc) sGlobal48_hz37 (by norm_num) (by norm_num)

theorem sGlobal48_hz109 {c : ℝ} (hc : B (117 / 200) (59 / 100) c) : B (-1990100638040650532961 / 1000000000000000000) (-1919068496019675779473 / 1000000000000000000) (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ)) := bweaken (bmin (sGlobal48_hz108 hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem sGlobal48_hz110 {c : ℝ} (hc : B (117 / 200) (59 / 100) c) : B (-1465319952206152503709 / 1000000000000000000) (-705062703726699653087 / 500000000000000000) ((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) := bmul (sGlobal48_hz76 hc) (sGlobal48_hz109 hc) (by norm_num) (by norm_num)

theorem sGlobal48_hz111 {c : ℝ} (hc : B (117 / 200) (59 / 100) c) : B (-1465335003330896879989 / 1000000000000000000) (-28202809171562873649 / 20000000000000000) (((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) := bsub (sGlobal48_hz110 hc) sGlobal48_hz104 (by norm_num) (by norm_num)

theorem sGlobal48_hz112 {c : ℝ} (hc : B (117 / 200) (59 / 100) c) : B (-300766415357004230001 / 200000000000000000) (-1448637532029390952581 / 1000000000000000000) ((((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) - (s3rs 12225 46 maskSlack)) := bsub (sGlobal48_hz111 hc) sGlobal48_hz29 (by norm_num) (by norm_num)

theorem sGlobal48_hz113 {c : ℝ} (hc : B (117 / 200) (59 / 100) c) : B (-300766415357004230001 / 200000000000000000) (-1448637532029390952581 / 1000000000000000000) (s3L 12225 46 maskSlack c) := by
    convert (sGlobal48_hz112 hc) using 1 <;>
      norm_num [s3L] <;> ring

theorem sGlobal48_hz114 {c : ℝ} (hc : B (117 / 200) (59 / 100) c) : B 0 (929801187318754384073 / 1000000000000000000) |(s3U 12225 46 maskSlack c)| := bweaken (babs (sGlobal48_hz107 hc)) (by norm_num) (by norm_num)

theorem sGlobal48_hz115 {c : ℝ} (hc : B (117 / 200) (59 / 100) c) : B 0 (300766415357004230001 / 200000000000000000) |(s3L 12225 46 maskSlack c)| := bweaken (babs (sGlobal48_hz113 hc)) (by norm_num) (by norm_num)

theorem sGlobal48_hz116 {c : ℝ} (hc : B (117 / 200) (59 / 100) c) : B 0 (300766415357004230001 / 200000000000000000) (max |(s3U 12225 46 maskSlack c)| |(s3L 12225 46 maskSlack c)|) := bweaken (bmax (sGlobal48_hz114 hc) (sGlobal48_hz115 hc)) (by norm_num) (by norm_num)

theorem sGlobal48_hz117 {c : ℝ} (hc : B (117 / 200) (59 / 100) c) : B 0 (300766415357004230001 / 200000000000000000) (s3nks 12225 46 maskSlack c) := by
    convert (sGlobal48_hz116 hc) using 1 <;>
      norm_num [s3nks] <;> ring

theorem sGlobal48 {c : ℝ} (hc : B (117 / 200) (59 / 100) c) :
    0 < s3am 12225 46 ∧ 0 ≤ s3dm 12225 46 c ∧
    s3dm 12225 46 c ^ 2 ≤ 2 * s3ap 12225 46 ^ 2 ∧ s3c1 12225 46 c < 1 ∧
    0 ≤ s3Cpa 12225 c - s3r1 12225 46 ∧
    s3e0 12225 46 ≤ (s3Cpa 12225 c - s3r1 12225 46) / s3ap 12225 46 ∧
    s3nks 12225 46 maskSlack c ≤ 12225 * (123013 / 1000000) := by

  refine ⟨lt_of_lt_of_le (by norm_num) sGlobal48_hz14.1,
    le_trans (by norm_num) (sGlobal48_hz64 hc).1, ?_,
    lt_of_le_of_lt (sGlobal48_hz72 hc).2 (by norm_num), ?_, ?_,
    le_trans (sGlobal48_hz117 hc).2 (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (sGlobal48_hz64 hc).1) (sGlobal48_hz64 hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) sGlobal48_hz9.1 2
    nlinarith only [h1, h2]
  · linarith only [(sGlobal48_hz84 hc).1, sGlobal48_hz33.2]
  · have hap : 0 < s3ap 12225 46 := lt_of_lt_of_le (by norm_num) sGlobal48_hz9.1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul sGlobal48_hz16.2 sGlobal48_hz9.2 (le_trans (by norm_num) sGlobal48_hz9.1) (by norm_num)
    linarith only [h, (sGlobal48_hz84 hc).1, sGlobal48_hz33.2]

end BstLean.Part255
