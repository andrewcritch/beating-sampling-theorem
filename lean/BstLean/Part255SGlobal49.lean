import BstLean.Part255SGlobal45
import BstLean.Part255Numeric10
namespace BstLean.Part255
open Real BstLean.Part130 BstLean.Part182 BstLean.Part197 BstLean.Part246
theorem sGlobal49_hz0 : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal49_hz1 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) ((√(23 : ℝ)) / (12225 : ℝ)) := bdiv sGlobal49_hz0 (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal49_hz2 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) maskSlack := by
    convert sGlobal49_hz1 using 1 <;>
      norm_num [maskSlack] <;> ring

theorem sGlobal49_hz3 : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal49_hz4 : B (6395294793910793 / 500000000000000000) (12790589587821587 / 1000000000000000000) (√((2 / 12225) : ℝ)) := bsqrt (bpoint ((2 / 12225) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal49_hz5 : B (7230130686979 / 62500000000000000) (23136418198333 / 200000000000000000) (√((2 / 149450625) : ℝ)) := bsqrt (bpoint ((2 / 149450625) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal49_hz6 : B (2211334438749598093 / 20000000000000000) (110566721937479904651 / 1000000000000000000) (√(12225 : ℝ)) := bsqrt (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal49_hz7 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))) := bmul sGlobal49_hz3 sGlobal49_hz4 (by norm_num) (by norm_num)

theorem sGlobal49_hz8 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) ((√(12225 : ℝ)) + ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := badd sGlobal49_hz6 sGlobal49_hz7 (by norm_num) (by norm_num)

theorem sGlobal49_hz9 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) (s3ap 12225 46) := by
    convert sGlobal49_hz8 using 1 <;>
      norm_num [s3ap, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal49_hz10 : B (163599182004089 / 1000000000000000000) (16359918200409 / 100000000000000000) ((2 : ℝ) / (12225 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal49_hz11 : B (1222499983640081799591 / 100000000000000000) (12224999836400817995911 / 1000000000000000000) ((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ))) := bsub (bpoint (12225 : ℝ)) sGlobal49_hz10 (by norm_num) (by norm_num)

theorem sGlobal49_hz12 : B (110566721197658827907 / 1000000000000000000) (27641680299414706977 / 250000000000000000) (√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) := bsqrt sGlobal49_hz11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal49_hz13 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) ((√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) - ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bsub sGlobal49_hz12 sGlobal49_hz7 (by norm_num) (by norm_num)

theorem sGlobal49_hz14 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) (s3am 12225 46) := by
    convert sGlobal49_hz13 using 1 <;>
      norm_num [s3am, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal49_hz15 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√((2 / 12225) : ℝ)) * (√(92 : ℝ))) := bmul sGlobal49_hz4 sGlobal49_hz3 (by norm_num) (by norm_num)

theorem sGlobal49_hz16 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) (s3e0 12225 46) := by
    convert sGlobal49_hz15 using 1 <;>
      norm_num [s3e0, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal49_hz17 : B (250196148528560847 / 500000000000000000) (100078459411424339 / 200000000000000000) (((1 / 2) : ℝ) + maskSlack) := badd (bpoint ((1 / 2) : ℝ)) sGlobal49_hz2 (by norm_num) (by norm_num)

theorem sGlobal49_hz18 : B (59827153232297998295487 / 800000000000000) (23930861292919199366019 / 320000000000000) ((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack)) := bmul (bpoint (149450625 : ℝ)) sGlobal49_hz17 (by norm_num) (by norm_num)

theorem sGlobal49_hz19 : B (1729554180017180009583 / 200000000000000000) (8647770900085900056557 / 1000000000000000000) (√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) := bsqrt sGlobal49_hz18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal49_hz20 : B (4328681281566262743499 / 500000000000000000) (8657362563132525495641 / 1000000000000000000) ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))) := badd sGlobal49_hz19 sGlobal49_hz3 (by norm_num) (by norm_num)

theorem sGlobal49_hz21 : B (110732771457999278473 / 1000000000000000000) (55366385728999643621 / 500000000000000000) ((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ)))) := bmul sGlobal49_hz4 sGlobal49_hz20 (by norm_num) (by norm_num)

theorem sGlobal49_hz22 : B (209099159 / 15625000000000000) (13382346177 / 1000000000000000000) ((2 : ℝ) / (149450625 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (149450625 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal49_hz23 : B (2452349334953899930479 / 200000000000000000) (12261746674769501594427 / 1000000000000000000) (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2) := bsq sGlobal49_hz21 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal49_hz24 : B (82045469362091 / 500000000000000000) (32818187747289 / 200000000000000000) (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2)) := bmul sGlobal49_hz22 sGlobal49_hz23 (by norm_num) (by norm_num)

theorem sGlobal49_hz25 : B (82045469362091 / 250000000000000000) (32818187747289 / 100000000000000000) ((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) := bmul (bpoint (2 : ℝ)) sGlobal49_hz24 (by norm_num) (by norm_num)

theorem sGlobal49_hz26 : B (117258080744995992792057 / 1000000000000000000) (58629040372497996396029 / 500000000000000000) (√(13749457500 : ℝ)) := bsqrt (bpoint (13749457500 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal49_hz27 : B (117304080744995992792057 / 1000000000000000000) (58652040372497996396029 / 500000000000000000) ((√(13749457500 : ℝ)) + (46 : ℝ)) := badd sGlobal49_hz26 (bpoint (46 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal49_hz28 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal49_hz25 sGlobal49_hz27 (by norm_num) (by norm_num)

theorem sGlobal49_hz29 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (s3rs 12225 46 maskSlack) := by
    convert sGlobal49_hz28 using 1 <;>
      norm_num [s3rs, s3pp, s3K, mA, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal49_hz30 : B (490797546012267 / 1000000000000000000) (49079754601227 / 100000000000000000) ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (3 : ℝ)) sGlobal49_hz10 (by norm_num) (by norm_num)

theorem sGlobal49_hz31 : B (490797546012267 / 500000000000000000) (49079754601227 / 50000000000000000) ((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal49_hz30 (by norm_num) (by norm_num)

theorem sGlobal49_hz32 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal49_hz31 sGlobal49_hz27 (by norm_num) (by norm_num)

theorem sGlobal49_hz33 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (s3r1 12225 46) := by
    convert sGlobal49_hz32 using 1 <;>
      norm_num [s3r1, mA] <;> ring

theorem sGlobal49_hz34 : B (163599182004089 / 500000000000000000) (16359918200409 / 50000000000000000) ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (2 : ℝ)) sGlobal49_hz10 (by norm_num) (by norm_num)

theorem sGlobal49_hz35 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal49_hz34 (by norm_num) (by norm_num)

theorem sGlobal49_hz36 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal49_hz35 sGlobal49_hz27 (by norm_num) (by norm_num)

theorem sGlobal49_hz37 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (s3rpp 12225 46) := by
    convert sGlobal49_hz36 using 1 <;>
      norm_num [s3rpp, mA] <;> ring

theorem sGlobal49_hz38 {c : ℝ} (hc : B (59 / 100) (119 / 200) c) : B (59 / 100) (119 / 200) c := hc

theorem sGlobal49_hz39 : B (350436133891663427 / 500000000000000000) (140174453556665391 / 200000000000000000) (kdot ((59 / 100))) := by
    constructor
    · apply bkdot_lower (q := (253900391502320151 / 500000000000000000)) (a := (117467185752109409 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (507800783004640301 / 1000000000000000000)) (a := (469868743008437479 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal49_hz40 : B (3481 / 10000) (3481 / 10000) (((59 / 100) : ℝ)^2) := bsq (bpoint ((59 / 100) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal49_hz41 : B (6519 / 10000) (6519 / 10000) ((1 : ℝ) - (((59 / 100) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal49_hz40 (by norm_num) (by norm_num)

theorem sGlobal49_hz42 : B (403701622488689039 / 500000000000000000) (807403244977378079 / 1000000000000000000) (√((1 : ℝ) - (((59 / 100) : ℝ)^2))) := bsqrt sGlobal49_hz41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal49_hz43 : B (257004435013172473 / 1000000000000000000) (128502217506586237 / 500000000000000000) ((√((1 : ℝ) - (((59 / 100) : ℝ)^2))) / Real.pi) := bdiv sGlobal49_hz42 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal49_hz44 : B (413514637992162843 / 1000000000000000000) (51689329749020363 / 125000000000000000) (((59 / 100) : ℝ) * (kdot ((59 / 100)))) := bmul (bpoint ((59 / 100) : ℝ)) sGlobal49_hz39 (by norm_num) (by norm_num)

theorem sGlobal49_hz45 : B (167629768251333829 / 250000000000000000) (335259536502667689 / 500000000000000000) (((√((1 : ℝ) - (((59 / 100) : ℝ)^2))) / Real.pi) + (((59 / 100) : ℝ) * (kdot ((59 / 100))))) := badd sGlobal49_hz43 sGlobal49_hz44 (by norm_num) (by norm_num)

theorem sGlobal49_hz46 : B (167629768251333829 / 250000000000000000) (335259536502667689 / 500000000000000000) (kappa ((59 / 100))) := by rw [kappa_eq]; exact sGlobal49_hz45

theorem sGlobal49_hz47 : B (140569591221326651 / 200000000000000000) (28113918244265333 / 40000000000000000) (kdot ((119 / 200))) := by
    constructor
    · apply bkdot_lower (q := (503903259860268857 / 1000000000000000000)) (a := (466765339047296373 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (62987907482533607 / 125000000000000000)) (a := (93353067809459253 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal49_hz48 : B (14161 / 40000) (14161 / 40000) (((119 / 200) : ℝ)^2) := bsq (bpoint ((119 / 200) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal49_hz49 : B (25839 / 40000) (25839 / 40000) ((1 : ℝ) - (((119 / 200) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal49_hz48 (by norm_num) (by norm_num)

theorem sGlobal49_hz50 : B (401862849738564413 / 500000000000000000) (803725699477128827 / 1000000000000000000) (√((1 : ℝ) - (((119 / 200) : ℝ)^2))) := bsqrt sGlobal49_hz49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal49_hz51 : B (127916917961776211 / 500000000000000000) (255833835923552423 / 1000000000000000000) ((√((1 : ℝ) - (((119 / 200) : ℝ)^2))) / Real.pi) := bdiv sGlobal49_hz50 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal49_hz52 : B (209097266941723393 / 500000000000000000) (418194533883446829 / 1000000000000000000) (((119 / 200) : ℝ) * (kdot ((119 / 200)))) := bmul (bpoint ((119 / 200) : ℝ)) sGlobal49_hz47 (by norm_num) (by norm_num)

theorem sGlobal49_hz53 : B (84253546225874901 / 125000000000000000) (168507092451749813 / 250000000000000000) (((√((1 : ℝ) - (((119 / 200) : ℝ)^2))) / Real.pi) + (((119 / 200) : ℝ) * (kdot ((119 / 200))))) := badd sGlobal49_hz51 sGlobal49_hz52 (by norm_num) (by norm_num)

theorem sGlobal49_hz54 : B (84253546225874901 / 125000000000000000) (168507092451749813 / 250000000000000000) (kappa ((119 / 200))) := by rw [kappa_eq]; exact sGlobal49_hz53

theorem sGlobal49_hz55 {c : ℝ} (hc : B (59 / 100) (119 / 200) c) : B (167629768251333829 / 250000000000000000) (168507092451749813 / 250000000000000000) (kappa c) := bkappa (sGlobal49_hz38 hc) (by norm_num) (by norm_num) sGlobal49_hz46.1 sGlobal49_hz54.2

theorem sGlobal49_hz56 : B 24450 24450 ((2 : ℝ) * (12225 : ℝ)) := bmul (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal49_hz57 {c : ℝ} (hc : B (59 / 100) (119 / 200) c) : B (81492907548250187 / 250000000000000000) (82370231748666171 / 250000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (sGlobal49_hz55 hc) (by norm_num) (by norm_num)

theorem sGlobal49_hz58 {c : ℝ} (hc : B (59 / 100) (119 / 200) c) : B (39850031791094341443 / 5000000000000000) (40279043325097757619 / 5000000000000000) (((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) := bmul sGlobal49_hz56 (sGlobal49_hz57 hc) (by norm_num) (by norm_num)

theorem sGlobal49_hz59 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (4 : ℝ)) sGlobal49_hz10 (by norm_num) (by norm_num)

theorem sGlobal49_hz60 {c : ℝ} (hc : B (59 / 100) (119 / 200) c) : B (99625071297776753403 / 12500000000000000) (2013952002655705876861 / 250000000000000000) ((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bsub (sGlobal49_hz58 hc) sGlobal49_hz59 (by norm_num) (by norm_num)

theorem sGlobal49_hz61 {c : ℝ} (hc : B (59 / 100) (119 / 200) c) : B (89274888427945628389 / 1000000000000000000) (89754153166429148297 / 1000000000000000000) (√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) := bsqrt (sGlobal49_hz60 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal49_hz62 : B (30670756373515103 / 125000000000000000) (122683025494060423 / 500000000000000000) ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal49_hz7 (by norm_num) (by norm_num)

theorem sGlobal49_hz63 {c : ℝ} (hc : B (59 / 100) (119 / 200) c) : B (89029522376957507543 / 1000000000000000000) (89508787115441027473 / 1000000000000000000) ((√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) - ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))))) := bsub (sGlobal49_hz61 hc) sGlobal49_hz62 (by norm_num) (by norm_num)

theorem sGlobal49_hz64 {c : ℝ} (hc : B (59 / 100) (119 / 200) c) : B (89029522376957507543 / 1000000000000000000) (89508787115441027473 / 1000000000000000000) (s3dm 12225 46 c) := by
    convert (sGlobal49_hz63 hc) using 1 <;>
      norm_num [s3dm, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal49_hz65 : B (6126072185528622723889 / 500000000000000000) (2450428874211449090087 / 200000000000000000) ((s3ap 12225 46)^2) := bsq sGlobal49_hz9 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal49_hz66 : B (6126072185528622723889 / 250000000000000000) (2450428874211449090087 / 100000000000000000) ((2 : ℝ) * ((s3ap 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal49_hz65 (by norm_num) (by norm_num)

theorem sGlobal49_hz67 {c : ℝ} (hc : B (59 / 100) (119 / 200) c) : B (3963127927334588781913 / 500000000000000000) (8011822970877341691611 / 1000000000000000000) ((s3dm 12225 46 c)^2) := bsq (sGlobal49_hz64 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal49_hz68 {c : ℝ} (hc : B (59 / 100) (119 / 200) c) : B (3298493154247429840789 / 200000000000000000) (4144508221861328334261 / 250000000000000000) (((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) := bsub sGlobal49_hz66 (sGlobal49_hz67 hc) (by norm_num) (by norm_num)

theorem sGlobal49_hz69 : B (1524735695971823534271 / 125000000000000000) (609894278388729413841 / 50000000000000000) ((s3am 12225 46)^2) := bsq sGlobal49_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal49_hz70 : B (1524735695971823534271 / 62500000000000000) (609894278388729413841 / 25000000000000000) ((2 : ℝ) * ((s3am 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal49_hz69 (by norm_num) (by norm_num)

theorem sGlobal49_hz71 {c : ℝ} (hc : B (59 / 100) (119 / 200) c) : B (67603789524015327 / 100000000000000000) (84943169019609487 / 125000000000000000) ((((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) / ((2 : ℝ) * ((s3am 12225 46)^2))) := bdiv (sGlobal49_hz68 hc) sGlobal49_hz70 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal49_hz72 {c : ℝ} (hc : B (59 / 100) (119 / 200) c) : B (67603789524015327 / 100000000000000000) (84943169019609487 / 125000000000000000) (s3c1 12225 46 c) := by
    convert (sGlobal49_hz71 hc) using 1 <;>
      norm_num [s3c1] <;> ring

theorem sGlobal49_hz73 {c : ℝ} (hc : B (59 / 100) (119 / 200) c) : B (350436133891663427 / 500000000000000000) (28113918244265333 / 40000000000000000) (kdot c) := bkdot (sGlobal49_hz38 hc) sGlobal49_hz39.1 sGlobal49_hz47.2

theorem sGlobal49_hz74 : B (736304448225708913 / 1000000000000000000) (184076112056427229 / 250000000000000000) (kdot ((67603789524015327 / 100000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (54956011032521953 / 125000000000000000)) (a := (207106002059604961 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (439648088260175623 / 1000000000000000000)) (a := (1294412512872531 / 3125000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal49_hz75 : B (737822919253221167 / 1000000000000000000) (737822919253221169 / 1000000000000000000) (kdot ((84943169019609487 / 125000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (109201204428333437 / 250000000000000000)) (a := (205913397703424601 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (436804817713333747 / 1000000000000000000)) (a := (1029566988517123 / 2500000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal49_hz76 {c : ℝ} (hc : B (59 / 100) (119 / 200) c) : B (736304448225708913 / 1000000000000000000) (737822919253221169 / 1000000000000000000) (kdot (s3c1 12225 46 c)) := bkdot (sGlobal49_hz72 hc) sGlobal49_hz74.1 sGlobal49_hz75.2

theorem sGlobal49_hz77 {c : ℝ} (hc : B (59 / 100) (119 / 200) c) : B (3481 / 10000) (14161 / 40000) (c^2) := bsq (sGlobal49_hz38 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal49_hz78 {c : ℝ} (hc : B (59 / 100) (119 / 200) c) : B (25839 / 40000) (6519 / 10000) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (sGlobal49_hz77 hc) (by norm_num) (by norm_num)

theorem sGlobal49_hz79 {c : ℝ} (hc : B (59 / 100) (119 / 200) c) : B (401862849738564413 / 500000000000000000) (807403244977378079 / 1000000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (sGlobal49_hz78 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal49_hz80 : B (39119999999999765769 / 1600000000000000) (3912000000000000489 / 160000000000000) ((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (149450625 : ℝ)) sGlobal49_hz10 (by norm_num) (by norm_num)

theorem sGlobal49_hz81 {c : ℝ} (hc : B (59 / 100) (119 / 200) c) : B (281654526834137959 / 500000000000000000) (283740860243106771 / 500000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (sGlobal49_hz79 hc) (sGlobal49_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal49_hz82 {c : ℝ} (hc : B (59 / 100) (119 / 200) c) : B (13772906362189263729823 / 1000000000000000000) (13874928065887922836267 / 1000000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) := bmul sGlobal49_hz80 (sGlobal49_hz81 hc) (by norm_num) (by norm_num)

theorem sGlobal49_hz83 {c : ℝ} (hc : B (59 / 100) (119 / 200) c) : B (6886453181094631864911 / 1000000000000000000) (3468732016471980709067 / 500000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) / (2 : ℝ)) := bdiv (sGlobal49_hz82 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal49_hz84 {c : ℝ} (hc : B (59 / 100) (119 / 200) c) : B (6886453181094631864911 / 1000000000000000000) (3468732016471980709067 / 500000000000000000) (s3Cpa 12225 c) := by
    convert (sGlobal49_hz83 hc) using 1 <;>
      norm_num [s3Cpa, mA] <;> ring

theorem sGlobal49_hz85 {c : ℝ} (hc : B (59 / 100) (119 / 200) c) : B (127916917961776211 / 500000000000000000) (128502217506586237 / 500000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (sGlobal49_hz79 hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal49_hz86 {c : ℝ} (hc : B (59 / 100) (119 / 200) c) : B (413514637992162843 / 1000000000000000000) (418194533883446829 / 1000000000000000000) (c * (kdot c)) := bmul (sGlobal49_hz38 hc) (sGlobal49_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal49_hz87 {c : ℝ} (hc : B (59 / 100) (119 / 200) c) : B (-162360697959894407 / 1000000000000000000) (-156510202978990369 / 1000000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (sGlobal49_hz85 hc) (sGlobal49_hz86 hc) (by norm_num) (by norm_num)

theorem sGlobal49_hz88 {c : ℝ} (hc : B (59 / 100) (119 / 200) c) : B (-793943813023883749473 / 200000000000000000) (-956668615709072902459 / 250000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) := bmul sGlobal49_hz80 (sGlobal49_hz87 hc) (by norm_num) (by norm_num)

theorem sGlobal49_hz89 {c : ℝ} (hc : B (59 / 100) (119 / 200) c) : B (-1984859532559709373683 / 1000000000000000000) (-956668615709072902459 / 500000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) / (2 : ℝ)) := bdiv (sGlobal49_hz88 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal49_hz90 {c : ℝ} (hc : B (59 / 100) (119 / 200) c) : B (-1984859532559709373683 / 1000000000000000000) (-956668615709072902459 / 500000000000000000) (s3Cpp 12225 c) := by
    convert (sGlobal49_hz89 hc) using 1 <;>
      norm_num [s3Cpp, mA] <;> ring

theorem sGlobal49_hz91 {c : ℝ} (hc : B (59 / 100) (119 / 200) c) : B (109399973297318274583 / 15625000000000000) (176315228571942495759 / 25000000000000000) ((s3Cpa 12225 c) + (s3r1 12225 46)) := badd (sGlobal49_hz84 hc) sGlobal49_hz33 (by norm_num) (by norm_num)

theorem sGlobal49_hz92 {c : ℝ} (hc : B (59 / 100) (119 / 200) c) : B (31697493168956691397 / 500000000000000000) (6385685691683781887 / 100000000000000000) (((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) := bdiv (sGlobal49_hz91 hc) sGlobal49_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal49_hz93 {c : ℝ} (hc : B (59 / 100) (119 / 200) c) : B (31758834681703721603 / 500000000000000000) (63979539942331879293 / 1000000000000000000) ((((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) + (s3e0 12225 46)) := badd (sGlobal49_hz92 hc) sGlobal49_hz16 (by norm_num) (by norm_num)

theorem sGlobal49_hz94 {c : ℝ} (hc : B (59 / 100) (119 / 200) c) : B (31758834681703721603 / 500000000000000000) (63979539942331879293 / 1000000000000000000) (s3Lam 12225 46 c) := by
    convert (sGlobal49_hz93 hc) using 1 <;>
      norm_num [s3Lam] <;> ring

theorem sGlobal49_hz95 {c : ℝ} (hc : B (59 / 100) (119 / 200) c) : B (-1908096125937217568083 / 1000000000000000000) (-18365738247956535301 / 10000000000000000) ((s3Cpp 12225 c) + (s3rpp 12225 46)) := badd (sGlobal49_hz90 hc) sGlobal49_hz37 (by norm_num) (by norm_num)

theorem sGlobal49_hz96 {c : ℝ} (hc : B (59 / 100) (119 / 200) c) : B (-351959263463689952099 / 250000000000000000) (-18365738247956535301 / 20000000000000000) (if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) := bweaken (bfirst (sGlobal49_hz95 hc) (sGlobal49_hz76 hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem sGlobal49_hz97 {c : ℝ} (hc : B (59 / 100) (119 / 200) c) : B (2017247160679574255727 / 500000000000000000) (4093381531232440332329 / 1000000000000000000) ((s3Lam 12225 46 c)^2) := bsq (sGlobal49_hz94 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal49_hz98 {c : ℝ} (hc : B (59 / 100) (119 / 200) c) : B (457027235800736447 / 1000000000000000000) (115445471409503119 / 250000000000000000) ((s3c1 12225 46 c)^2) := bsq (sGlobal49_hz72 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal49_hz99 {c : ℝ} (hc : B (59 / 100) (119 / 200) c) : B (134554528590496881 / 250000000000000000) (542972764199263553 / 1000000000000000000) ((1 : ℝ) - ((s3c1 12225 46 c)^2)) := bsub (bpoint (1 : ℝ)) (sGlobal49_hz98 hc) (by norm_num) (by norm_num)

theorem sGlobal49_hz100 {c : ℝ} (hc : B (59 / 100) (119 / 200) c) : B (73363350139016111 / 100000000000000000) (184216714123485473 / 250000000000000000) (√((1 : ℝ) - ((s3c1 12225 46 c)^2))) := bsqrt (sGlobal49_hz99 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal49_hz101 {c : ℝ} (hc : B (59 / 100) (119 / 200) c) : B (576194404598671877 / 250000000000000000) (2314935503035172277 / 1000000000000000000) (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))) := bmul pi_mem (sGlobal49_hz100 hc) (by norm_num) (by norm_num)

theorem sGlobal49_hz102 {c : ℝ} (hc : B (59 / 100) (119 / 200) c) : B (10892566758526905629 / 6250000000000000) (888020930644827790061 / 500000000000000000) (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2))))) := bdiv (sGlobal49_hz97 hc) (sGlobal49_hz101 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal49_hz103 {c : ℝ} (hc : B (59 / 100) (119 / 200) c) : B (83743406877386273061 / 250000000000000000) (26804842152869650471 / 31250000000000000) ((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) := badd (sGlobal49_hz96 hc) (sGlobal49_hz102 hc) (by norm_num) (by norm_num)

theorem sGlobal49_hz104 : B (3762781186094069 / 250000000000000000) (376278118609407 / 25000000000000000) ((s3e0 12225 46)^2) := bsq sGlobal49_hz16 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal49_hz105 {c : ℝ} (hc : B (59 / 100) (119 / 200) c) : B (8374716965857236713 / 25000000000000000) (107221250002071648919 / 125000000000000000) (((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) := badd (sGlobal49_hz103 hc) sGlobal49_hz104 (by norm_num) (by norm_num)

theorem sGlobal49_hz106 {c : ℝ} (hc : B (59 / 100) (119 / 200) c) : B (373485752085536738651 / 1000000000000000000) (112033384183837182671 / 125000000000000000) ((((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) + (s3rs 12225 46 maskSlack)) := badd (sGlobal49_hz105 hc) sGlobal49_hz29 (by norm_num) (by norm_num)

theorem sGlobal49_hz107 {c : ℝ} (hc : B (59 / 100) (119 / 200) c) : B (373485752085536738651 / 1000000000000000000) (112033384183837182671 / 125000000000000000) (s3U 12225 46 maskSlack c) := by
    convert (sGlobal49_hz106 hc) using 1 <;>
      norm_num [s3U] <;> ring

theorem sGlobal49_hz108 {c : ℝ} (hc : B (59 / 100) (119 / 200) c) : B (-2061622939182201648501 / 1000000000000000000) (-995050319020318805259 / 500000000000000000) ((s3Cpp 12225 c) - (s3rpp 12225 46)) := bsub (sGlobal49_hz90 hc) sGlobal49_hz37 (by norm_num) (by norm_num)

theorem sGlobal49_hz109 {c : ℝ} (hc : B (59 / 100) (119 / 200) c) : B (-2061622939182201648501 / 1000000000000000000) (-995050319020318805259 / 500000000000000000) (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ)) := bweaken (bmin (sGlobal49_hz108 hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem sGlobal49_hz110 {c : ℝ} (hc : B (59 / 100) (119 / 200) c) : B (-1521112655386818063841 / 1000000000000000000) (-1465319952206142929153 / 1000000000000000000) ((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) := bmul (sGlobal49_hz76 hc) (sGlobal49_hz109 hc) (by norm_num) (by norm_num)

theorem sGlobal49_hz111 {c : ℝ} (hc : B (59 / 100) (119 / 200) c) : B (-1521127706511562440121 / 1000000000000000000) (-1465335003330887305429 / 1000000000000000000) (((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) := bsub (sGlobal49_hz110 hc) sGlobal49_hz104 (by norm_num) (by norm_num)

theorem sGlobal49_hz112 {c : ℝ} (hc : B (59 / 100) (119 / 200) c) : B (-1559624779965686710137 / 1000000000000000000) (-37595801919553364389 / 25000000000000000) ((((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) - (s3rs 12225 46 maskSlack)) := bsub (sGlobal49_hz111 hc) sGlobal49_hz29 (by norm_num) (by norm_num)

theorem sGlobal49_hz113 {c : ℝ} (hc : B (59 / 100) (119 / 200) c) : B (-1559624779965686710137 / 1000000000000000000) (-37595801919553364389 / 25000000000000000) (s3L 12225 46 maskSlack c) := by
    convert (sGlobal49_hz112 hc) using 1 <;>
      norm_num [s3L] <;> ring

theorem sGlobal49_hz114 {c : ℝ} (hc : B (59 / 100) (119 / 200) c) : B 0 (112033384183837182671 / 125000000000000000) |(s3U 12225 46 maskSlack c)| := bweaken (babs (sGlobal49_hz107 hc)) (by norm_num) (by norm_num)

theorem sGlobal49_hz115 {c : ℝ} (hc : B (59 / 100) (119 / 200) c) : B 0 (1559624779965686710137 / 1000000000000000000) |(s3L 12225 46 maskSlack c)| := bweaken (babs (sGlobal49_hz113 hc)) (by norm_num) (by norm_num)

theorem sGlobal49_hz116 {c : ℝ} (hc : B (59 / 100) (119 / 200) c) : B 0 (1559624779965686710137 / 1000000000000000000) (max |(s3U 12225 46 maskSlack c)| |(s3L 12225 46 maskSlack c)|) := bweaken (bmax (sGlobal49_hz114 hc) (sGlobal49_hz115 hc)) (by norm_num) (by norm_num)

theorem sGlobal49_hz117 {c : ℝ} (hc : B (59 / 100) (119 / 200) c) : B 0 (1559624779965686710137 / 1000000000000000000) (s3nks 12225 46 maskSlack c) := by
    convert (sGlobal49_hz116 hc) using 1 <;>
      norm_num [s3nks] <;> ring

theorem sGlobal49 {c : ℝ} (hc : B (59 / 100) (119 / 200) c) :
    0 < s3am 12225 46 ∧ 0 ≤ s3dm 12225 46 c ∧
    s3dm 12225 46 c ^ 2 ≤ 2 * s3ap 12225 46 ^ 2 ∧ s3c1 12225 46 c < 1 ∧
    0 ≤ s3Cpa 12225 c - s3r1 12225 46 ∧
    s3e0 12225 46 ≤ (s3Cpa 12225 c - s3r1 12225 46) / s3ap 12225 46 ∧
    s3nks 12225 46 maskSlack c ≤ 12225 * (127577 / 1000000) := by

  refine ⟨lt_of_lt_of_le (by norm_num) sGlobal49_hz14.1,
    le_trans (by norm_num) (sGlobal49_hz64 hc).1, ?_,
    lt_of_le_of_lt (sGlobal49_hz72 hc).2 (by norm_num), ?_, ?_,
    le_trans (sGlobal49_hz117 hc).2 (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (sGlobal49_hz64 hc).1) (sGlobal49_hz64 hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) sGlobal49_hz9.1 2
    nlinarith only [h1, h2]
  · linarith only [(sGlobal49_hz84 hc).1, sGlobal49_hz33.2]
  · have hap : 0 < s3ap 12225 46 := lt_of_lt_of_le (by norm_num) sGlobal49_hz9.1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul sGlobal49_hz16.2 sGlobal49_hz9.2 (le_trans (by norm_num) sGlobal49_hz9.1) (by norm_num)
    linarith only [h, (sGlobal49_hz84 hc).1, sGlobal49_hz33.2]

end BstLean.Part255
