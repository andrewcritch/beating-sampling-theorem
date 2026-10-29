import BstLean.Part255SGlobal43
import BstLean.Part255Numeric10
namespace BstLean.Part255
open Real BstLean.Part130 BstLean.Part182 BstLean.Part197 BstLean.Part246
theorem sGlobal47_hz0 : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal47_hz1 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) ((√(23 : ℝ)) / (12225 : ℝ)) := bdiv sGlobal47_hz0 (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal47_hz2 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) maskSlack := by
    convert sGlobal47_hz1 using 1 <;>
      norm_num [maskSlack] <;> ring

theorem sGlobal47_hz3 : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal47_hz4 : B (6395294793910793 / 500000000000000000) (12790589587821587 / 1000000000000000000) (√((2 / 12225) : ℝ)) := bsqrt (bpoint ((2 / 12225) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal47_hz5 : B (7230130686979 / 62500000000000000) (23136418198333 / 200000000000000000) (√((2 / 149450625) : ℝ)) := bsqrt (bpoint ((2 / 149450625) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal47_hz6 : B (2211334438749598093 / 20000000000000000) (110566721937479904651 / 1000000000000000000) (√(12225 : ℝ)) := bsqrt (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal47_hz7 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))) := bmul sGlobal47_hz3 sGlobal47_hz4 (by norm_num) (by norm_num)

theorem sGlobal47_hz8 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) ((√(12225 : ℝ)) + ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := badd sGlobal47_hz6 sGlobal47_hz7 (by norm_num) (by norm_num)

theorem sGlobal47_hz9 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) (s3ap 12225 46) := by
    convert sGlobal47_hz8 using 1 <;>
      norm_num [s3ap, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal47_hz10 : B (163599182004089 / 1000000000000000000) (16359918200409 / 100000000000000000) ((2 : ℝ) / (12225 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal47_hz11 : B (1222499983640081799591 / 100000000000000000) (12224999836400817995911 / 1000000000000000000) ((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ))) := bsub (bpoint (12225 : ℝ)) sGlobal47_hz10 (by norm_num) (by norm_num)

theorem sGlobal47_hz12 : B (110566721197658827907 / 1000000000000000000) (27641680299414706977 / 250000000000000000) (√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) := bsqrt sGlobal47_hz11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal47_hz13 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) ((√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) - ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bsub sGlobal47_hz12 sGlobal47_hz7 (by norm_num) (by norm_num)

theorem sGlobal47_hz14 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) (s3am 12225 46) := by
    convert sGlobal47_hz13 using 1 <;>
      norm_num [s3am, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal47_hz15 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√((2 / 12225) : ℝ)) * (√(92 : ℝ))) := bmul sGlobal47_hz4 sGlobal47_hz3 (by norm_num) (by norm_num)

theorem sGlobal47_hz16 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) (s3e0 12225 46) := by
    convert sGlobal47_hz15 using 1 <;>
      norm_num [s3e0, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal47_hz17 : B (250196148528560847 / 500000000000000000) (100078459411424339 / 200000000000000000) (((1 / 2) : ℝ) + maskSlack) := badd (bpoint ((1 / 2) : ℝ)) sGlobal47_hz2 (by norm_num) (by norm_num)

theorem sGlobal47_hz18 : B (59827153232297998295487 / 800000000000000) (23930861292919199366019 / 320000000000000) ((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack)) := bmul (bpoint (149450625 : ℝ)) sGlobal47_hz17 (by norm_num) (by norm_num)

theorem sGlobal47_hz19 : B (1729554180017180009583 / 200000000000000000) (8647770900085900056557 / 1000000000000000000) (√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) := bsqrt sGlobal47_hz18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal47_hz20 : B (4328681281566262743499 / 500000000000000000) (8657362563132525495641 / 1000000000000000000) ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))) := badd sGlobal47_hz19 sGlobal47_hz3 (by norm_num) (by norm_num)

theorem sGlobal47_hz21 : B (110732771457999278473 / 1000000000000000000) (55366385728999643621 / 500000000000000000) ((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ)))) := bmul sGlobal47_hz4 sGlobal47_hz20 (by norm_num) (by norm_num)

theorem sGlobal47_hz22 : B (209099159 / 15625000000000000) (13382346177 / 1000000000000000000) ((2 : ℝ) / (149450625 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (149450625 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal47_hz23 : B (2452349334953899930479 / 200000000000000000) (12261746674769501594427 / 1000000000000000000) (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2) := bsq sGlobal47_hz21 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal47_hz24 : B (82045469362091 / 500000000000000000) (32818187747289 / 200000000000000000) (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2)) := bmul sGlobal47_hz22 sGlobal47_hz23 (by norm_num) (by norm_num)

theorem sGlobal47_hz25 : B (82045469362091 / 250000000000000000) (32818187747289 / 100000000000000000) ((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) := bmul (bpoint (2 : ℝ)) sGlobal47_hz24 (by norm_num) (by norm_num)

theorem sGlobal47_hz26 : B (117258080744995992792057 / 1000000000000000000) (58629040372497996396029 / 500000000000000000) (√(13749457500 : ℝ)) := bsqrt (bpoint (13749457500 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal47_hz27 : B (117304080744995992792057 / 1000000000000000000) (58652040372497996396029 / 500000000000000000) ((√(13749457500 : ℝ)) + (46 : ℝ)) := badd sGlobal47_hz26 (bpoint (46 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal47_hz28 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal47_hz25 sGlobal47_hz27 (by norm_num) (by norm_num)

theorem sGlobal47_hz29 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (s3rs 12225 46 maskSlack) := by
    convert sGlobal47_hz28 using 1 <;>
      norm_num [s3rs, s3pp, s3K, mA, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal47_hz30 : B (490797546012267 / 1000000000000000000) (49079754601227 / 100000000000000000) ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (3 : ℝ)) sGlobal47_hz10 (by norm_num) (by norm_num)

theorem sGlobal47_hz31 : B (490797546012267 / 500000000000000000) (49079754601227 / 50000000000000000) ((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal47_hz30 (by norm_num) (by norm_num)

theorem sGlobal47_hz32 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal47_hz31 sGlobal47_hz27 (by norm_num) (by norm_num)

theorem sGlobal47_hz33 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (s3r1 12225 46) := by
    convert sGlobal47_hz32 using 1 <;>
      norm_num [s3r1, mA] <;> ring

theorem sGlobal47_hz34 : B (163599182004089 / 500000000000000000) (16359918200409 / 50000000000000000) ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (2 : ℝ)) sGlobal47_hz10 (by norm_num) (by norm_num)

theorem sGlobal47_hz35 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal47_hz34 (by norm_num) (by norm_num)

theorem sGlobal47_hz36 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal47_hz35 sGlobal47_hz27 (by norm_num) (by norm_num)

theorem sGlobal47_hz37 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (s3rpp 12225 46) := by
    convert sGlobal47_hz36 using 1 <;>
      norm_num [s3rpp, mA] <;> ring

theorem sGlobal47_hz38 {c : ℝ} (hc : B (29 / 50) (117 / 200) c) : B (29 / 50) (117 / 200) c := hc

theorem sGlobal47_hz39 : B (2722451012134883 / 3906250000000000) (696947459106530257 / 1000000000000000000) (kdot ((29 / 50))) := by
    constructor
    · apply bkdot_lower (q := (515580046947248127 / 1000000000000000000)) (a := (238016909030661399 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (257790023473624063 / 500000000000000000)) (a := (47603381806132247 / 100000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal47_hz40 : B (841 / 2500) (841 / 2500) (((29 / 50) : ℝ)^2) := bsq (bpoint ((29 / 50) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal47_hz41 : B (1659 / 2500) (1659 / 2500) ((1 : ℝ) - (((29 / 50) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal47_hz40 (by norm_num) (by norm_num)

theorem sGlobal47_hz42 : B (20365411854416301 / 25000000000000000) (814616474176652041 / 1000000000000000000) (√((1 : ℝ) - (((29 / 50) : ℝ)^2))) := bsqrt sGlobal47_hz41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal47_hz43 : B (259300477178610963 / 1000000000000000000) (64825119294652741 / 250000000000000000) ((√((1 : ℝ) - (((29 / 50) : ℝ)^2))) / Real.pi) := bdiv sGlobal47_hz42 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal47_hz44 : B (404229526281787427 / 1000000000000000000) (8084590525635751 / 20000000000000000) (((29 / 50) : ℝ) * (kdot ((29 / 50)))) := bmul (bpoint ((29 / 50) : ℝ)) sGlobal47_hz39 (by norm_num) (by norm_num)

theorem sGlobal47_hz45 : B (66353000346039839 / 100000000000000000) (331765001730199257 / 500000000000000000) (((√((1 : ℝ) - (((29 / 50) : ℝ)^2))) / Real.pi) + (((29 / 50) : ℝ) * (kdot ((29 / 50))))) := badd sGlobal47_hz43 sGlobal47_hz44 (by norm_num) (by norm_num)

theorem sGlobal47_hz46 : B (66353000346039839 / 100000000000000000) (331765001730199257 / 500000000000000000) (kappa ((29 / 50))) := by rw [kappa_eq]; exact sGlobal47_hz45

theorem sGlobal47_hz47 : B (698905500064522689 / 1000000000000000000) (139781100012904567 / 200000000000000000) (kdot ((117 / 200))) := by
    constructor
    · apply bkdot_lower (q := (511692928421768817 / 1000000000000000000)) (a := (118239533629198499 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (31980808026360551 / 62500000000000000)) (a := (472958134516793769 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal47_hz48 : B (13689 / 40000) (13689 / 40000) (((117 / 200) : ℝ)^2) := bsq (bpoint ((117 / 200) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal47_hz49 : B (26311 / 40000) (26311 / 40000) ((1 : ℝ) - (((117 / 200) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal47_hz48 (by norm_num) (by norm_num)

theorem sGlobal47_hz50 : B (405516645774251787 / 500000000000000000) (32441331661940143 / 40000000000000000) (√((1 : ℝ) - (((117 / 200) : ℝ)^2))) := bsqrt sGlobal47_hz49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal47_hz51 : B (258159914724069289 / 1000000000000000000) (25815991472406929 / 100000000000000000) ((√((1 : ℝ) - (((117 / 200) : ℝ)^2))) / Real.pi) := bdiv sGlobal47_hz50 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal47_hz52 : B (408859717537745773 / 1000000000000000000) (408859717537745859 / 1000000000000000000) (((117 / 200) : ℝ) * (kdot ((117 / 200)))) := bmul (bpoint ((117 / 200) : ℝ)) sGlobal47_hz47 (by norm_num) (by norm_num)

theorem sGlobal47_hz53 : B (333509816130907531 / 500000000000000000) (667019632261815149 / 1000000000000000000) (((√((1 : ℝ) - (((117 / 200) : ℝ)^2))) / Real.pi) + (((117 / 200) : ℝ) * (kdot ((117 / 200))))) := badd sGlobal47_hz51 sGlobal47_hz52 (by norm_num) (by norm_num)

theorem sGlobal47_hz54 : B (333509816130907531 / 500000000000000000) (667019632261815149 / 1000000000000000000) (kappa ((117 / 200))) := by rw [kappa_eq]; exact sGlobal47_hz53

theorem sGlobal47_hz55 {c : ℝ} (hc : B (29 / 50) (117 / 200) c) : B (66353000346039839 / 100000000000000000) (667019632261815149 / 1000000000000000000) (kappa c) := bkappa (sGlobal47_hz38 hc) (by norm_num) (by norm_num) sGlobal47_hz46.1 sGlobal47_hz54.2

theorem sGlobal47_hz56 : B 24450 24450 ((2 : ℝ) * (12225 : ℝ)) := bmul (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal47_hz57 {c : ℝ} (hc : B (29 / 50) (117 / 200) c) : B (332980367738184851 / 1000000000000000000) (33646999653960161 / 100000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (sGlobal47_hz55 hc) (by norm_num) (by norm_num)

theorem sGlobal47_hz58 {c : ℝ} (hc : B (29 / 50) (117 / 200) c) : B (162827399823972392139 / 20000000000000000) (16453382830786518729 / 2000000000000000) (((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) := bmul sGlobal47_hz56 (sGlobal47_hz57 hc) (by norm_num) (by norm_num)

theorem sGlobal47_hz59 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (4 : ℝ)) sGlobal47_hz10 (by norm_num) (by norm_num)

theorem sGlobal47_hz60 {c : ℝ} (hc : B (29 / 50) (117 / 200) c) : B (814136933680189159059 / 100000000000000000) (514168172562283209259 / 62500000000000000) ((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bsub (sGlobal47_hz58 hc) sGlobal47_hz59 (by norm_num) (by norm_num)

theorem sGlobal47_hz61 {c : ℝ} (hc : B (29 / 50) (117 / 200) c) : B (22557384235547308343 / 250000000000000000) (45350553362104996889 / 500000000000000000) (√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) := bsqrt (sGlobal47_hz60 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal47_hz62 : B (30670756373515103 / 125000000000000000) (122683025494060423 / 500000000000000000) ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal47_hz7 (by norm_num) (by norm_num)

theorem sGlobal47_hz63 {c : ℝ} (hc : B (29 / 50) (117 / 200) c) : B (44992085445600556263 / 500000000000000000) (45227870336610936477 / 500000000000000000) ((√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) - ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))))) := bsub (sGlobal47_hz61 hc) sGlobal47_hz62 (by norm_num) (by norm_num)

theorem sGlobal47_hz64 {c : ℝ} (hc : B (29 / 50) (117 / 200) c) : B (44992085445600556263 / 500000000000000000) (45227870336610936477 / 500000000000000000) (s3dm 12225 46 c) := by
    convert (sGlobal47_hz63 hc) using 1 <;>
      norm_num [s3dm, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal47_hz65 : B (6126072185528622723889 / 500000000000000000) (2450428874211449090087 / 200000000000000000) ((s3ap 12225 46)^2) := bsq sGlobal47_hz9 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal47_hz66 : B (6126072185528622723889 / 250000000000000000) (2450428874211449090087 / 100000000000000000) ((2 : ℝ) * ((s3ap 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal47_hz65 (by norm_num) (by norm_num)

theorem sGlobal47_hz67 {c : ℝ} (hc : B (29 / 50) (117 / 200) c) : B (126517984546513837839 / 15625000000000000) (2045560255185291464427 / 250000000000000000) ((s3dm 12225 46 c)^2) := bsq (sGlobal47_hz64 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal47_hz68 {c : ℝ} (hc : B (29 / 50) (117 / 200) c) : B (2040255965171665629731 / 125000000000000000) (8203568865568802639587 / 500000000000000000) (((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) := bsub sGlobal47_hz66 (sGlobal47_hz67 hc) (by norm_num) (by norm_num)

theorem sGlobal47_hz69 : B (1524735695971823534271 / 125000000000000000) (609894278388729413841 / 50000000000000000) ((s3am 12225 46)^2) := bsq sGlobal47_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal47_hz70 : B (1524735695971823534271 / 62500000000000000) (609894278388729413841 / 25000000000000000) ((2 : ℝ) * ((s3am 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal47_hz69 (by norm_num) (by norm_num)

theorem sGlobal47_hz71 {c : ℝ} (hc : B (29 / 50) (117 / 200) c) : B (669052338238616501 / 1000000000000000000) (134508047644612911 / 200000000000000000) ((((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) / ((2 : ℝ) * ((s3am 12225 46)^2))) := bdiv (sGlobal47_hz68 hc) sGlobal47_hz70 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal47_hz72 {c : ℝ} (hc : B (29 / 50) (117 / 200) c) : B (669052338238616501 / 1000000000000000000) (134508047644612911 / 200000000000000000) (s3c1 12225 46 c) := by
    convert (sGlobal47_hz71 hc) using 1 <;>
      norm_num [s3c1] <;> ring

theorem sGlobal47_hz73 {c : ℝ} (hc : B (29 / 50) (117 / 200) c) : B (2722451012134883 / 3906250000000000) (139781100012904567 / 200000000000000000) (kdot c) := bkdot (sGlobal47_hz38 hc) sGlobal47_hz39.1 sGlobal47_hz47.2

theorem sGlobal47_hz74 : B (733299810479554311 / 1000000000000000000) (366649905239777157 / 500000000000000000) (kdot ((669052338238616501 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (445291782600019399 / 1000000000000000000)) (a := (104732919513554717 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (222645891300009699 / 500000000000000000)) (a := (209465839027109433 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal47_hz75 : B (367398404584862113 / 500000000000000000) (183699202292431057 / 250000000000000000) (kdot ((134508047644612911 / 200000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (442476982047513913 / 1000000000000000000)) (a := (83316039602096639 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (55309622755939239 / 125000000000000000)) (a := (416580198010483193 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal47_hz76 {c : ℝ} (hc : B (29 / 50) (117 / 200) c) : B (733299810479554311 / 1000000000000000000) (183699202292431057 / 250000000000000000) (kdot (s3c1 12225 46 c)) := bkdot (sGlobal47_hz72 hc) sGlobal47_hz74.1 sGlobal47_hz75.2

theorem sGlobal47_hz77 {c : ℝ} (hc : B (29 / 50) (117 / 200) c) : B (841 / 2500) (13689 / 40000) (c^2) := bsq (sGlobal47_hz38 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal47_hz78 {c : ℝ} (hc : B (29 / 50) (117 / 200) c) : B (26311 / 40000) (1659 / 2500) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (sGlobal47_hz77 hc) (by norm_num) (by norm_num)

theorem sGlobal47_hz79 {c : ℝ} (hc : B (29 / 50) (117 / 200) c) : B (405516645774251787 / 500000000000000000) (814616474176652041 / 1000000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (sGlobal47_hz78 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal47_hz80 : B (39119999999999765769 / 1600000000000000) (3912000000000000489 / 160000000000000) ((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (149450625 : ℝ)) sGlobal47_hz10 (by norm_num) (by norm_num)

theorem sGlobal47_hz81 {c : ℝ} (hc : B (29 / 50) (117 / 200) c) : B (141311897948883789 / 250000000000000000) (71167491780653931 / 125000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (sGlobal47_hz79 hc) (sGlobal47_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal47_hz82 {c : ℝ} (hc : B (29 / 50) (117 / 200) c) : B (3455075904850187953783 / 250000000000000000) (6960180696147955321823 / 500000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) := bmul sGlobal47_hz80 (sGlobal47_hz81 hc) (by norm_num) (by norm_num)

theorem sGlobal47_hz83 {c : ℝ} (hc : B (29 / 50) (117 / 200) c) : B (3455075904850187953783 / 500000000000000000) (6960180696147955321823 / 1000000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) / (2 : ℝ)) := bdiv (sGlobal47_hz82 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal47_hz84 {c : ℝ} (hc : B (29 / 50) (117 / 200) c) : B (3455075904850187953783 / 500000000000000000) (6960180696147955321823 / 1000000000000000000) (s3Cpa 12225 c) := by
    convert (sGlobal47_hz83 hc) using 1 <;>
      norm_num [s3Cpa, mA] <;> ring

theorem sGlobal47_hz85 {c : ℝ} (hc : B (29 / 50) (117 / 200) c) : B (258159914724069289 / 1000000000000000000) (64825119294652741 / 250000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (sGlobal47_hz79 hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal47_hz86 {c : ℝ} (hc : B (29 / 50) (117 / 200) c) : B (404229526281787427 / 1000000000000000000) (408859717537745859 / 1000000000000000000) (c * (kdot c)) := bmul (sGlobal47_hz38 hc) (sGlobal47_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal47_hz87 {c : ℝ} (hc : B (29 / 50) (117 / 200) c) : B (-15069980281367657 / 100000000000000000) (-144929049103176463 / 1000000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (sGlobal47_hz85 hc) (sGlobal47_hz86 hc) (by norm_num) (by norm_num)

theorem sGlobal47_hz88 {c : ℝ} (hc : B (29 / 50) (117 / 200) c) : B (-3684610178794392597077 / 1000000000000000000) (-27683712895098775809 / 7812500000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) := bmul sGlobal47_hz80 (sGlobal47_hz87 hc) (by norm_num) (by norm_num)

theorem sGlobal47_hz89 {c : ℝ} (hc : B (29 / 50) (117 / 200) c) : B (-1842305089397196298539 / 1000000000000000000) (-27683712895098775809 / 15625000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) / (2 : ℝ)) := bdiv (sGlobal47_hz88 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal47_hz90 {c : ℝ} (hc : B (29 / 50) (117 / 200) c) : B (-1842305089397196298539 / 1000000000000000000) (-27683712895098775809 / 15625000000000000) (s3Cpp 12225 c) := by
    convert (sGlobal47_hz89 hc) using 1 <;>
      norm_num [s3Cpp, mA] <;> ring

theorem sGlobal47_hz91 {c : ℝ} (hc : B (29 / 50) (117 / 200) c) : B (7025296919634113615967 / 1000000000000000000) (7075325806081693734049 / 1000000000000000000) ((s3Cpa 12225 c) + (s3r1 12225 46)) := badd (sGlobal47_hz84 hc) sGlobal47_hz33 (by norm_num) (by norm_num)

theorem sGlobal47_hz92 {c : ℝ} (hc : B (29 / 50) (117 / 200) c) : B (31804781117667882277 / 500000000000000000) (32031270873364758403 / 500000000000000000) (((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) := bdiv (sGlobal47_hz91 hc) sGlobal47_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal47_hz93 {c : ℝ} (hc : B (29 / 50) (117 / 200) c) : B (31866122630414912483 / 500000000000000000) (64185224772223577229 / 1000000000000000000) ((((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) + (s3e0 12225 46)) := badd (sGlobal47_hz92 hc) sGlobal47_hz16 (by norm_num) (by norm_num)

theorem sGlobal47_hz94 {c : ℝ} (hc : B (29 / 50) (117 / 200) c) : B (31866122630414912483 / 500000000000000000) (64185224772223577229 / 1000000000000000000) (s3Lam 12225 46 c) := by
    convert (sGlobal47_hz93 hc) using 1 <;>
      norm_num [s3Lam] <;> ring

theorem sGlobal47_hz95 {c : ℝ} (hc : B (29 / 50) (117 / 200) c) : B (-1765541682774704492939 / 1000000000000000000) (-847497109331914688479 / 500000000000000000) ((s3Cpp 12225 c) + (s3rpp 12225 46)) := badd (sGlobal47_hz90 hc) sGlobal47_hz37 (by norm_num) (by norm_num)

theorem sGlobal47_hz96 {c : ℝ} (hc : B (29 / 50) (117 / 200) c) : B (-1297314394958998326441 / 1000000000000000000) (-847497109331914688479 / 1000000000000000000) (if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) := bweaken (bfirst (sGlobal47_hz95 hc) (sGlobal47_hz76 hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem sGlobal47_hz97 {c : ℝ} (hc : B (29 / 50) (117 / 200) c) : B (253862442874160355257 / 62500000000000000) (4119743079060863161379 / 1000000000000000000) ((s3Lam 12225 46 c)^2) := bsq (sGlobal47_hz94 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal47_hz98 {c : ℝ} (hc : B (29 / 50) (117 / 200) c) : B (447631031302560099 / 1000000000000000000) (226155186014568211 / 500000000000000000) ((s3c1 12225 46 c)^2) := bsq (sGlobal47_hz72 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal47_hz99 {c : ℝ} (hc : B (29 / 50) (117 / 200) c) : B (273844813985431789 / 500000000000000000) (552368968697439901 / 1000000000000000000) ((1 : ℝ) - ((s3c1 12225 46 c)^2)) := bsub (bpoint (1 : ℝ)) (sGlobal47_hz98 hc) (by norm_num) (by norm_num)

theorem sGlobal47_hz100 {c : ℝ} (hc : B (29 / 50) (117 / 200) c) : B (740060556961971577 / 1000000000000000000) (23225477842093877 / 31250000000000000) (√((1 : ℝ) - ((s3c1 12225 46 c)^2))) := bsqrt (sGlobal47_hz99 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal47_hz101 {c : ℝ} (hc : B (29 / 50) (117 / 200) c) : B (2324968808963300619 / 1000000000000000000) (1167439849037354367 / 500000000000000000) (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))) := bmul pi_mem (sGlobal47_hz100 hc) (by norm_num) (by norm_num)

theorem sGlobal47_hz102 {c : ℝ} (hc : B (29 / 50) (117 / 200) c) : B (869809071819810952623 / 500000000000000000) (177195627880179998577 / 100000000000000000) (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2))))) := bdiv (sGlobal47_hz97 hc) (sGlobal47_hz101 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal47_hz103 {c : ℝ} (hc : B (29 / 50) (117 / 200) c) : B (88460749736124715761 / 200000000000000000) (924459169469885297291 / 1000000000000000000) ((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) := badd (sGlobal47_hz96 hc) (sGlobal47_hz102 hc) (by norm_num) (by norm_num)

theorem sGlobal47_hz104 : B (3762781186094069 / 250000000000000000) (376278118609407 / 25000000000000000) ((s3e0 12225 46)^2) := bsq sGlobal47_hz16 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal47_hz105 {c : ℝ} (hc : B (29 / 50) (117 / 200) c) : B (442318799805367955081 / 1000000000000000000) (924474220594629673571 / 1000000000000000000) (((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) := badd (sGlobal47_hz103 hc) sGlobal47_hz104 (by norm_num) (by norm_num)

theorem sGlobal47_hz106 {c : ℝ} (hc : B (29 / 50) (117 / 200) c) : B (120203968314153806303 / 250000000000000000) (962971294048753943587 / 1000000000000000000) ((((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) + (s3rs 12225 46 maskSlack)) := badd (sGlobal47_hz105 hc) sGlobal47_hz29 (by norm_num) (by norm_num)

theorem sGlobal47_hz107 {c : ℝ} (hc : B (29 / 50) (117 / 200) c) : B (120203968314153806303 / 250000000000000000) (962971294048753943587 / 1000000000000000000) (s3U 12225 46 maskSlack c) := by
    convert (sGlobal47_hz106 hc) using 1 <;>
      norm_num [s3U] <;> ring

theorem sGlobal47_hz108 {c : ℝ} (hc : B (29 / 50) (117 / 200) c) : B (-1919068496019688573357 / 1000000000000000000) (-57766282247150420543 / 31250000000000000) ((s3Cpp 12225 c) - (s3rpp 12225 46)) := bsub (sGlobal47_hz90 hc) sGlobal47_hz37 (by norm_num) (by norm_num)

theorem sGlobal47_hz109 {c : ℝ} (hc : B (29 / 50) (117 / 200) c) : B (-1919068496019688573357 / 1000000000000000000) (-57766282247150420543 / 31250000000000000) (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ)) := bweaken (bmin (sGlobal47_hz108 hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem sGlobal47_hz110 {c : ℝ} (hc : B (29 / 50) (117 / 200) c) : B (-1410125407453408783843 / 1000000000000000000) (-271104024473240615089 / 200000000000000000) ((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) := bmul (sGlobal47_hz76 hc) (sGlobal47_hz109 hc) (by norm_num) (by norm_num)

theorem sGlobal47_hz111 {c : ℝ} (hc : B (29 / 50) (117 / 200) c) : B (-1410140458578153160123 / 1000000000000000000) (-1355535173490947451721 / 1000000000000000000) (((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) := bsub (sGlobal47_hz110 hc) sGlobal47_hz104 (by norm_num) (by norm_num)

theorem sGlobal47_hz112 {c : ℝ} (hc : B (29 / 50) (117 / 200) c) : B (-1448637532032277430139 / 1000000000000000000) (-348508061735548680463 / 250000000000000000) ((((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) - (s3rs 12225 46 maskSlack)) := bsub (sGlobal47_hz111 hc) sGlobal47_hz29 (by norm_num) (by norm_num)

theorem sGlobal47_hz113 {c : ℝ} (hc : B (29 / 50) (117 / 200) c) : B (-1448637532032277430139 / 1000000000000000000) (-348508061735548680463 / 250000000000000000) (s3L 12225 46 maskSlack c) := by
    convert (sGlobal47_hz112 hc) using 1 <;>
      norm_num [s3L] <;> ring

theorem sGlobal47_hz114 {c : ℝ} (hc : B (29 / 50) (117 / 200) c) : B 0 (962971294048753943587 / 1000000000000000000) |(s3U 12225 46 maskSlack c)| := bweaken (babs (sGlobal47_hz107 hc)) (by norm_num) (by norm_num)

theorem sGlobal47_hz115 {c : ℝ} (hc : B (29 / 50) (117 / 200) c) : B 0 (1448637532032277430139 / 1000000000000000000) |(s3L 12225 46 maskSlack c)| := bweaken (babs (sGlobal47_hz113 hc)) (by norm_num) (by norm_num)

theorem sGlobal47_hz116 {c : ℝ} (hc : B (29 / 50) (117 / 200) c) : B 0 (1448637532032277430139 / 1000000000000000000) (max |(s3U 12225 46 maskSlack c)| |(s3L 12225 46 maskSlack c)|) := bweaken (bmax (sGlobal47_hz114 hc) (sGlobal47_hz115 hc)) (by norm_num) (by norm_num)

theorem sGlobal47_hz117 {c : ℝ} (hc : B (29 / 50) (117 / 200) c) : B 0 (1448637532032277430139 / 1000000000000000000) (s3nks 12225 46 maskSlack c) := by
    convert (sGlobal47_hz116 hc) using 1 <;>
      norm_num [s3nks] <;> ring

theorem sGlobal47 {c : ℝ} (hc : B (29 / 50) (117 / 200) c) :
    0 < s3am 12225 46 ∧ 0 ≤ s3dm 12225 46 c ∧
    s3dm 12225 46 c ^ 2 ≤ 2 * s3ap 12225 46 ^ 2 ∧ s3c1 12225 46 c < 1 ∧
    0 ≤ s3Cpa 12225 c - s3r1 12225 46 ∧
    s3e0 12225 46 ≤ (s3Cpa 12225 c - s3r1 12225 46) / s3ap 12225 46 ∧
    s3nks 12225 46 maskSlack c ≤ 12225 * (59249 / 500000) := by

  refine ⟨lt_of_lt_of_le (by norm_num) sGlobal47_hz14.1,
    le_trans (by norm_num) (sGlobal47_hz64 hc).1, ?_,
    lt_of_le_of_lt (sGlobal47_hz72 hc).2 (by norm_num), ?_, ?_,
    le_trans (sGlobal47_hz117 hc).2 (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (sGlobal47_hz64 hc).1) (sGlobal47_hz64 hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) sGlobal47_hz9.1 2
    nlinarith only [h1, h2]
  · linarith only [(sGlobal47_hz84 hc).1, sGlobal47_hz33.2]
  · have hap : 0 < s3ap 12225 46 := lt_of_lt_of_le (by norm_num) sGlobal47_hz9.1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul sGlobal47_hz16.2 sGlobal47_hz9.2 (le_trans (by norm_num) sGlobal47_hz9.1) (by norm_num)
    linarith only [h, (sGlobal47_hz84 hc).1, sGlobal47_hz33.2]

end BstLean.Part255
