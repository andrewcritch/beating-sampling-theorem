import BstLean.Part255SGlobal40
import BstLean.Part255Numeric10
namespace BstLean.Part255
open Real BstLean.Part130 BstLean.Part182 BstLean.Part197 BstLean.Part246
theorem sGlobal44_hz0 : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal44_hz1 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) ((√(23 : ℝ)) / (12225 : ℝ)) := bdiv sGlobal44_hz0 (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal44_hz2 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) maskSlack := by
    convert sGlobal44_hz1 using 1 <;>
      norm_num [maskSlack] <;> ring

theorem sGlobal44_hz3 : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal44_hz4 : B (6395294793910793 / 500000000000000000) (12790589587821587 / 1000000000000000000) (√((2 / 12225) : ℝ)) := bsqrt (bpoint ((2 / 12225) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal44_hz5 : B (7230130686979 / 62500000000000000) (23136418198333 / 200000000000000000) (√((2 / 149450625) : ℝ)) := bsqrt (bpoint ((2 / 149450625) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal44_hz6 : B (2211334438749598093 / 20000000000000000) (110566721937479904651 / 1000000000000000000) (√(12225 : ℝ)) := bsqrt (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal44_hz7 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))) := bmul sGlobal44_hz3 sGlobal44_hz4 (by norm_num) (by norm_num)

theorem sGlobal44_hz8 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) ((√(12225 : ℝ)) + ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := badd sGlobal44_hz6 sGlobal44_hz7 (by norm_num) (by norm_num)

theorem sGlobal44_hz9 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) (s3ap 12225 46) := by
    convert sGlobal44_hz8 using 1 <;>
      norm_num [s3ap, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal44_hz10 : B (163599182004089 / 1000000000000000000) (16359918200409 / 100000000000000000) ((2 : ℝ) / (12225 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal44_hz11 : B (1222499983640081799591 / 100000000000000000) (12224999836400817995911 / 1000000000000000000) ((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ))) := bsub (bpoint (12225 : ℝ)) sGlobal44_hz10 (by norm_num) (by norm_num)

theorem sGlobal44_hz12 : B (110566721197658827907 / 1000000000000000000) (27641680299414706977 / 250000000000000000) (√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) := bsqrt sGlobal44_hz11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal44_hz13 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) ((√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) - ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bsub sGlobal44_hz12 sGlobal44_hz7 (by norm_num) (by norm_num)

theorem sGlobal44_hz14 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) (s3am 12225 46) := by
    convert sGlobal44_hz13 using 1 <;>
      norm_num [s3am, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal44_hz15 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√((2 / 12225) : ℝ)) * (√(92 : ℝ))) := bmul sGlobal44_hz4 sGlobal44_hz3 (by norm_num) (by norm_num)

theorem sGlobal44_hz16 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) (s3e0 12225 46) := by
    convert sGlobal44_hz15 using 1 <;>
      norm_num [s3e0, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal44_hz17 : B (250196148528560847 / 500000000000000000) (100078459411424339 / 200000000000000000) (((1 / 2) : ℝ) + maskSlack) := badd (bpoint ((1 / 2) : ℝ)) sGlobal44_hz2 (by norm_num) (by norm_num)

theorem sGlobal44_hz18 : B (59827153232297998295487 / 800000000000000) (23930861292919199366019 / 320000000000000) ((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack)) := bmul (bpoint (149450625 : ℝ)) sGlobal44_hz17 (by norm_num) (by norm_num)

theorem sGlobal44_hz19 : B (1729554180017180009583 / 200000000000000000) (8647770900085900056557 / 1000000000000000000) (√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) := bsqrt sGlobal44_hz18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal44_hz20 : B (4328681281566262743499 / 500000000000000000) (8657362563132525495641 / 1000000000000000000) ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))) := badd sGlobal44_hz19 sGlobal44_hz3 (by norm_num) (by norm_num)

theorem sGlobal44_hz21 : B (110732771457999278473 / 1000000000000000000) (55366385728999643621 / 500000000000000000) ((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ)))) := bmul sGlobal44_hz4 sGlobal44_hz20 (by norm_num) (by norm_num)

theorem sGlobal44_hz22 : B (209099159 / 15625000000000000) (13382346177 / 1000000000000000000) ((2 : ℝ) / (149450625 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (149450625 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal44_hz23 : B (2452349334953899930479 / 200000000000000000) (12261746674769501594427 / 1000000000000000000) (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2) := bsq sGlobal44_hz21 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal44_hz24 : B (82045469362091 / 500000000000000000) (32818187747289 / 200000000000000000) (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2)) := bmul sGlobal44_hz22 sGlobal44_hz23 (by norm_num) (by norm_num)

theorem sGlobal44_hz25 : B (82045469362091 / 250000000000000000) (32818187747289 / 100000000000000000) ((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) := bmul (bpoint (2 : ℝ)) sGlobal44_hz24 (by norm_num) (by norm_num)

theorem sGlobal44_hz26 : B (117258080744995992792057 / 1000000000000000000) (58629040372497996396029 / 500000000000000000) (√(13749457500 : ℝ)) := bsqrt (bpoint (13749457500 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal44_hz27 : B (117304080744995992792057 / 1000000000000000000) (58652040372497996396029 / 500000000000000000) ((√(13749457500 : ℝ)) + (46 : ℝ)) := badd sGlobal44_hz26 (bpoint (46 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal44_hz28 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal44_hz25 sGlobal44_hz27 (by norm_num) (by norm_num)

theorem sGlobal44_hz29 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (s3rs 12225 46 maskSlack) := by
    convert sGlobal44_hz28 using 1 <;>
      norm_num [s3rs, s3pp, s3K, mA, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal44_hz30 : B (490797546012267 / 1000000000000000000) (49079754601227 / 100000000000000000) ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (3 : ℝ)) sGlobal44_hz10 (by norm_num) (by norm_num)

theorem sGlobal44_hz31 : B (490797546012267 / 500000000000000000) (49079754601227 / 50000000000000000) ((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal44_hz30 (by norm_num) (by norm_num)

theorem sGlobal44_hz32 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal44_hz31 sGlobal44_hz27 (by norm_num) (by norm_num)

theorem sGlobal44_hz33 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (s3r1 12225 46) := by
    convert sGlobal44_hz32 using 1 <;>
      norm_num [s3r1, mA] <;> ring

theorem sGlobal44_hz34 : B (163599182004089 / 500000000000000000) (16359918200409 / 50000000000000000) ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (2 : ℝ)) sGlobal44_hz10 (by norm_num) (by norm_num)

theorem sGlobal44_hz35 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal44_hz34 (by norm_num) (by norm_num)

theorem sGlobal44_hz36 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal44_hz35 sGlobal44_hz27 (by norm_num) (by norm_num)

theorem sGlobal44_hz37 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (s3rpp 12225 46) := by
    convert sGlobal44_hz36 using 1 <;>
      norm_num [s3rpp, mA] <;> ring

theorem sGlobal44_hz38 {c : ℝ} (hc : B (113 / 200) (57 / 100) c) : B (113 / 200) (57 / 100) c := hc

theorem sGlobal44_hz39 : B (345561920304089723 / 500000000000000000) (172780960152045017 / 250000000000000000) (kdot ((113 / 200))) := by
    constructor
    · apply bkdot_lower (q := (527214635196610611 / 1000000000000000000)) (a := (97036307321437347 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (52721463519661061 / 100000000000000000)) (a := (3032384603794911 / 6250000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal44_hz40 : B (12769 / 40000) (12769 / 40000) (((113 / 200) : ℝ)^2) := bsq (bpoint ((113 / 200) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal44_hz41 : B (27231 / 40000) (27231 / 40000) ((1 : ℝ) - (((113 / 200) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal44_hz40 (by norm_num) (by norm_num)

theorem sGlobal44_hz42 : B (165018180816539121 / 200000000000000000) (412545452041347803 / 500000000000000000) (√((1 : ℝ) - (((113 / 200) : ℝ)^2))) := bsqrt sGlobal44_hz41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal44_hz43 : B (262634591769843783 / 1000000000000000000) (52526918353968757 / 200000000000000000) ((√((1 : ℝ) - (((113 / 200) : ℝ)^2))) / Real.pi) := bdiv sGlobal44_hz42 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal44_hz44 : B (195242484971810693 / 500000000000000000) (390484969943621739 / 1000000000000000000) (((113 / 200) : ℝ) * (kdot ((113 / 200)))) := bmul (bpoint ((113 / 200) : ℝ)) sGlobal44_hz39 (by norm_num) (by norm_num)

theorem sGlobal44_hz45 : B (653119561713465169 / 1000000000000000000) (163279890428366381 / 250000000000000000) (((√((1 : ℝ) - (((113 / 200) : ℝ)^2))) / Real.pi) + (((113 / 200) : ℝ) * (kdot ((113 / 200))))) := badd sGlobal44_hz43 sGlobal44_hz44 (by norm_num) (by norm_num)

theorem sGlobal44_hz46 : B (653119561713465169 / 1000000000000000000) (163279890428366381 / 250000000000000000) (kappa ((113 / 200))) := by rw [kappa_eq]; exact sGlobal44_hz45

theorem sGlobal44_hz47 : B (173264202435670071 / 250000000000000000) (346528404871340359 / 500000000000000000) (kdot ((57 / 100))) := by
    constructor
    · apply bkdot_lower (q := (10466811363896291 / 20000000000000000)) (a := (120536308947726227 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (523340568194814549 / 1000000000000000000)) (a := (120536308947726057 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal44_hz48 : B (3249 / 10000) (3249 / 10000) (((57 / 100) : ℝ)^2) := bsq (bpoint ((57 / 100) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal44_hz49 : B (6751 / 10000) (6751 / 10000) ((1 : ℝ) - (((57 / 100) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal44_hz48 (by norm_num) (by norm_num)

theorem sGlobal44_hz50 : B (410822346032929421 / 500000000000000000) (821644692065858843 / 1000000000000000000) (√((1 : ℝ) - (((57 / 100) : ℝ)^2))) := bsqrt sGlobal44_hz49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal44_hz51 : B (130768814207499631 / 500000000000000000) (261537628414999263 / 1000000000000000000) ((√((1 : ℝ) - (((57 / 100) : ℝ)^2))) / Real.pi) := bdiv sGlobal44_hz50 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal44_hz52 : B (395042381553327761 / 1000000000000000000) (39504238155332801 / 100000000000000000) (((57 / 100) : ℝ) * (kdot ((57 / 100)))) := bmul (bpoint ((57 / 100) : ℝ)) sGlobal44_hz47 (by norm_num) (by norm_num)

theorem sGlobal44_hz53 : B (656580009968327023 / 1000000000000000000) (656580009968327273 / 1000000000000000000) (((√((1 : ℝ) - (((57 / 100) : ℝ)^2))) / Real.pi) + (((57 / 100) : ℝ) * (kdot ((57 / 100))))) := badd sGlobal44_hz51 sGlobal44_hz52 (by norm_num) (by norm_num)

theorem sGlobal44_hz54 : B (656580009968327023 / 1000000000000000000) (656580009968327273 / 1000000000000000000) (kappa ((57 / 100))) := by rw [kappa_eq]; exact sGlobal44_hz53

theorem sGlobal44_hz55 {c : ℝ} (hc : B (113 / 200) (57 / 100) c) : B (653119561713465169 / 1000000000000000000) (656580009968327273 / 1000000000000000000) (kappa c) := bkappa (sGlobal44_hz38 hc) (by norm_num) (by norm_num) sGlobal44_hz46.1 sGlobal44_hz54.2

theorem sGlobal44_hz56 : B 24450 24450 ((2 : ℝ) * (12225 : ℝ)) := bmul (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal44_hz57 {c : ℝ} (hc : B (113 / 200) (57 / 100) c) : B (343419990031672727 / 1000000000000000000) (346880438286534831 / 1000000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (sGlobal44_hz55 hc) (by norm_num) (by norm_num)

theorem sGlobal44_hz58 {c : ℝ} (hc : B (113 / 200) (57 / 100) c) : B (167932375125487963503 / 20000000000000000) (169624534322115532359 / 20000000000000000) (((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) := bmul sGlobal44_hz56 (sGlobal44_hz57 hc) (by norm_num) (by norm_num)

theorem sGlobal44_hz59 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (4 : ℝ)) sGlobal44_hz10 (by norm_num) (by norm_num)

theorem sGlobal44_hz60 {c : ℝ} (hc : B (113 / 200) (57 / 100) c) : B (839661810187767015879 / 100000000000000000) (4240613030854524300797 / 500000000000000000) ((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bsub (sGlobal44_hz58 hc) sGlobal44_hz59 (by norm_num) (by norm_num)

theorem sGlobal44_hz61 {c : ℝ} (hc : B (113 / 200) (57 / 100) c) : B (22908265568727685433 / 250000000000000000) (92093572314842085301 / 1000000000000000000) (√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) := bsqrt (sGlobal44_hz60 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal44_hz62 : B (30670756373515103 / 125000000000000000) (122683025494060423 / 500000000000000000) ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal44_hz7 (by norm_num) (by norm_num)

theorem sGlobal44_hz63 {c : ℝ} (hc : B (113 / 200) (57 / 100) c) : B (45693848111961310443 / 500000000000000000) (91848206263853964477 / 1000000000000000000) ((√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) - ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))))) := bsub (sGlobal44_hz61 hc) sGlobal44_hz62 (by norm_num) (by norm_num)

theorem sGlobal44_hz64 {c : ℝ} (hc : B (113 / 200) (57 / 100) c) : B (45693848111961310443 / 500000000000000000) (91848206263853964477 / 1000000000000000000) (s3dm 12225 46 c) := by
    convert (sGlobal44_hz63 hc) using 1 <;>
      norm_num [s3dm, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal44_hz65 : B (6126072185528622723889 / 500000000000000000) (2450428874211449090087 / 200000000000000000) ((s3ap 12225 46)^2) := bsq sGlobal44_hz9 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal44_hz66 : B (6126072185528622723889 / 250000000000000000) (2450428874211449090087 / 100000000000000000) ((2 : ℝ) * ((s3ap 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal44_hz65 (by norm_num) (by norm_num)

theorem sGlobal44_hz67 {c : ℝ} (hc : B (113 / 200) (57 / 100) c) : B (8351711021115960860247 / 1000000000000000000) (421804649694373131801 / 50000000000000000) ((s3dm 12225 46 c)^2) := bsq (sGlobal44_hz64 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal44_hz68 {c : ℝ} (hc : B (113 / 200) (57 / 100) c) : B (1004262234264189266221 / 62500000000000000) (16152577720998530040623 / 1000000000000000000) (((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) := bsub sGlobal44_hz66 (sGlobal44_hz67 hc) (by norm_num) (by norm_num)

theorem sGlobal44_hz69 : B (1524735695971823534271 / 125000000000000000) (609894278388729413841 / 50000000000000000) ((s3am 12225 46)^2) := bsq sGlobal44_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal44_hz70 : B (1524735695971823534271 / 62500000000000000) (609894278388729413841 / 25000000000000000) ((2 : ℝ) * ((s3am 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal44_hz69 (by norm_num) (by norm_num)

theorem sGlobal44_hz71 {c : ℝ} (hc : B (113 / 200) (57 / 100) c) : B (658646765414710671 / 1000000000000000000) (26484225698381339 / 40000000000000000) ((((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) / ((2 : ℝ) * ((s3am 12225 46)^2))) := bdiv (sGlobal44_hz68 hc) sGlobal44_hz70 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal44_hz72 {c : ℝ} (hc : B (113 / 200) (57 / 100) c) : B (658646765414710671 / 1000000000000000000) (26484225698381339 / 40000000000000000) (s3c1 12225 46 c) := by
    convert (sGlobal44_hz71 hc) using 1 <;>
      norm_num [s3c1] <;> ring

theorem sGlobal44_hz73 {c : ℝ} (hc : B (113 / 200) (57 / 100) c) : B (345561920304089723 / 500000000000000000) (346528404871340359 / 500000000000000000) (kdot c) := bkdot (sGlobal44_hz38 hc) sGlobal44_hz39.1 sGlobal44_hz47.2

theorem sGlobal44_hz74 : B (728870827299893493 / 1000000000000000000) (145774165459978699 / 200000000000000000) (kdot ((658646765414710671 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (56706790954066171 / 125000000000000000)) (a := (425888708564266463 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (453654327632529367 / 1000000000000000000)) (a := (425888708564266461 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal44_hz75 : B (365168498465754699 / 500000000000000000) (3651684984657547 / 5000000000000000) (kdot ((26484225698381339 / 40000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (1803520774312691 / 4000000000000000)) (a := (423585654692465973 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (450880193578172749 / 1000000000000000000)) (a := (423585654692465971 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal44_hz76 {c : ℝ} (hc : B (113 / 200) (57 / 100) c) : B (728870827299893493 / 1000000000000000000) (3651684984657547 / 5000000000000000) (kdot (s3c1 12225 46 c)) := bkdot (sGlobal44_hz72 hc) sGlobal44_hz74.1 sGlobal44_hz75.2

theorem sGlobal44_hz77 {c : ℝ} (hc : B (113 / 200) (57 / 100) c) : B (12769 / 40000) (3249 / 10000) (c^2) := bsq (sGlobal44_hz38 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal44_hz78 {c : ℝ} (hc : B (113 / 200) (57 / 100) c) : B (6751 / 10000) (27231 / 40000) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (sGlobal44_hz77 hc) (by norm_num) (by norm_num)

theorem sGlobal44_hz79 {c : ℝ} (hc : B (113 / 200) (57 / 100) c) : B (410822346032929421 / 500000000000000000) (412545452041347803 / 500000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (sGlobal44_hz78 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal44_hz80 : B (39119999999999765769 / 1600000000000000) (3912000000000000489 / 160000000000000) ((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (149450625 : ℝ)) sGlobal44_hz10 (by norm_num) (by norm_num)

theorem sGlobal44_hz81 {c : ℝ} (hc : B (113 / 200) (57 / 100) c) : B (567858235195881309 / 1000000000000000000) (285917434865628597 / 500000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (sGlobal44_hz79 hc) (sGlobal44_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal44_hz82 {c : ℝ} (hc : B (113 / 200) (57 / 100) c) : B (6942066925269607436899 / 500000000000000000) (13981362564929240140971 / 1000000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) := bmul sGlobal44_hz80 (sGlobal44_hz81 hc) (by norm_num) (by norm_num)

theorem sGlobal44_hz83 {c : ℝ} (hc : B (113 / 200) (57 / 100) c) : B (6942066925269607436899 / 1000000000000000000) (3495340641232310035243 / 500000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) / (2 : ℝ)) := bdiv (sGlobal44_hz82 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal44_hz84 {c : ℝ} (hc : B (113 / 200) (57 / 100) c) : B (6942066925269607436899 / 1000000000000000000) (3495340641232310035243 / 500000000000000000) (s3Cpa 12225 c) := by
    convert (sGlobal44_hz83 hc) using 1 <;>
      norm_num [s3Cpa, mA] <;> ring

theorem sGlobal44_hz85 {c : ℝ} (hc : B (113 / 200) (57 / 100) c) : B (130768814207499631 / 500000000000000000) (52526918353968757 / 200000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (sGlobal44_hz79 hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal44_hz86 {c : ℝ} (hc : B (113 / 200) (57 / 100) c) : B (195242484971810693 / 500000000000000000) (39504238155332801 / 100000000000000000) (c * (kdot c)) := bmul (sGlobal44_hz38 hc) (sGlobal44_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal44_hz87 {c : ℝ} (hc : B (113 / 200) (57 / 100) c) : B (-33376188284582187 / 250000000000000000) (-127850378173777601 / 1000000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (sGlobal44_hz85 hc) (sGlobal44_hz86 hc) (by norm_num) (by norm_num)

theorem sGlobal44_hz88 {c : ℝ} (hc : B (113 / 200) (57 / 100) c) : B (-204011950889508643539 / 62500000000000000) (-3125941746348843627873 / 1000000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) := bmul sGlobal44_hz80 (sGlobal44_hz87 hc) (by norm_num) (by norm_num)

theorem sGlobal44_hz89 {c : ℝ} (hc : B (113 / 200) (57 / 100) c) : B (-204011950889508643539 / 125000000000000000) (-97685679573401363371 / 62500000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) / (2 : ℝ)) := bdiv (sGlobal44_hz88 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal44_hz90 {c : ℝ} (hc : B (113 / 200) (57 / 100) c) : B (-204011950889508643539 / 125000000000000000) (-97685679573401363371 / 62500000000000000) (s3Cpp 12225 c) := by
    convert (sGlobal44_hz89 hc) using 1 <;>
      norm_num [s3Cpp, mA] <;> ring

theorem sGlobal44_hz91 {c : ℝ} (hc : B (113 / 200) (57 / 100) c) : B (70572120352033451453 / 10000000000000000) (888228299049794810339 / 125000000000000000) ((s3Cpa 12225 c) + (s3r1 12225 46)) := badd (sGlobal44_hz84 hc) sGlobal44_hz33 (by norm_num) (by norm_num)

theorem sGlobal44_hz92 {c : ℝ} (hc : B (113 / 200) (57 / 100) c) : B (7987316644700039219 / 125000000000000000) (32169352506477082511 / 500000000000000000) (((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) := bdiv (sGlobal44_hz91 hc) sGlobal44_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal44_hz93 {c : ℝ} (hc : B (113 / 200) (57 / 100) c) : B (16005304045773593541 / 250000000000000000) (12892277607689645089 / 200000000000000000) ((((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) + (s3e0 12225 46)) := badd (sGlobal44_hz92 hc) sGlobal44_hz16 (by norm_num) (by norm_num)

theorem sGlobal44_hz94 {c : ℝ} (hc : B (113 / 200) (57 / 100) c) : B (16005304045773593541 / 250000000000000000) (12892277607689645089 / 200000000000000000) (s3Lam 12225 46 c) := by
    convert (sGlobal44_hz93 hc) using 1 <;>
      norm_num [s3Lam] <;> ring

theorem sGlobal44_hz95 {c : ℝ} (hc : B (113 / 200) (57 / 100) c) : B (-194416525061697167839 / 125000000000000000) (-743103733275964769559 / 500000000000000000) ((s3Cpp 12225 c) + (s3rpp 12225 46)) := badd (sGlobal44_hz90 hc) sGlobal44_hz37 (by norm_num) (by norm_num)

theorem sGlobal44_hz96 {c : ℝ} (hc : B (113 / 200) (57 / 100) c) : B (-1135916648539355558653 / 1000000000000000000) (-743103733275964769559 / 1000000000000000000) (if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) := bweaken (bfirst (sGlobal44_hz95 hc) (sGlobal44_hz76 hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem sGlobal44_hz97 {c : ℝ} (hc : B (113 / 200) (57 / 100) c) : B (4098716121562504987 / 1000000000000000) (2077635273921697979061 / 500000000000000000) ((s3Lam 12225 46 c)^2) := bsq (sGlobal44_hz94 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal44_hz98 {c : ℝ} (hc : B (113 / 200) (57 / 100) c) : B (108453890397815227 / 250000000000000000) (219191940888375789 / 500000000000000000) ((s3c1 12225 46 c)^2) := bsq (sGlobal44_hz72 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal44_hz99 {c : ℝ} (hc : B (113 / 200) (57 / 100) c) : B (280808059111624211 / 500000000000000000) (141546109602184773 / 250000000000000000) ((1 : ℝ) - ((s3c1 12225 46 c)^2)) := bsub (bpoint (1 : ℝ)) (sGlobal44_hz98 hc) (by norm_num) (by norm_num)

theorem sGlobal44_hz100 {c : ℝ} (hc : B (113 / 200) (57 / 100) c) : B (187352628454881909 / 250000000000000000) (150490456628816047 / 200000000000000000) (√((1 : ℝ) - ((s3c1 12225 46 c)^2))) := bsqrt (sGlobal44_hz99 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal44_hz101 {c : ℝ} (hc : B (113 / 200) (57 / 100) c) : B (2354342564738380243 / 1000000000000000000) (590974641225577369 / 250000000000000000) (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))) := bmul pi_mem (sGlobal44_hz100 hc) (by norm_num) (by norm_num)

theorem sGlobal44_hz102 {c : ℝ} (hc : B (113 / 200) (57 / 100) c) : B (69355194548830205317 / 40000000000000000) (1764938802907443003673 / 1000000000000000000) (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2))))) := bdiv (sGlobal44_hz97 hc) (sGlobal44_hz101 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal44_hz103 {c : ℝ} (hc : B (113 / 200) (57 / 100) c) : B (2335793809302342087 / 3906250000000000) (510917534815739117057 / 500000000000000000) ((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) := badd (sGlobal44_hz96 hc) (sGlobal44_hz102 hc) (by norm_num) (by norm_num)

theorem sGlobal44_hz104 : B (3762781186094069 / 250000000000000000) (376278118609407 / 25000000000000000) ((s3e0 12225 46)^2) := bsq sGlobal44_hz16 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal44_hz105 {c : ℝ} (hc : B (113 / 200) (57 / 100) c) : B (149494566576535987637 / 250000000000000000) (510925060378111305197 / 500000000000000000) (((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) := badd (sGlobal44_hz103 hc) sGlobal44_hz104 (by norm_num) (by norm_num)

theorem sGlobal44_hz106 {c : ℝ} (hc : B (113 / 200) (57 / 100) c) : B (636475339757391220679 / 1000000000000000000) (106034719421034688041 / 100000000000000000) ((((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) + (s3rs 12225 46 maskSlack)) := badd (sGlobal44_hz105 hc) sGlobal44_hz29 (by norm_num) (by norm_num)

theorem sGlobal44_hz107 {c : ℝ} (hc : B (113 / 200) (57 / 100) c) : B (636475339757391220679 / 1000000000000000000) (106034719421034688041 / 100000000000000000) (s3U 12225 46 maskSlack c) := by
    convert (sGlobal44_hz106 hc) using 1 <;>
      norm_num [s3U] <;> ring

theorem sGlobal44_hz108 {c : ℝ} (hc : B (113 / 200) (57 / 100) c) : B (-170885901373856142313 / 100000000000000000) (-102483392487307101221 / 62500000000000000) ((s3Cpp 12225 c) - (s3rpp 12225 46)) := bsub (sGlobal44_hz90 hc) sGlobal44_hz37 (by norm_num) (by norm_num)

theorem sGlobal44_hz109 {c : ℝ} (hc : B (113 / 200) (57 / 100) c) : B (-170885901373856142313 / 100000000000000000) (-102483392487307101221 / 62500000000000000) (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ)) := bweaken (bmin (sGlobal44_hz108 hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem sGlobal44_hz110 {c : ℝ} (hc : B (113 / 200) (57 / 100) c) : B (-1248042960273161913703 / 1000000000000000000) (-597577240533785731339 / 500000000000000000) ((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) := bmul (sGlobal44_hz76 hc) (sGlobal44_hz109 hc) (by norm_num) (by norm_num)

theorem sGlobal44_hz111 {c : ℝ} (hc : B (113 / 200) (57 / 100) c) : B (-1248058011397906289983 / 1000000000000000000) (-597584766096157919477 / 500000000000000000) (((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) := bsub (sGlobal44_hz110 hc) sGlobal44_hz104 (by norm_num) (by norm_num)

theorem sGlobal44_hz112 {c : ℝ} (hc : B (113 / 200) (57 / 100) c) : B (-1286555084852030559999 / 1000000000000000000) (-246733321128712621817 / 200000000000000000) ((((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) - (s3rs 12225 46 maskSlack)) := bsub (sGlobal44_hz111 hc) sGlobal44_hz29 (by norm_num) (by norm_num)

theorem sGlobal44_hz113 {c : ℝ} (hc : B (113 / 200) (57 / 100) c) : B (-1286555084852030559999 / 1000000000000000000) (-246733321128712621817 / 200000000000000000) (s3L 12225 46 maskSlack c) := by
    convert (sGlobal44_hz112 hc) using 1 <;>
      norm_num [s3L] <;> ring

theorem sGlobal44_hz114 {c : ℝ} (hc : B (113 / 200) (57 / 100) c) : B 0 (106034719421034688041 / 100000000000000000) |(s3U 12225 46 maskSlack c)| := bweaken (babs (sGlobal44_hz107 hc)) (by norm_num) (by norm_num)

theorem sGlobal44_hz115 {c : ℝ} (hc : B (113 / 200) (57 / 100) c) : B 0 (1286555084852030559999 / 1000000000000000000) |(s3L 12225 46 maskSlack c)| := bweaken (babs (sGlobal44_hz113 hc)) (by norm_num) (by norm_num)

theorem sGlobal44_hz116 {c : ℝ} (hc : B (113 / 200) (57 / 100) c) : B 0 (1286555084852030559999 / 1000000000000000000) (max |(s3U 12225 46 maskSlack c)| |(s3L 12225 46 maskSlack c)|) := bweaken (bmax (sGlobal44_hz114 hc) (sGlobal44_hz115 hc)) (by norm_num) (by norm_num)

theorem sGlobal44_hz117 {c : ℝ} (hc : B (113 / 200) (57 / 100) c) : B 0 (1286555084852030559999 / 1000000000000000000) (s3nks 12225 46 maskSlack c) := by
    convert (sGlobal44_hz116 hc) using 1 <;>
      norm_num [s3nks] <;> ring

theorem sGlobal44 {c : ℝ} (hc : B (113 / 200) (57 / 100) c) :
    0 < s3am 12225 46 ∧ 0 ≤ s3dm 12225 46 c ∧
    s3dm 12225 46 c ^ 2 ≤ 2 * s3ap 12225 46 ^ 2 ∧ s3c1 12225 46 c < 1 ∧
    0 ≤ s3Cpa 12225 c - s3r1 12225 46 ∧
    s3e0 12225 46 ≤ (s3Cpa 12225 c - s3r1 12225 46) / s3ap 12225 46 ∧
    s3nks 12225 46 maskSlack c ≤ 12225 * (2631 / 25000) := by

  refine ⟨lt_of_lt_of_le (by norm_num) sGlobal44_hz14.1,
    le_trans (by norm_num) (sGlobal44_hz64 hc).1, ?_,
    lt_of_le_of_lt (sGlobal44_hz72 hc).2 (by norm_num), ?_, ?_,
    le_trans (sGlobal44_hz117 hc).2 (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (sGlobal44_hz64 hc).1) (sGlobal44_hz64 hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) sGlobal44_hz9.1 2
    nlinarith only [h1, h2]
  · linarith only [(sGlobal44_hz84 hc).1, sGlobal44_hz33.2]
  · have hap : 0 < s3ap 12225 46 := lt_of_lt_of_le (by norm_num) sGlobal44_hz9.1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul sGlobal44_hz16.2 sGlobal44_hz9.2 (le_trans (by norm_num) sGlobal44_hz9.1) (by norm_num)
    linarith only [h, (sGlobal44_hz84 hc).1, sGlobal44_hz33.2]

end BstLean.Part255
