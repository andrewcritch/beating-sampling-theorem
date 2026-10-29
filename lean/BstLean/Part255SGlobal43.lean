import BstLean.Part255SGlobal39
import BstLean.Part255Numeric10
namespace BstLean.Part255
open Real BstLean.Part130 BstLean.Part182 BstLean.Part197 BstLean.Part246
theorem sGlobal43_hz0 : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal43_hz1 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) ((√(23 : ℝ)) / (12225 : ℝ)) := bdiv sGlobal43_hz0 (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal43_hz2 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) maskSlack := by
    convert sGlobal43_hz1 using 1 <;>
      norm_num [maskSlack] <;> ring

theorem sGlobal43_hz3 : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal43_hz4 : B (6395294793910793 / 500000000000000000) (12790589587821587 / 1000000000000000000) (√((2 / 12225) : ℝ)) := bsqrt (bpoint ((2 / 12225) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal43_hz5 : B (7230130686979 / 62500000000000000) (23136418198333 / 200000000000000000) (√((2 / 149450625) : ℝ)) := bsqrt (bpoint ((2 / 149450625) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal43_hz6 : B (2211334438749598093 / 20000000000000000) (110566721937479904651 / 1000000000000000000) (√(12225 : ℝ)) := bsqrt (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal43_hz7 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))) := bmul sGlobal43_hz3 sGlobal43_hz4 (by norm_num) (by norm_num)

theorem sGlobal43_hz8 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) ((√(12225 : ℝ)) + ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := badd sGlobal43_hz6 sGlobal43_hz7 (by norm_num) (by norm_num)

theorem sGlobal43_hz9 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) (s3ap 12225 46) := by
    convert sGlobal43_hz8 using 1 <;>
      norm_num [s3ap, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal43_hz10 : B (163599182004089 / 1000000000000000000) (16359918200409 / 100000000000000000) ((2 : ℝ) / (12225 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal43_hz11 : B (1222499983640081799591 / 100000000000000000) (12224999836400817995911 / 1000000000000000000) ((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ))) := bsub (bpoint (12225 : ℝ)) sGlobal43_hz10 (by norm_num) (by norm_num)

theorem sGlobal43_hz12 : B (110566721197658827907 / 1000000000000000000) (27641680299414706977 / 250000000000000000) (√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) := bsqrt sGlobal43_hz11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal43_hz13 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) ((√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) - ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bsub sGlobal43_hz12 sGlobal43_hz7 (by norm_num) (by norm_num)

theorem sGlobal43_hz14 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) (s3am 12225 46) := by
    convert sGlobal43_hz13 using 1 <;>
      norm_num [s3am, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal43_hz15 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√((2 / 12225) : ℝ)) * (√(92 : ℝ))) := bmul sGlobal43_hz4 sGlobal43_hz3 (by norm_num) (by norm_num)

theorem sGlobal43_hz16 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) (s3e0 12225 46) := by
    convert sGlobal43_hz15 using 1 <;>
      norm_num [s3e0, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal43_hz17 : B (250196148528560847 / 500000000000000000) (100078459411424339 / 200000000000000000) (((1 / 2) : ℝ) + maskSlack) := badd (bpoint ((1 / 2) : ℝ)) sGlobal43_hz2 (by norm_num) (by norm_num)

theorem sGlobal43_hz18 : B (59827153232297998295487 / 800000000000000) (23930861292919199366019 / 320000000000000) ((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack)) := bmul (bpoint (149450625 : ℝ)) sGlobal43_hz17 (by norm_num) (by norm_num)

theorem sGlobal43_hz19 : B (1729554180017180009583 / 200000000000000000) (8647770900085900056557 / 1000000000000000000) (√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) := bsqrt sGlobal43_hz18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal43_hz20 : B (4328681281566262743499 / 500000000000000000) (8657362563132525495641 / 1000000000000000000) ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))) := badd sGlobal43_hz19 sGlobal43_hz3 (by norm_num) (by norm_num)

theorem sGlobal43_hz21 : B (110732771457999278473 / 1000000000000000000) (55366385728999643621 / 500000000000000000) ((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ)))) := bmul sGlobal43_hz4 sGlobal43_hz20 (by norm_num) (by norm_num)

theorem sGlobal43_hz22 : B (209099159 / 15625000000000000) (13382346177 / 1000000000000000000) ((2 : ℝ) / (149450625 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (149450625 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal43_hz23 : B (2452349334953899930479 / 200000000000000000) (12261746674769501594427 / 1000000000000000000) (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2) := bsq sGlobal43_hz21 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal43_hz24 : B (82045469362091 / 500000000000000000) (32818187747289 / 200000000000000000) (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2)) := bmul sGlobal43_hz22 sGlobal43_hz23 (by norm_num) (by norm_num)

theorem sGlobal43_hz25 : B (82045469362091 / 250000000000000000) (32818187747289 / 100000000000000000) ((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) := bmul (bpoint (2 : ℝ)) sGlobal43_hz24 (by norm_num) (by norm_num)

theorem sGlobal43_hz26 : B (117258080744995992792057 / 1000000000000000000) (58629040372497996396029 / 500000000000000000) (√(13749457500 : ℝ)) := bsqrt (bpoint (13749457500 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal43_hz27 : B (117304080744995992792057 / 1000000000000000000) (58652040372497996396029 / 500000000000000000) ((√(13749457500 : ℝ)) + (46 : ℝ)) := badd sGlobal43_hz26 (bpoint (46 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal43_hz28 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal43_hz25 sGlobal43_hz27 (by norm_num) (by norm_num)

theorem sGlobal43_hz29 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (s3rs 12225 46 maskSlack) := by
    convert sGlobal43_hz28 using 1 <;>
      norm_num [s3rs, s3pp, s3K, mA, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal43_hz30 : B (490797546012267 / 1000000000000000000) (49079754601227 / 100000000000000000) ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (3 : ℝ)) sGlobal43_hz10 (by norm_num) (by norm_num)

theorem sGlobal43_hz31 : B (490797546012267 / 500000000000000000) (49079754601227 / 50000000000000000) ((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal43_hz30 (by norm_num) (by norm_num)

theorem sGlobal43_hz32 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal43_hz31 sGlobal43_hz27 (by norm_num) (by norm_num)

theorem sGlobal43_hz33 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (s3r1 12225 46) := by
    convert sGlobal43_hz32 using 1 <;>
      norm_num [s3r1, mA] <;> ring

theorem sGlobal43_hz34 : B (163599182004089 / 500000000000000000) (16359918200409 / 50000000000000000) ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (2 : ℝ)) sGlobal43_hz10 (by norm_num) (by norm_num)

theorem sGlobal43_hz35 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal43_hz34 (by norm_num) (by norm_num)

theorem sGlobal43_hz36 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal43_hz35 sGlobal43_hz27 (by norm_num) (by norm_num)

theorem sGlobal43_hz37 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (s3rpp 12225 46) := by
    convert sGlobal43_hz36 using 1 <;>
      norm_num [s3rpp, mA] <;> ring

theorem sGlobal43_hz38 {c : ℝ} (hc : B (14 / 25) (113 / 200) c) : B (14 / 25) (113 / 200) c := hc

theorem sGlobal43_hz39 : B (34459943817379969 / 50000000000000000) (689198876347600269 / 1000000000000000000) (kdot ((14 / 25))) := by
    constructor
    · apply bkdot_lower (q := (531085004543794337 / 1000000000000000000)) (a := (488205263396917357 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (16596406391993573 / 31250000000000000)) (a := (244102631698457981 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal43_hz40 : B (196 / 625) (196 / 625) (((14 / 25) : ℝ)^2) := bsq (bpoint ((14 / 25) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal43_hz41 : B (429 / 625) (429 / 625) ((1 : ℝ) - (((14 / 25) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal43_hz40 (by norm_num) (by norm_num)

theorem sGlobal43_hz42 : B (165698521417663833 / 200000000000000000) (414246303544159583 / 500000000000000000) (√((1 : ℝ) - (((14 / 25) : ℝ)^2))) := bsqrt sGlobal43_hz41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal43_hz43 : B (263717387466394877 / 1000000000000000000) (263717387466394879 / 1000000000000000000) ((√((1 : ℝ) - (((14 / 25) : ℝ)^2))) / Real.pi) := bdiv sGlobal43_hz42 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal43_hz44 : B (96487842688663913 / 250000000000000000) (385951370754656151 / 1000000000000000000) (((14 / 25) : ℝ) * (kdot ((14 / 25)))) := bmul (bpoint ((14 / 25) : ℝ)) sGlobal43_hz39 (by norm_num) (by norm_num)

theorem sGlobal43_hz45 : B (649668758221050529 / 1000000000000000000) (64966875822105103 / 100000000000000000) (((√((1 : ℝ) - (((14 / 25) : ℝ)^2))) / Real.pi) + (((14 / 25) : ℝ) * (kdot ((14 / 25))))) := badd sGlobal43_hz43 sGlobal43_hz44 (by norm_num) (by norm_num)

theorem sGlobal43_hz46 : B (649668758221050529 / 1000000000000000000) (64966875822105103 / 100000000000000000) (kappa ((14 / 25))) := by rw [kappa_eq]; exact sGlobal43_hz45

theorem sGlobal43_hz47 : B (345561920304089723 / 500000000000000000) (172780960152045017 / 250000000000000000) (kdot ((113 / 200))) := by
    constructor
    · apply bkdot_lower (q := (527214635196610611 / 1000000000000000000)) (a := (97036307321437347 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (52721463519661061 / 100000000000000000)) (a := (3032384603794911 / 6250000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal43_hz48 : B (12769 / 40000) (12769 / 40000) (((113 / 200) : ℝ)^2) := bsq (bpoint ((113 / 200) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal43_hz49 : B (27231 / 40000) (27231 / 40000) ((1 : ℝ) - (((113 / 200) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal43_hz48 (by norm_num) (by norm_num)

theorem sGlobal43_hz50 : B (165018180816539121 / 200000000000000000) (412545452041347803 / 500000000000000000) (√((1 : ℝ) - (((113 / 200) : ℝ)^2))) := bsqrt sGlobal43_hz49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal43_hz51 : B (262634591769843783 / 1000000000000000000) (52526918353968757 / 200000000000000000) ((√((1 : ℝ) - (((113 / 200) : ℝ)^2))) / Real.pi) := bdiv sGlobal43_hz50 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal43_hz52 : B (195242484971810693 / 500000000000000000) (390484969943621739 / 1000000000000000000) (((113 / 200) : ℝ) * (kdot ((113 / 200)))) := bmul (bpoint ((113 / 200) : ℝ)) sGlobal43_hz47 (by norm_num) (by norm_num)

theorem sGlobal43_hz53 : B (653119561713465169 / 1000000000000000000) (163279890428366381 / 250000000000000000) (((√((1 : ℝ) - (((113 / 200) : ℝ)^2))) / Real.pi) + (((113 / 200) : ℝ) * (kdot ((113 / 200))))) := badd sGlobal43_hz51 sGlobal43_hz52 (by norm_num) (by norm_num)

theorem sGlobal43_hz54 : B (653119561713465169 / 1000000000000000000) (163279890428366381 / 250000000000000000) (kappa ((113 / 200))) := by rw [kappa_eq]; exact sGlobal43_hz53

theorem sGlobal43_hz55 {c : ℝ} (hc : B (14 / 25) (113 / 200) c) : B (649668758221050529 / 1000000000000000000) (163279890428366381 / 250000000000000000) (kappa c) := bkappa (sGlobal43_hz38 hc) (by norm_num) (by norm_num) sGlobal43_hz46.1 sGlobal43_hz54.2

theorem sGlobal43_hz56 : B 24450 24450 ((2 : ℝ) * (12225 : ℝ)) := bmul (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal43_hz57 {c : ℝ} (hc : B (14 / 25) (113 / 200) c) : B (86720109571633619 / 250000000000000000) (350331241778949471 / 1000000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (sGlobal43_hz55 hc) (by norm_num) (by norm_num)

theorem sGlobal43_hz58 {c : ℝ} (hc : B (14 / 25) (113 / 200) c) : B (42406133580528839691 / 5000000000000000) (171311977229906291319 / 20000000000000000) (((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) := bmul sGlobal43_hz56 (sGlobal43_hz57 hc) (by norm_num) (by norm_num)

theorem sGlobal43_hz59 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (4 : ℝ)) sGlobal43_hz10 (by norm_num) (by norm_num)

theorem sGlobal43_hz60 {c : ℝ} (hc : B (14 / 25) (113 / 200) c) : B (106015325771362999023 / 12500000000000000) (4282799103549293274797 / 500000000000000000) ((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bsub (sGlobal43_hz58 hc) sGlobal43_hz59 (by norm_num) (by norm_num)

theorem sGlobal43_hz61 {c : ℝ} (hc : B (14 / 25) (113 / 200) c) : B (3683742892593681527 / 40000000000000000) (23137629263683469681 / 250000000000000000) (√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) := bsqrt (sGlobal43_hz60 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal43_hz62 : B (30670756373515103 / 125000000000000000) (122683025494060423 / 500000000000000000) ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal43_hz7 (by norm_num) (by norm_num)

theorem sGlobal43_hz63 {c : ℝ} (hc : B (14 / 25) (113 / 200) c) : B (91848206263853917329 / 1000000000000000000) (923051510037457579 / 10000000000000000) ((√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) - ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))))) := bsub (sGlobal43_hz61 hc) sGlobal43_hz62 (by norm_num) (by norm_num)

theorem sGlobal43_hz64 {c : ℝ} (hc : B (14 / 25) (113 / 200) c) : B (91848206263853917329 / 1000000000000000000) (923051510037457579 / 10000000000000000) (s3dm 12225 46 c) := by
    convert (sGlobal43_hz63 hc) using 1 <;>
      norm_num [s3dm, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal43_hz65 : B (6126072185528622723889 / 500000000000000000) (2450428874211449090087 / 200000000000000000) ((s3ap 12225 46)^2) := bsq sGlobal43_hz9 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal43_hz66 : B (6126072185528622723889 / 250000000000000000) (2450428874211449090087 / 100000000000000000) ((2 : ℝ) * ((s3ap 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal43_hz65 (by norm_num) (by norm_num)

theorem sGlobal43_hz67 {c : ℝ} (hc : B (14 / 25) (113 / 200) c) : B (84360929938874539751 / 10000000000000000) (66564382045502394509 / 7812500000000000) ((s3dm 12225 46 c)^2) := bsq (sGlobal43_hz64 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal43_hz68 {c : ℝ} (hc : B (14 / 25) (113 / 200) c) : B (3996011960072546099601 / 250000000000000000) (1606819574822703692577 / 100000000000000000) (((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) := bsub sGlobal43_hz66 (sGlobal43_hz67 hc) (by norm_num) (by norm_num)

theorem sGlobal43_hz69 : B (1524735695971823534271 / 125000000000000000) (609894278388729413841 / 50000000000000000) ((s3am 12225 46)^2) := bsq sGlobal43_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal43_hz70 : B (1524735695971823534271 / 62500000000000000) (609894278388729413841 / 25000000000000000) ((2 : ℝ) * ((s3am 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal43_hz69 (by norm_num) (by norm_num)

theorem sGlobal43_hz71 {c : ℝ} (hc : B (14 / 25) (113 / 200) c) : B (327598741426919959 / 500000000000000000) (658646765414711027 / 1000000000000000000) ((((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) / ((2 : ℝ) * ((s3am 12225 46)^2))) := bdiv (sGlobal43_hz68 hc) sGlobal43_hz70 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal43_hz72 {c : ℝ} (hc : B (14 / 25) (113 / 200) c) : B (327598741426919959 / 500000000000000000) (658646765414711027 / 1000000000000000000) (s3c1 12225 46 c) := by
    convert (sGlobal43_hz71 hc) using 1 <;>
      norm_num [s3c1] <;> ring

theorem sGlobal43_hz73 {c : ℝ} (hc : B (14 / 25) (113 / 200) c) : B (34459943817379969 / 50000000000000000) (172780960152045017 / 250000000000000000) (kdot c) := bkdot (sGlobal43_hz38 hc) sGlobal43_hz39.1 sGlobal43_hz47.2

theorem sGlobal43_hz74 : B (727414588035923031 / 1000000000000000000) (363707294017961517 / 500000000000000000) (kdot ((327598741426919959 / 500000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (456415416397964451 / 1000000000000000000)) (a := (53522020481380721 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (9128308327959289 / 20000000000000000)) (a := (85635232770209153 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal43_hz75 : B (182217706824973411 / 250000000000000000) (728870827299893647 / 1000000000000000000) (kdot ((658646765414711027 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (226827163816264541 / 500000000000000000)) (a := (212944354282133113 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (453654327632529081 / 1000000000000000000)) (a := (425888708564266223 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal43_hz76 {c : ℝ} (hc : B (14 / 25) (113 / 200) c) : B (727414588035923031 / 1000000000000000000) (728870827299893647 / 1000000000000000000) (kdot (s3c1 12225 46 c)) := bkdot (sGlobal43_hz72 hc) sGlobal43_hz74.1 sGlobal43_hz75.2

theorem sGlobal43_hz77 {c : ℝ} (hc : B (14 / 25) (113 / 200) c) : B (196 / 625) (12769 / 40000) (c^2) := bsq (sGlobal43_hz38 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal43_hz78 {c : ℝ} (hc : B (14 / 25) (113 / 200) c) : B (27231 / 40000) (429 / 625) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (sGlobal43_hz77 hc) (by norm_num) (by norm_num)

theorem sGlobal43_hz79 {c : ℝ} (hc : B (14 / 25) (113 / 200) c) : B (165018180816539121 / 200000000000000000) (414246303544159583 / 500000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (sGlobal43_hz78 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal43_hz80 : B (39119999999999765769 / 1600000000000000) (3912000000000000489 / 160000000000000) ((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (149450625 : ℝ)) sGlobal43_hz10 (by norm_num) (by norm_num)

theorem sGlobal43_hz81 {c : ℝ} (hc : B (14 / 25) (113 / 200) c) : B (142162930994604677 / 250000000000000000) (143147748131590763 / 250000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (sGlobal43_hz79 hc) (sGlobal43_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal43_hz82 {c : ℝ} (hc : B (14 / 25) (113 / 200) c) : B (6951767325636127081593 / 500000000000000000) (6999924883634789185691 / 500000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) := bmul sGlobal43_hz80 (sGlobal43_hz81 hc) (by norm_num) (by norm_num)

theorem sGlobal43_hz83 {c : ℝ} (hc : B (14 / 25) (113 / 200) c) : B (6951767325636127081593 / 1000000000000000000) (6999924883634789185691 / 1000000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) / (2 : ℝ)) := bdiv (sGlobal43_hz82 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal43_hz84 {c : ℝ} (hc : B (14 / 25) (113 / 200) c) : B (6951767325636127081593 / 1000000000000000000) (6999924883634789185691 / 1000000000000000000) (s3Cpa 12225 c) := by
    convert (sGlobal43_hz83 hc) using 1 <;>
      norm_num [s3Cpa, mA] <;> ring

theorem sGlobal43_hz85 {c : ℝ} (hc : B (14 / 25) (113 / 200) c) : B (262634591769843783 / 1000000000000000000) (263717387466394879 / 1000000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (sGlobal43_hz79 hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal43_hz86 {c : ℝ} (hc : B (14 / 25) (113 / 200) c) : B (96487842688663913 / 250000000000000000) (390484969943621739 / 1000000000000000000) (c * (kdot c)) := bmul (sGlobal43_hz38 hc) (sGlobal43_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal43_hz87 {c : ℝ} (hc : B (14 / 25) (113 / 200) c) : B (-31962594543444489 / 250000000000000000) (-122233983288260773 / 1000000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (sGlobal43_hz85 hc) (sGlobal43_hz86 hc) (by norm_num) (by norm_num)

theorem sGlobal43_hz88 {c : ℝ} (hc : B (14 / 25) (113 / 200) c) : B (-3125941746348871414943 / 1000000000000000000) (-1494310445698979002741 / 500000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) := bmul sGlobal43_hz80 (sGlobal43_hz87 hc) (by norm_num) (by norm_num)

theorem sGlobal43_hz89 {c : ℝ} (hc : B (14 / 25) (113 / 200) c) : B (-97685679573402231717 / 62500000000000000) (-1494310445698979002741 / 1000000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) / (2 : ℝ)) := bdiv (sGlobal43_hz88 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal43_hz90 {c : ℝ} (hc : B (14 / 25) (113 / 200) c) : B (-97685679573402231717 / 62500000000000000) (-1494310445698979002741 / 1000000000000000000) (s3Cpp 12225 c) := by
    convert (sGlobal43_hz89 hc) using 1 <;>
      norm_num [s3Cpp, mA] <;> ring

theorem sGlobal43_hz91 {c : ℝ} (hc : B (14 / 25) (113 / 200) c) : B (3533456217784932394997 / 500000000000000000) (7115069993568527597917 / 1000000000000000000) ((s3Cpa 12225 c) + (s3r1 12225 46)) := badd (sGlobal43_hz84 hc) sGlobal43_hz33 (by norm_num) (by norm_num)

theorem sGlobal43_hz92 {c : ℝ} (hc : B (14 / 25) (113 / 200) c) : B (63986364067507811489 / 1000000000000000000) (64422399898827133599 / 1000000000000000000) (((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) := bdiv (sGlobal43_hz91 hc) sGlobal43_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal43_hz93 {c : ℝ} (hc : B (14 / 25) (113 / 200) c) : B (64109047093001871901 / 1000000000000000000) (32272541462160597011 / 500000000000000000) ((((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) + (s3e0 12225 46)) := badd (sGlobal43_hz92 hc) sGlobal43_hz16 (by norm_num) (by norm_num)

theorem sGlobal43_hz94 {c : ℝ} (hc : B (14 / 25) (113 / 200) c) : B (64109047093001871901 / 1000000000000000000) (32272541462160597011 / 500000000000000000) (s3Lam 12225 46 c) := by
    convert (sGlobal43_hz93 hc) using 1 <;>
      norm_num [s3Lam] <;> ring

theorem sGlobal43_hz95 {c : ℝ} (hc : B (14 / 25) (113 / 200) c) : B (-92887966659496493867 / 62500000000000000) (-1417547039076486727923 / 1000000000000000000) ((s3Cpp 12225 c) + (s3rpp 12225 46)) := badd (sGlobal43_hz90 hc) sGlobal43_hz37 (by norm_num) (by norm_num)

theorem sGlobal43_hz96 {c : ℝ} (hc : B (14 / 25) (113 / 200) c) : B (-541626632842497183779 / 500000000000000000) (-708773519538243363961 / 1000000000000000000) (if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) := bweaken (bfirst (sGlobal43_hz95 hc) (sGlobal43_hz76 hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem sGlobal43_hz97 {c : ℝ} (hc : B (14 / 25) (113 / 200) c) : B (4109969919172731762227 / 1000000000000000000) (2083033864853749689673 / 500000000000000000) ((s3Lam 12225 46 c)^2) := bsq (sGlobal43_hz94 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal43_hz98 {c : ℝ} (hc : B (14 / 25) (113 / 200) c) : B (429283741538007853 / 1000000000000000000) (216907780795630689 / 500000000000000000) ((s3c1 12225 46 c)^2) := bsq (sGlobal43_hz72 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal43_hz99 {c : ℝ} (hc : B (14 / 25) (113 / 200) c) : B (283092219204369311 / 500000000000000000) (570716258461992147 / 1000000000000000000) ((1 : ℝ) - ((s3c1 12225 46 c)^2)) := bsub (bpoint (1 : ℝ)) (sGlobal43_hz98 hc) (by norm_num) (by norm_num)

theorem sGlobal43_hz100 {c : ℝ} (hc : B (14 / 25) (113 / 200) c) : B (376226141572039961 / 500000000000000000) (755457648357597971 / 1000000000000000000) (√((1 : ℝ) - ((s3c1 12225 46 c)^2))) := bsqrt (sGlobal43_hz99 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal43_hz101 {c : ℝ} (hc : B (14 / 25) (113 / 200) c) : B (590974641225577123 / 250000000000000000) (593335049544612779 / 250000000000000000) (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))) := bmul pi_mem (sGlobal43_hz100 hc) (by norm_num) (by norm_num)

theorem sGlobal43_hz102 {c : ℝ} (hc : B (14 / 25) (113 / 200) c) : B (865861944766104640329 / 500000000000000000) (1762371614231961818547 / 1000000000000000000) (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2))))) := bdiv (sGlobal43_hz97 hc) (sGlobal43_hz101 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal43_hz103 {c : ℝ} (hc : B (14 / 25) (113 / 200) c) : B (6484706238472149131 / 10000000000000000) (526799047346859227293 / 500000000000000000) ((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) := badd (sGlobal43_hz96 hc) (sGlobal43_hz102 hc) (by norm_num) (by norm_num)

theorem sGlobal43_hz104 : B (3762781186094069 / 250000000000000000) (376278118609407 / 25000000000000000) ((s3e0 12225 46)^2) := bsq sGlobal43_hz16 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal43_hz105 {c : ℝ} (hc : B (14 / 25) (113 / 200) c) : B (20265177342873727793 / 31250000000000000) (526806572909231415433 / 500000000000000000) (((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) := badd (sGlobal43_hz103 hc) sGlobal43_hz104 (by norm_num) (by norm_num)

theorem sGlobal43_hz106 {c : ℝ} (hc : B (14 / 25) (113 / 200) c) : B (686982748423206559507 / 1000000000000000000) (546055109636293550441 / 500000000000000000) ((((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) + (s3rs 12225 46 maskSlack)) := badd (sGlobal43_hz105 hc) sGlobal43_hz29 (by norm_num) (by norm_num)

theorem sGlobal43_hz107 {c : ℝ} (hc : B (14 / 25) (113 / 200) c) : B (686982748423206559507 / 1000000000000000000) (546055109636293550441 / 500000000000000000) (s3U 12225 46 maskSlack c) := by
    convert (sGlobal43_hz106 hc) using 1 <;>
      norm_num [s3U] <;> ring

theorem sGlobal43_hz108 {c : ℝ} (hc : B (14 / 25) (113 / 200) c) : B (-163973427979692798229 / 100000000000000000) (-1571073852321470808341 / 1000000000000000000) ((s3Cpp 12225 c) - (s3rpp 12225 46)) := bsub (sGlobal43_hz90 hc) sGlobal43_hz37 (by norm_num) (by norm_num)

theorem sGlobal43_hz109 {c : ℝ} (hc : B (14 / 25) (113 / 200) c) : B (-163973427979692798229 / 100000000000000000) (-1571073852321470808341 / 1000000000000000000) (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ)) := bweaken (bmin (sGlobal43_hz108 hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem sGlobal43_hz110 {c : ℝ} (hc : B (14 / 25) (113 / 200) c) : B (-1195154481067582183791 / 1000000000000000000) (-1142822039060433266303 / 1000000000000000000) ((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) := bmul (sGlobal43_hz76 hc) (sGlobal43_hz109 hc) (by norm_num) (by norm_num)

theorem sGlobal43_hz111 {c : ℝ} (hc : B (14 / 25) (113 / 200) c) : B (-1195169532192326560071 / 1000000000000000000) (-1142837090185177642579 / 1000000000000000000) (((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) := bsub (sGlobal43_hz110 hc) sGlobal43_hz104 (by norm_num) (by norm_num)

theorem sGlobal43_hz112 {c : ℝ} (hc : B (14 / 25) (113 / 200) c) : B (-1233666605646450830087 / 1000000000000000000) (-118133416363642491271 / 100000000000000000) ((((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) - (s3rs 12225 46 maskSlack)) := bsub (sGlobal43_hz111 hc) sGlobal43_hz29 (by norm_num) (by norm_num)

theorem sGlobal43_hz113 {c : ℝ} (hc : B (14 / 25) (113 / 200) c) : B (-1233666605646450830087 / 1000000000000000000) (-118133416363642491271 / 100000000000000000) (s3L 12225 46 maskSlack c) := by
    convert (sGlobal43_hz112 hc) using 1 <;>
      norm_num [s3L] <;> ring

theorem sGlobal43_hz114 {c : ℝ} (hc : B (14 / 25) (113 / 200) c) : B 0 (546055109636293550441 / 500000000000000000) |(s3U 12225 46 maskSlack c)| := bweaken (babs (sGlobal43_hz107 hc)) (by norm_num) (by norm_num)

theorem sGlobal43_hz115 {c : ℝ} (hc : B (14 / 25) (113 / 200) c) : B 0 (1233666605646450830087 / 1000000000000000000) |(s3L 12225 46 maskSlack c)| := bweaken (babs (sGlobal43_hz113 hc)) (by norm_num) (by norm_num)

theorem sGlobal43_hz116 {c : ℝ} (hc : B (14 / 25) (113 / 200) c) : B 0 (1233666605646450830087 / 1000000000000000000) (max |(s3U 12225 46 maskSlack c)| |(s3L 12225 46 maskSlack c)|) := bweaken (bmax (sGlobal43_hz114 hc) (sGlobal43_hz115 hc)) (by norm_num) (by norm_num)

theorem sGlobal43_hz117 {c : ℝ} (hc : B (14 / 25) (113 / 200) c) : B 0 (1233666605646450830087 / 1000000000000000000) (s3nks 12225 46 maskSlack c) := by
    convert (sGlobal43_hz116 hc) using 1 <;>
      norm_num [s3nks] <;> ring

theorem sGlobal43 {c : ℝ} (hc : B (14 / 25) (113 / 200) c) :
    0 < s3am 12225 46 ∧ 0 ≤ s3dm 12225 46 c ∧
    s3dm 12225 46 c ^ 2 ≤ 2 * s3ap 12225 46 ^ 2 ∧ s3c1 12225 46 c < 1 ∧
    0 ≤ s3Cpa 12225 c - s3r1 12225 46 ∧
    s3e0 12225 46 ≤ (s3Cpa 12225 c - s3r1 12225 46) / s3ap 12225 46 ∧
    s3nks 12225 46 maskSlack c ≤ 12225 * (50457 / 500000) := by

  refine ⟨lt_of_lt_of_le (by norm_num) sGlobal43_hz14.1,
    le_trans (by norm_num) (sGlobal43_hz64 hc).1, ?_,
    lt_of_le_of_lt (sGlobal43_hz72 hc).2 (by norm_num), ?_, ?_,
    le_trans (sGlobal43_hz117 hc).2 (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (sGlobal43_hz64 hc).1) (sGlobal43_hz64 hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) sGlobal43_hz9.1 2
    nlinarith only [h1, h2]
  · linarith only [(sGlobal43_hz84 hc).1, sGlobal43_hz33.2]
  · have hap : 0 < s3ap 12225 46 := lt_of_lt_of_le (by norm_num) sGlobal43_hz9.1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul sGlobal43_hz16.2 sGlobal43_hz9.2 (le_trans (by norm_num) sGlobal43_hz9.1) (by norm_num)
    linarith only [h, (sGlobal43_hz84 hc).1, sGlobal43_hz33.2]

end BstLean.Part255
