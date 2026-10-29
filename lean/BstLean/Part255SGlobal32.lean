import BstLean.Part255SGlobal28
import BstLean.Part255Numeric10
namespace BstLean.Part255
open Real BstLean.Part130 BstLean.Part182 BstLean.Part197 BstLean.Part246
theorem sGlobal32_hz0 : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal32_hz1 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) ((√(23 : ℝ)) / (12225 : ℝ)) := bdiv sGlobal32_hz0 (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal32_hz2 : B (196148528560847 / 500000000000000000) (78459411424339 / 200000000000000000) maskSlack := by
    convert sGlobal32_hz1 using 1 <;>
      norm_num [maskSlack] <;> ring

theorem sGlobal32_hz3 : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal32_hz4 : B (6395294793910793 / 500000000000000000) (12790589587821587 / 1000000000000000000) (√((2 / 12225) : ℝ)) := bsqrt (bpoint ((2 / 12225) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal32_hz5 : B (7230130686979 / 62500000000000000) (23136418198333 / 200000000000000000) (√((2 / 149450625) : ℝ)) := bsqrt (bpoint ((2 / 149450625) : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal32_hz6 : B (2211334438749598093 / 20000000000000000) (110566721937479904651 / 1000000000000000000) (√(12225 : ℝ)) := bsqrt (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal32_hz7 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))) := bmul sGlobal32_hz3 sGlobal32_hz4 (by norm_num) (by norm_num)

theorem sGlobal32_hz8 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) ((√(12225 : ℝ)) + ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := badd sGlobal32_hz6 sGlobal32_hz7 (by norm_num) (by norm_num)

theorem sGlobal32_hz9 : B (55344702481486982531 / 500000000000000000) (55344702481486982537 / 500000000000000000) (s3ap 12225 46) := by
    convert sGlobal32_hz8 using 1 <;>
      norm_num [s3ap, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal32_hz10 : B (163599182004089 / 1000000000000000000) (16359918200409 / 100000000000000000) ((2 : ℝ) / (12225 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal32_hz11 : B (1222499983640081799591 / 100000000000000000) (12224999836400817995911 / 1000000000000000000) ((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ))) := bsub (bpoint (12225 : ℝ)) sGlobal32_hz10 (by norm_num) (by norm_num)

theorem sGlobal32_hz12 : B (110566721197658827907 / 1000000000000000000) (27641680299414706977 / 250000000000000000) (√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) := bsqrt sGlobal32_hz11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal32_hz13 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) ((√((12225 : ℝ) - ((2 : ℝ) / (12225 : ℝ)))) - ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bsub sGlobal32_hz12 sGlobal32_hz7 (by norm_num) (by norm_num)

theorem sGlobal32_hz14 : B (27611009543041191871 / 250000000000000000) (13805504771520595937 / 125000000000000000) (s3am 12225 46) := by
    convert sGlobal32_hz13 using 1 <;>
      norm_num [s3am, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal32_hz15 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) ((√((2 / 12225) : ℝ)) * (√(92 : ℝ))) := bmul sGlobal32_hz4 sGlobal32_hz3 (by norm_num) (by norm_num)

theorem sGlobal32_hz16 : B (30670756373515103 / 250000000000000000) (122683025494060423 / 1000000000000000000) (s3e0 12225 46) := by
    convert sGlobal32_hz15 using 1 <;>
      norm_num [s3e0, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal32_hz17 : B (250196148528560847 / 500000000000000000) (100078459411424339 / 200000000000000000) (((1 / 2) : ℝ) + maskSlack) := badd (bpoint ((1 / 2) : ℝ)) sGlobal32_hz2 (by norm_num) (by norm_num)

theorem sGlobal32_hz18 : B (59827153232297998295487 / 800000000000000) (23930861292919199366019 / 320000000000000) ((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack)) := bmul (bpoint (149450625 : ℝ)) sGlobal32_hz17 (by norm_num) (by norm_num)

theorem sGlobal32_hz19 : B (1729554180017180009583 / 200000000000000000) (8647770900085900056557 / 1000000000000000000) (√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) := bsqrt sGlobal32_hz18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal32_hz20 : B (4328681281566262743499 / 500000000000000000) (8657362563132525495641 / 1000000000000000000) ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))) := badd sGlobal32_hz19 sGlobal32_hz3 (by norm_num) (by norm_num)

theorem sGlobal32_hz21 : B (110732771457999278473 / 1000000000000000000) (55366385728999643621 / 500000000000000000) ((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ)))) := bmul sGlobal32_hz4 sGlobal32_hz20 (by norm_num) (by norm_num)

theorem sGlobal32_hz22 : B (209099159 / 15625000000000000) (13382346177 / 1000000000000000000) ((2 : ℝ) / (149450625 : ℝ)) := bdiv (bpoint (2 : ℝ)) (bpoint (149450625 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal32_hz23 : B (2452349334953899930479 / 200000000000000000) (12261746674769501594427 / 1000000000000000000) (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2) := bsq sGlobal32_hz21 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal32_hz24 : B (82045469362091 / 500000000000000000) (32818187747289 / 200000000000000000) (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2)) := bmul sGlobal32_hz22 sGlobal32_hz23 (by norm_num) (by norm_num)

theorem sGlobal32_hz25 : B (82045469362091 / 250000000000000000) (32818187747289 / 100000000000000000) ((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) := bmul (bpoint (2 : ℝ)) sGlobal32_hz24 (by norm_num) (by norm_num)

theorem sGlobal32_hz26 : B (117258080744995992792057 / 1000000000000000000) (58629040372497996396029 / 500000000000000000) (√(13749457500 : ℝ)) := bsqrt (bpoint (13749457500 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal32_hz27 : B (117304080744995992792057 / 1000000000000000000) (58652040372497996396029 / 500000000000000000) ((√(13749457500 : ℝ)) + (46 : ℝ)) := badd sGlobal32_hz26 (bpoint (46 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal32_hz28 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (((2 : ℝ) * (((2 : ℝ) / (149450625 : ℝ)) * (((√((2 / 12225) : ℝ)) * ((√((149450625 : ℝ) * (((1 / 2) : ℝ) + maskSlack))) + (√(92 : ℝ))))^2))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal32_hz25 sGlobal32_hz27 (by norm_num) (by norm_num)

theorem sGlobal32_hz29 : B (38497073451247270131 / 1000000000000000000) (601516772720691719 / 15625000000000000) (s3rs 12225 46 maskSlack) := by
    convert sGlobal32_hz28 using 1 <;>
      norm_num [s3rs, s3pp, s3K, mA, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal32_hz30 : B (490797546012267 / 1000000000000000000) (49079754601227 / 100000000000000000) ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (3 : ℝ)) sGlobal32_hz10 (by norm_num) (by norm_num)

theorem sGlobal32_hz31 : B (490797546012267 / 500000000000000000) (49079754601227 / 50000000000000000) ((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal32_hz30 (by norm_num) (by norm_num)

theorem sGlobal32_hz32 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (((2 : ℝ) * ((3 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal32_hz31 sGlobal32_hz27 (by norm_num) (by norm_num)

theorem sGlobal32_hz33 : B (115145109933737708401 / 1000000000000000000) (57572554966869206113 / 500000000000000000) (s3r1 12225 46) := by
    convert sGlobal32_hz32 using 1 <;>
      norm_num [s3r1, mA] <;> ring

theorem sGlobal32_hz34 : B (163599182004089 / 500000000000000000) (16359918200409 / 50000000000000000) ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (2 : ℝ)) sGlobal32_hz10 (by norm_num) (by norm_num)

theorem sGlobal32_hz35 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal32_hz34 (by norm_num) (by norm_num)

theorem sGlobal32_hz36 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (((2 : ℝ) * ((2 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) * ((√(13749457500 : ℝ)) + (46 : ℝ))) := bmul sGlobal32_hz35 sGlobal32_hz27 (by norm_num) (by norm_num)

theorem sGlobal32_hz37 : B (95954258278114757 / 1250000000000000) (38381703311246137409 / 500000000000000000) (s3rpp 12225 46) := by
    convert sGlobal32_hz36 using 1 <;>
      norm_num [s3rpp, mA] <;> ring

theorem sGlobal32_hz38 {c : ℝ} (hc : B (101 / 200) (51 / 100) c) : B (101 / 200) (51 / 100) c := hc

theorem sGlobal32_hz39 : B (83563439141160113 / 125000000000000000) (33425375656465959 / 50000000000000000) (kdot ((101 / 200))) := by
    constructor
    · apply bkdot_lower (q := (573501224484350891 / 1000000000000000000)) (a := (520707180736631049 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (57350122448435089 / 100000000000000000)) (a := (520707180736570927 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal32_hz40 : B (10201 / 40000) (10201 / 40000) (((101 / 200) : ℝ)^2) := bsq (bpoint ((101 / 200) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal32_hz41 : B (29799 / 40000) (29799 / 40000) ((1 : ℝ) - (((101 / 200) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal32_hz40 (by norm_num) (by norm_num)

theorem sGlobal32_hz42 : B (86311934284894809 / 100000000000000000) (863119342848948091 / 1000000000000000000) (√((1 : ℝ) - (((101 / 200) : ℝ)^2))) := bsqrt sGlobal32_hz41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal32_hz43 : B (54947883957055373 / 200000000000000000) (137369709892638433 / 500000000000000000) ((√((1 : ℝ) - (((101 / 200) : ℝ)^2))) / Real.pi) := bdiv sGlobal32_hz42 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal32_hz44 : B (42199536766285857 / 125000000000000000) (168798147065153093 / 500000000000000000) (((101 / 200) : ℝ) * (kdot ((101 / 200)))) := bmul (bpoint ((101 / 200) : ℝ)) sGlobal32_hz39 (by norm_num) (by norm_num)

theorem sGlobal32_hz45 : B (612335713915563721 / 1000000000000000000) (153083928478895763 / 250000000000000000) (((√((1 : ℝ) - (((101 / 200) : ℝ)^2))) / Real.pi) + (((101 / 200) : ℝ) * (kdot ((101 / 200))))) := badd sGlobal32_hz43 sGlobal32_hz44 (by norm_num) (by norm_num)

theorem sGlobal32_hz46 : B (612335713915563721 / 1000000000000000000) (153083928478895763 / 250000000000000000) (kappa ((101 / 200))) := by rw [kappa_eq]; exact sGlobal32_hz45

theorem sGlobal32_hz47 : B (335177304839959399 / 500000000000000000) (167588652419986579 / 250000000000000000) (kdot ((51 / 100))) := by
    constructor
    · apply bkdot_lower (q := (569651921139811611 / 1000000000000000000)) (a := (258902884129826761 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (56965192113981161 / 100000000000000000)) (a := (258902884129805149 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal32_hz48 : B (2601 / 10000) (2601 / 10000) (((51 / 100) : ℝ)^2) := bsq (bpoint ((51 / 100) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal32_hz49 : B (7399 / 10000) (7399 / 10000) ((1 : ℝ) - (((51 / 100) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) sGlobal32_hz48 (by norm_num) (by norm_num)

theorem sGlobal32_hz50 : B (860174400921115531 / 1000000000000000000) (215043600230278883 / 250000000000000000) (√((1 : ℝ) - (((51 / 100) : ℝ)^2))) := bsqrt sGlobal32_hz49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal32_hz51 : B (27380201565541061 / 100000000000000000) (273802015655410611 / 1000000000000000000) ((√((1 : ℝ) - (((51 / 100) : ℝ)^2))) / Real.pi) := bdiv sGlobal32_hz50 pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal32_hz52 : B (170940425468379293 / 500000000000000000) (170940425468386311 / 500000000000000000) (((51 / 100) : ℝ) * (kdot ((51 / 100)))) := bmul (bpoint ((51 / 100) : ℝ)) sGlobal32_hz47 (by norm_num) (by norm_num)

theorem sGlobal32_hz53 : B (153920716648042299 / 250000000000000000) (615682866592183233 / 1000000000000000000) (((√((1 : ℝ) - (((51 / 100) : ℝ)^2))) / Real.pi) + (((51 / 100) : ℝ) * (kdot ((51 / 100))))) := badd sGlobal32_hz51 sGlobal32_hz52 (by norm_num) (by norm_num)

theorem sGlobal32_hz54 : B (153920716648042299 / 250000000000000000) (615682866592183233 / 1000000000000000000) (kappa ((51 / 100))) := by rw [kappa_eq]; exact sGlobal32_hz53

theorem sGlobal32_hz55 {c : ℝ} (hc : B (101 / 200) (51 / 100) c) : B (612335713915563721 / 1000000000000000000) (615682866592183233 / 1000000000000000000) (kappa c) := bkappa (sGlobal32_hz38 hc) (by norm_num) (by norm_num) sGlobal32_hz46.1 sGlobal32_hz54.2

theorem sGlobal32_hz56 : B 24450 24450 ((2 : ℝ) * (12225 : ℝ)) := bmul (bpoint (2 : ℝ)) (bpoint (12225 : ℝ)) (by norm_num) (by norm_num)

theorem sGlobal32_hz57 {c : ℝ} (hc : B (101 / 200) (51 / 100) c) : B (384317133407816767 / 1000000000000000000) (387664286084436279 / 1000000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (sGlobal32_hz55 hc) (by norm_num) (by norm_num)

theorem sGlobal32_hz58 {c : ℝ} (hc : B (101 / 200) (51 / 100) c) : B (187931078236422399063 / 20000000000000000) (189567835895289340431 / 20000000000000000) (((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) := bmul sGlobal32_hz56 (sGlobal32_hz57 hc) (by norm_num) (by norm_num)

theorem sGlobal32_hz59 : B (163599182004089 / 250000000000000000) (16359918200409 / 25000000000000000) ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (4 : ℝ)) sGlobal32_hz10 (by norm_num) (by norm_num)

theorem sGlobal32_hz60 {c : ℝ} (hc : B (101 / 200) (51 / 100) c) : B (939655325742439193679 / 100000000000000000) (4739195570183869502597 / 500000000000000000) ((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ)))) := bsub (sGlobal32_hz58 hc) sGlobal32_hz59 (by norm_num) (by norm_num)

theorem sGlobal32_hz61 {c : ℝ} (hc : B (101 / 200) (51 / 100) c) : B (6058488768811413007 / 62500000000000000) (9735702922936658201 / 100000000000000000) (√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) := bsqrt (sGlobal32_hz60 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal32_hz62 : B (30670756373515103 / 125000000000000000) (122683025494060423 / 500000000000000000) ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ)))) := bmul (bpoint (2 : ℝ)) sGlobal32_hz7 (by norm_num) (by norm_num)

theorem sGlobal32_hz63 {c : ℝ} (hc : B (101 / 200) (51 / 100) c) : B (48345227124997243633 / 500000000000000000) (48555831589189230593 / 500000000000000000) ((√((((2 : ℝ) * (12225 : ℝ)) * ((1 : ℝ) - (kappa c))) - ((4 : ℝ) * ((2 : ℝ) / (12225 : ℝ))))) - ((2 : ℝ) * ((√(92 : ℝ)) * (√((2 / 12225) : ℝ))))) := bsub (sGlobal32_hz61 hc) sGlobal32_hz62 (by norm_num) (by norm_num)

theorem sGlobal32_hz64 {c : ℝ} (hc : B (101 / 200) (51 / 100) c) : B (48345227124997243633 / 500000000000000000) (48555831589189230593 / 500000000000000000) (s3dm 12225 46 c) := by
    convert (sGlobal32_hz63 hc) using 1 <;>
      norm_num [s3dm, show (2 * (46 : ℝ)) = 92 by norm_num] <;> ring

theorem sGlobal32_hz65 : B (6126072185528622723889 / 500000000000000000) (2450428874211449090087 / 200000000000000000) ((s3ap 12225 46)^2) := bsq sGlobal32_hz9 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal32_hz66 : B (6126072185528622723889 / 250000000000000000) (2450428874211449090087 / 100000000000000000) ((2 : ℝ) * ((s3ap 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal32_hz65 (by norm_num) (by norm_num)

theorem sGlobal32_hz67 {c : ℝ} (hc : B (101 / 200) (51 / 100) c) : B (934904394307027700499 / 100000000000000000) (4715337562635413525063 / 500000000000000000) ((s3dm 12225 46 c)^2) := bsq (sGlobal32_hz64 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal32_hz68 {c : ℝ} (hc : B (101 / 200) (51 / 100) c) : B (1507361361684366384543 / 100000000000000000) (378881119976105347397 / 25000000000000000) (((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) := bsub sGlobal32_hz66 (sGlobal32_hz67 hc) (by norm_num) (by norm_num)

theorem sGlobal32_hz69 : B (1524735695971823534271 / 125000000000000000) (609894278388729413841 / 50000000000000000) ((s3am 12225 46)^2) := bsq sGlobal32_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal32_hz70 : B (1524735695971823534271 / 62500000000000000) (609894278388729413841 / 25000000000000000) ((2 : ℝ) * ((s3am 12225 46)^2)) := bmul (bpoint (2 : ℝ)) sGlobal32_hz69 (by norm_num) (by norm_num)

theorem sGlobal32_hz71 {c : ℝ} (hc : B (101 / 200) (51 / 100) c) : B (154469534218561807 / 250000000000000000) (621224257058232651 / 1000000000000000000) ((((2 : ℝ) * ((s3ap 12225 46)^2)) - ((s3dm 12225 46 c)^2)) / ((2 : ℝ) * ((s3am 12225 46)^2))) := bdiv (sGlobal32_hz68 hc) sGlobal32_hz70 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal32_hz72 {c : ℝ} (hc : B (101 / 200) (51 / 100) c) : B (154469534218561807 / 250000000000000000) (621224257058232651 / 1000000000000000000) (s3c1 12225 46 c) := by
    convert (sGlobal32_hz71 hc) using 1 <;>
      norm_num [s3c1] <;> ring

theorem sGlobal32_hz73 {c : ℝ} (hc : B (101 / 200) (51 / 100) c) : B (83563439141160113 / 125000000000000000) (167588652419986579 / 250000000000000000) (kdot c) := bkdot (sGlobal32_hz38 hc) sGlobal32_hz39.1 sGlobal32_hz47.2

theorem sGlobal32_hz74 : B (356003749488028853 / 500000000000000000) (17800187474401443 / 25000000000000000) (kdot ((154469534218561807 / 250000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (242995395639279377 / 500000000000000000)) (a := (226188781376442029 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (485990791278558753 / 1000000000000000000)) (a := (226188781376442019 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal32_hz75 : B (356682198413431413 / 500000000000000000) (713364396826862837 / 1000000000000000000) (kdot ((621224257058232651 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (12083967302630131 / 25000000000000000)) (a := (225123076296501743 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (483358692105205239 / 1000000000000000000)) (a := (450246152593003471 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem sGlobal32_hz76 {c : ℝ} (hc : B (101 / 200) (51 / 100) c) : B (356003749488028853 / 500000000000000000) (713364396826862837 / 1000000000000000000) (kdot (s3c1 12225 46 c)) := bkdot (sGlobal32_hz72 hc) sGlobal32_hz74.1 sGlobal32_hz75.2

theorem sGlobal32_hz77 {c : ℝ} (hc : B (101 / 200) (51 / 100) c) : B (10201 / 40000) (2601 / 10000) (c^2) := bsq (sGlobal32_hz38 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal32_hz78 {c : ℝ} (hc : B (101 / 200) (51 / 100) c) : B (7399 / 10000) (29799 / 40000) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (sGlobal32_hz77 hc) (by norm_num) (by norm_num)

theorem sGlobal32_hz79 {c : ℝ} (hc : B (101 / 200) (51 / 100) c) : B (860174400921115531 / 1000000000000000000) (863119342848948091 / 1000000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (sGlobal32_hz78 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal32_hz80 : B (39119999999999765769 / 1600000000000000) (3912000000000000489 / 160000000000000) ((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) := bmul (bpoint (149450625 : ℝ)) sGlobal32_hz10 (by norm_num) (by norm_num)

theorem sGlobal32_hz81 {c : ℝ} (hc : B (101 / 200) (51 / 100) c) : B (71879131202155497 / 125000000000000000) (289298015091359181 / 500000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (sGlobal32_hz79 hc) (sGlobal32_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal32_hz82 {c : ℝ} (hc : B (101 / 200) (51 / 100) c) : B (3514889515785382757899 / 250000000000000000) (2829334587593493143847 / 200000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) := bmul sGlobal32_hz80 (sGlobal32_hz81 hc) (by norm_num) (by norm_num)

theorem sGlobal32_hz83 {c : ℝ} (hc : B (101 / 200) (51 / 100) c) : B (3514889515785382757899 / 500000000000000000) (3536668234491866429809 / 500000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * ((√((1 : ℝ) - (c^2))) * (kdot c))) / (2 : ℝ)) := bdiv (sGlobal32_hz82 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal32_hz84 {c : ℝ} (hc : B (101 / 200) (51 / 100) c) : B (3514889515785382757899 / 500000000000000000) (3536668234491866429809 / 500000000000000000) (s3Cpa 12225 c) := by
    convert (sGlobal32_hz83 hc) using 1 <;>
      norm_num [s3Cpa, mA] <;> ring

theorem sGlobal32_hz85 {c : ℝ} (hc : B (101 / 200) (51 / 100) c) : B (27380201565541061 / 100000000000000000) (137369709892638433 / 500000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (sGlobal32_hz79 hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal32_hz86 {c : ℝ} (hc : B (101 / 200) (51 / 100) c) : B (42199536766285857 / 125000000000000000) (170940425468386311 / 500000000000000000) (c * (kdot c)) := bmul (sGlobal32_hz38 hc) (sGlobal32_hz73 hc) (by norm_num) (by norm_num)

theorem sGlobal32_hz87 {c : ℝ} (hc : B (101 / 200) (51 / 100) c) : B (-17019708820340503 / 250000000000000000) (-6285687434500999 / 100000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (sGlobal32_hz85 hc) (sGlobal32_hz86 hc) (by norm_num) (by norm_num)

theorem sGlobal32_hz88 {c : ℝ} (hc : B (101 / 200) (51 / 100) c) : B (-832263761314650700733 / 500000000000000000) (-1536850577735485053607 / 1000000000000000000) (((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) := bmul sGlobal32_hz80 (sGlobal32_hz87 hc) (by norm_num) (by norm_num)

theorem sGlobal32_hz89 {c : ℝ} (hc : B (101 / 200) (51 / 100) c) : B (-832263761314650700733 / 1000000000000000000) (-768425288867742526803 / 1000000000000000000) ((((149450625 : ℝ) * ((2 : ℝ) / (12225 : ℝ))) * (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c)))) / (2 : ℝ)) := bdiv (sGlobal32_hz88 hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal32_hz90 {c : ℝ} (hc : B (101 / 200) (51 / 100) c) : B (-832263761314650700733 / 1000000000000000000) (-768425288867742526803 / 1000000000000000000) (s3Cpp 12225 c) := by
    convert (sGlobal32_hz89 hc) using 1 <;>
      norm_num [s3Cpp, mA] <;> ring

theorem sGlobal32_hz91 {c : ℝ} (hc : B (101 / 200) (51 / 100) c) : B (7144924141504503224199 / 1000000000000000000) (1797120394729367817961 / 250000000000000000) ((s3Cpa 12225 c) + (s3r1 12225 46)) := badd (sGlobal32_hz84 hc) sGlobal32_hz33 (by norm_num) (by norm_num)

theorem sGlobal32_hz92 {c : ℝ} (hc : B (101 / 200) (51 / 100) c) : B (64692710079712024243 / 1000000000000000000) (65087094766598145707 / 1000000000000000000) (((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) := bdiv (sGlobal32_hz91 hc) sGlobal32_hz14 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal32_hz93 {c : ℝ} (hc : B (101 / 200) (51 / 100) c) : B (12963078621041216931 / 200000000000000000) (6520977779209220613 / 100000000000000000) ((((s3Cpa 12225 c) + (s3r1 12225 46)) / (s3am 12225 46)) + (s3e0 12225 46)) := badd (sGlobal32_hz92 hc) sGlobal32_hz16 (by norm_num) (by norm_num)

theorem sGlobal32_hz94 {c : ℝ} (hc : B (101 / 200) (51 / 100) c) : B (12963078621041216931 / 200000000000000000) (6520977779209220613 / 100000000000000000) (s3Lam 12225 46 c) := by
    convert (sGlobal32_hz93 hc) using 1 <;>
      norm_num [s3Lam] <;> ring

theorem sGlobal32_hz95 {c : ℝ} (hc : B (101 / 200) (51 / 100) c) : B (-755500354692158895133 / 1000000000000000000) (-138332376449050050397 / 200000000000000000) ((s3Cpp 12225 c) + (s3rpp 12225 46)) := badd (sGlobal32_hz90 hc) sGlobal32_hz37 (by norm_num) (by norm_num)

theorem sGlobal32_hz96 {c : ℝ} (hc : B (101 / 200) (51 / 100) c) : B (-269473527413726431399 / 500000000000000000) (-43228867640328140749 / 125000000000000000) (if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) := bweaken (bfirst (sGlobal32_hz95 hc) (sGlobal32_hz76 hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem sGlobal32_hz97 {c : ℝ} (hc : B (101 / 200) (51 / 100) c) : B (2100517591691198228439 / 500000000000000000) (4252315119694041877761 / 1000000000000000000) ((s3Lam 12225 46 c)^2) := bsq (sGlobal32_hz94 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal32_hz98 {c : ℝ} (hc : B (101 / 200) (51 / 100) c) : B (23860837001699437 / 62500000000000000) (2411997359734707 / 6250000000000000) ((s3c1 12225 46 c)^2) := bsq (sGlobal32_hz72 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal32_hz99 {c : ℝ} (hc : B (101 / 200) (51 / 100) c) : B (3838002640265293 / 6250000000000000) (38639162998300563 / 62500000000000000) ((1 : ℝ) - ((s3c1 12225 46 c)^2)) := bsub (bpoint (1 : ℝ)) (sGlobal32_hz98 hc) (by norm_num) (by norm_num)

theorem sGlobal32_hz100 {c : ℝ} (hc : B (101 / 200) (51 / 100) c) : B (195908209125225097 / 250000000000000000) (196568468982948949 / 250000000000000000) (√((1 : ℝ) - ((s3c1 12225 46 c)^2))) := bsqrt (sGlobal32_hz99 hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal32_hz101 {c : ℝ} (hc : B (101 / 200) (51 / 100) c) : B (492371032452592047 / 200000000000000000) (1235076116168451109 / 500000000000000000) (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))) := bmul pi_mem (sGlobal32_hz100 hc) (by norm_num) (by norm_num)

theorem sGlobal32_hz102 {c : ℝ} (hc : B (101 / 200) (51 / 100) c) : B (212589892658558037709 / 125000000000000000) (863640393000470861243 / 500000000000000000) (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2))))) := bdiv (sGlobal32_hz97 hc) (sGlobal32_hz101 hc) (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal32_hz103 {c : ℝ} (hc : B (101 / 200) (51 / 100) c) : B (580886043220505719437 / 500000000000000000) (690724922439158298247 / 500000000000000000) ((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) := badd (sGlobal32_hz96 hc) (sGlobal32_hz102 hc) (by norm_num) (by norm_num)

theorem sGlobal32_hz104 : B (3762781186094069 / 250000000000000000) (376278118609407 / 25000000000000000) ((s3e0 12225 46)^2) := bsq sGlobal32_hz16 (by norm_num) (by norm_num) (by norm_num)

theorem sGlobal32_hz105 {c : ℝ} (hc : B (101 / 200) (51 / 100) c) : B (23235742751315116303 / 20000000000000000) (690732448001530486387 / 500000000000000000) (((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) := badd (sGlobal32_hz103 hc) sGlobal32_hz104 (by norm_num) (by norm_num)

theorem sGlobal32_hz106 {c : ℝ} (hc : B (101 / 200) (51 / 100) c) : B (1200284211017003085281 / 1000000000000000000) (141996196945718524279 / 100000000000000000) ((((if 0 ≤ ((s3Cpp 12225 c) + (s3rpp 12225 46)) then (kdot (s3c1 12225 46 c)) * ((s3Cpp 12225 c) + (s3rpp 12225 46)) else ((s3Cpp 12225 c) + (s3rpp 12225 46)) / 2) + (((s3Lam 12225 46 c)^2) / (Real.pi * (√((1 : ℝ) - ((s3c1 12225 46 c)^2)))))) + ((s3e0 12225 46)^2)) + (s3rs 12225 46 maskSlack)) := badd (sGlobal32_hz105 hc) sGlobal32_hz29 (by norm_num) (by norm_num)

theorem sGlobal32_hz107 {c : ℝ} (hc : B (101 / 200) (51 / 100) c) : B (1200284211017003085281 / 1000000000000000000) (141996196945718524279 / 100000000000000000) (s3U 12225 46 maskSlack c) := by
    convert (sGlobal32_hz106 hc) using 1 <;>
      norm_num [s3U] <;> ring

theorem sGlobal32_hz108 {c : ℝ} (hc : B (101 / 200) (51 / 100) c) : B (-909027167937142975551 / 1000000000000000000) (-845188695490234332403 / 1000000000000000000) ((s3Cpp 12225 c) - (s3rpp 12225 46)) := bsub (sGlobal32_hz90 hc) sGlobal32_hz37 (by norm_num) (by norm_num)

theorem sGlobal32_hz109 {c : ℝ} (hc : B (101 / 200) (51 / 100) c) : B (-909027167937142975551 / 1000000000000000000) (-845188695490234332403 / 1000000000000000000) (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ)) := bweaken (bmin (sGlobal32_hz108 hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem sGlobal32_hz110 {c : ℝ} (hc : B (101 / 200) (51 / 100) c) : B (-648467617354711347711 / 1000000000000000000) (-120356137847767713941 / 200000000000000000) ((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) := bmul (sGlobal32_hz76 hc) (sGlobal32_hz109 hc) (by norm_num) (by norm_num)

theorem sGlobal32_hz111 {c : ℝ} (hc : B (101 / 200) (51 / 100) c) : B (-648482668479455723991 / 1000000000000000000) (-601795740363582945981 / 1000000000000000000) (((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) := bsub (sGlobal32_hz110 hc) sGlobal32_hz104 (by norm_num) (by norm_num)

theorem sGlobal32_hz112 {c : ℝ} (hc : B (101 / 200) (51 / 100) c) : B (-686979741933579994007 / 1000000000000000000) (-40018300863426888507 / 62500000000000000) ((((kdot (s3c1 12225 46 c)) * (min ((s3Cpp 12225 c) - (s3rpp 12225 46)) (0 : ℝ))) - ((s3e0 12225 46)^2)) - (s3rs 12225 46 maskSlack)) := bsub (sGlobal32_hz111 hc) sGlobal32_hz29 (by norm_num) (by norm_num)

theorem sGlobal32_hz113 {c : ℝ} (hc : B (101 / 200) (51 / 100) c) : B (-686979741933579994007 / 1000000000000000000) (-40018300863426888507 / 62500000000000000) (s3L 12225 46 maskSlack c) := by
    convert (sGlobal32_hz112 hc) using 1 <;>
      norm_num [s3L] <;> ring

theorem sGlobal32_hz114 {c : ℝ} (hc : B (101 / 200) (51 / 100) c) : B 0 (141996196945718524279 / 100000000000000000) |(s3U 12225 46 maskSlack c)| := bweaken (babs (sGlobal32_hz107 hc)) (by norm_num) (by norm_num)

theorem sGlobal32_hz115 {c : ℝ} (hc : B (101 / 200) (51 / 100) c) : B 0 (686979741933579994007 / 1000000000000000000) |(s3L 12225 46 maskSlack c)| := bweaken (babs (sGlobal32_hz113 hc)) (by norm_num) (by norm_num)

theorem sGlobal32_hz116 {c : ℝ} (hc : B (101 / 200) (51 / 100) c) : B 0 (141996196945718524279 / 100000000000000000) (max |(s3U 12225 46 maskSlack c)| |(s3L 12225 46 maskSlack c)|) := bweaken (bmax (sGlobal32_hz114 hc) (sGlobal32_hz115 hc)) (by norm_num) (by norm_num)

theorem sGlobal32_hz117 {c : ℝ} (hc : B (101 / 200) (51 / 100) c) : B 0 (141996196945718524279 / 100000000000000000) (s3nks 12225 46 maskSlack c) := by
    convert (sGlobal32_hz116 hc) using 1 <;>
      norm_num [s3nks] <;> ring

theorem sGlobal32 {c : ℝ} (hc : B (101 / 200) (51 / 100) c) :
    0 < s3am 12225 46 ∧ 0 ≤ s3dm 12225 46 c ∧
    s3dm 12225 46 c ^ 2 ≤ 2 * s3ap 12225 46 ^ 2 ∧ s3c1 12225 46 c < 1 ∧
    0 ≤ s3Cpa 12225 c - s3r1 12225 46 ∧
    s3e0 12225 46 ≤ (s3Cpa 12225 c - s3r1 12225 46) / s3ap 12225 46 ∧
    s3nks 12225 46 maskSlack c ≤ 12225 * (116153 / 1000000) := by

  refine ⟨lt_of_lt_of_le (by norm_num) sGlobal32_hz14.1,
    le_trans (by norm_num) (sGlobal32_hz64 hc).1, ?_,
    lt_of_le_of_lt (sGlobal32_hz72 hc).2 (by norm_num), ?_, ?_,
    le_trans (sGlobal32_hz117 hc).2 (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (sGlobal32_hz64 hc).1) (sGlobal32_hz64 hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) sGlobal32_hz9.1 2
    nlinarith only [h1, h2]
  · linarith only [(sGlobal32_hz84 hc).1, sGlobal32_hz33.2]
  · have hap : 0 < s3ap 12225 46 := lt_of_lt_of_le (by norm_num) sGlobal32_hz9.1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul sGlobal32_hz16.2 sGlobal32_hz9.2 (le_trans (by norm_num) sGlobal32_hz9.1) (by norm_num)
    linarith only [h, (sGlobal32_hz84 hc).1, sGlobal32_hz33.2]

end BstLean.Part255
