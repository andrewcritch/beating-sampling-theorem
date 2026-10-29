import BstLean.Part264bNormalize
namespace BstLean.BlueprintLow
open Real BstLean.Part130 BstLean.Part182 BstLean.Part197 BstLean.Part246 BstLean.Part255
open BstLean.Part264b
theorem lowCoarseS16_hz0 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B 0 (1 / 8000) x := hx

theorem lowCoarseS16_hz1 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B (23 / 50) (47 / 100) c := hc

theorem lowCoarseS16_hz2 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B (6782329983125268139 / 500000000000000000) (13564659966250536279 / 1000000000000000000) (√(184 : ℝ)) := bsqrt (bpoint (184 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS16_hz3 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS16_hz4 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B 0 (847791247890659 / 500000000000000000) ((√(184 : ℝ)) * x) := bmul (lowCoarseS16_hz2 hx hc) (lowCoarseS16_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS16_hz5 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B 1 (500847791247890659 / 500000000000000000) ((1 : ℝ) + ((√(184 : ℝ)) * x)) := badd (bpoint (1 : ℝ)) (lowCoarseS16_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS16_hz6 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B 1 (500847791247890659 / 500000000000000000) (nap x) := by
    convert (lowCoarseS16_hz5 hx hc) using 1 <;>
      norm_num [nap] <;> ring

theorem lowCoarseS16_hz7 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B 0 (1 / 64000000) (x^2) := bsq (lowCoarseS16_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS16_hz8 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B 0 (1 / 32000000) ((2 : ℝ) * (x^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS16_hz7 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS16_hz9 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B (31999999 / 32000000) 1 ((1 : ℝ) - ((2 : ℝ) * (x^2))) := bsub (bpoint (1 : ℝ)) (lowCoarseS16_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS16_hz10 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B (999999984374999877 / 1000000000000000000) 1 (√((1 : ℝ) - ((2 : ℝ) * (x^2)))) := bsqrt (lowCoarseS16_hz9 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS16_hz11 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B (998304401879218559 / 1000000000000000000) 1 ((√((1 : ℝ) - ((2 : ℝ) * (x^2)))) - ((√(184 : ℝ)) * x)) := bsub (lowCoarseS16_hz10 hx hc) (lowCoarseS16_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS16_hz12 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B (998304401879218559 / 1000000000000000000) 1 (nam x) := by
    convert (lowCoarseS16_hz11 hx hc) using 1 <;>
      norm_num [nam] <;> ring

theorem lowCoarseS16_hz13 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B (163037649309219301 / 250000000000000000) (326075298618777983 / 500000000000000000) (kdot ((23 / 50))) := by
    constructor
    · apply bkdot_lower (q := (121632728111907469 / 200000000000000000)) (a := (10928011282762237 / 20000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (9502556883742771 / 15625000000000000)) (a := (273200282068522827 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS16_hz14 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B (529 / 2500) (529 / 2500) (((23 / 50) : ℝ)^2) := bsq (bpoint ((23 / 50) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS16_hz15 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B (1971 / 2500) (1971 / 2500) ((1 : ℝ) - (((23 / 50) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS16_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS16_hz16 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B (887918915216924523 / 1000000000000000000) (221979728804231131 / 250000000000000000) (√((1 : ℝ) - (((23 / 50) : ℝ)^2))) := bsqrt (lowCoarseS16_hz15 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS16_hz17 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B (282633368843134123 / 1000000000000000000) (2261066950745073 / 8000000000000000) ((√((1 : ℝ) - (((23 / 50) : ℝ)^2))) / Real.pi) := bdiv (lowCoarseS16_hz16 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS16_hz18 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B (299989274728963513 / 1000000000000000000) (59997854945855149 / 200000000000000000) (((23 / 50) : ℝ) * (kdot ((23 / 50)))) := bmul (bpoint ((23 / 50) : ℝ)) (lowCoarseS16_hz13 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS16_hz19 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B (145655660893024409 / 250000000000000000) (58262264357240987 / 100000000000000000) (((√((1 : ℝ) - (((23 / 50) : ℝ)^2))) / Real.pi) + (((23 / 50) : ℝ) * (kdot ((23 / 50))))) := badd (lowCoarseS16_hz17 hx hc) (lowCoarseS16_hz18 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS16_hz20 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B (145655660893024409 / 250000000000000000) (58262264357240987 / 100000000000000000) (kappa ((23 / 50))) := by rw [kappa_eq]; exact (lowCoarseS16_hz19 hx hc)

theorem lowCoarseS16_hz21 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B (131149218372080969 / 200000000000000000) (655746091860768091 / 1000000000000000000) (kdot ((47 / 100))) := by
    constructor
    · apply bkdot_lower (q := (600453343472309121 / 1000000000000000000)) (a := (540752774390463831 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (938208349175483 / 1562500000000000)) (a := (4224631049921041 / 7812500000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS16_hz22 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B (2209 / 10000) (2209 / 10000) (((47 / 100) : ℝ)^2) := bsq (bpoint ((47 / 100) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS16_hz23 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B (7791 / 10000) (7791 / 10000) ((1 : ℝ) - (((47 / 100) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS16_hz22 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS16_hz24 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B (882666414904294407 / 1000000000000000000) (110333301863036801 / 125000000000000000) (√((1 : ℝ) - (((47 / 100) : ℝ)^2))) := bsqrt (lowCoarseS16_hz23 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS16_hz25 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B (140480723033220253 / 500000000000000000) (70240361516610127 / 250000000000000000) ((√((1 : ℝ) - (((47 / 100) : ℝ)^2))) / Real.pi) := bdiv (lowCoarseS16_hz24 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS16_hz26 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B (308200663174390277 / 1000000000000000000) (308200663174561003 / 1000000000000000000) (((47 / 100) : ℝ) * (kdot ((47 / 100)))) := bmul (bpoint ((47 / 100) : ℝ)) (lowCoarseS16_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS16_hz27 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B (589162109240830783 / 1000000000000000000) (589162109241001511 / 1000000000000000000) (((√((1 : ℝ) - (((47 / 100) : ℝ)^2))) / Real.pi) + (((47 / 100) : ℝ) * (kdot ((47 / 100))))) := badd (lowCoarseS16_hz25 hx hc) (lowCoarseS16_hz26 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS16_hz28 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B (589162109240830783 / 1000000000000000000) (589162109241001511 / 1000000000000000000) (kappa ((47 / 100))) := by rw [kappa_eq]; exact (lowCoarseS16_hz27 hx hc)

theorem lowCoarseS16_hz29 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B (145655660893024409 / 250000000000000000) (589162109241001511 / 1000000000000000000) (kappa c) := bkappa (lowCoarseS16_hz1 hx hc) (by norm_num) (by norm_num) (lowCoarseS16_hz20 hx hc).1 (lowCoarseS16_hz28 hx hc).2

theorem lowCoarseS16_hz30 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B (410837890758998489 / 1000000000000000000) (104344339106975591 / 250000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (lowCoarseS16_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS16_hz31 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B (410837890758998489 / 500000000000000000) (104344339106975591 / 125000000000000000) ((2 : ℝ) * ((1 : ℝ) - (kappa c))) := bmul (bpoint (2 : ℝ)) (lowCoarseS16_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS16_hz32 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B 0 (1 / 8000000) ((8 : ℝ) * (x^2)) := bmul (bpoint (8 : ℝ)) (lowCoarseS16_hz7 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS16_hz33 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B (410837828258998489 / 500000000000000000) (104344339106975591 / 125000000000000000) (((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2))) := bsub (lowCoarseS16_hz31 hx hc) (lowCoarseS16_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS16_hz34 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B (906463268157070431 / 1000000000000000000) (182729823822582911 / 200000000000000000) (√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) := bsqrt (lowCoarseS16_hz33 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS16_hz35 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B (6782329983125268139 / 250000000000000000) (13564659966250536279 / 500000000000000000) ((2 : ℝ) * (√(184 : ℝ))) := bmul (bpoint (2 : ℝ)) (lowCoarseS16_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS16_hz36 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B 0 (678232998312527 / 200000000000000000) (((2 : ℝ) * (√(184 : ℝ))) * x) := bmul (lowCoarseS16_hz35 hx hc) (lowCoarseS16_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS16_hz37 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B (225768025791376949 / 250000000000000000) (182729823822582911 / 200000000000000000) ((√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) - (((2 : ℝ) * (√(184 : ℝ))) * x)) := bsub (lowCoarseS16_hz34 hx hc) (lowCoarseS16_hz36 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS16_hz38 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B (225768025791376949 / 250000000000000000) (182729823822582911 / 200000000000000000) (ndm x c) := by
    convert (lowCoarseS16_hz37 hx hc) using 1 <;>
      norm_num [ndm] <;> ring

theorem lowCoarseS16_hz39 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B 1 (1003394039991562637 / 1000000000000000000) ((nap x)^2) := bsq (lowCoarseS16_hz6 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS16_hz40 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B 2 (1003394039991562637 / 500000000000000000) ((2 : ℝ) * ((nap x)^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS16_hz39 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS16_hz41 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B (163107844703154711 / 200000000000000000) (834754712855804729 / 1000000000000000000) ((ndm x c)^2) := bsq (lowCoarseS16_hz38 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS16_hz42 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B (1165245287144195271 / 1000000000000000000) (1191248856467351719 / 1000000000000000000) (((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) := bsub (lowCoarseS16_hz40 hx hc) (lowCoarseS16_hz41 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS16_hz43 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B (199322335762284863 / 200000000000000000) 1 ((nam x)^2) := bsq (lowCoarseS16_hz12 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS16_hz44 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B (199322335762284863 / 100000000000000000) 2 ((2 : ℝ) * ((nam x)^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS16_hz43 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS16_hz45 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B (116524528714419527 / 200000000000000000) (597649456550647161 / 1000000000000000000) ((((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) / ((2 : ℝ) * ((nam x)^2))) := bdiv (lowCoarseS16_hz42 hx hc) (lowCoarseS16_hz44 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS16_hz46 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B (116524528714419527 / 200000000000000000) (597649456550647161 / 1000000000000000000) (nc1 x c) := by
    convert (lowCoarseS16_hz45 hx hc) using 1 <;>
      norm_num [nc1] <;> ring

theorem lowCoarseS16_hz47 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B (163037649309219301 / 250000000000000000) (655746091860768091 / 1000000000000000000) (kdot c) := bkdot (lowCoarseS16_hz1 hx hc) (lowCoarseS16_hz13 hx hc).1 (lowCoarseS16_hz21 hx hc).2

theorem lowCoarseS16_hz48 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B (697973431267234781 / 1000000000000000000) (348986715633617477 / 500000000000000000) (kdot ((116524528714419527 / 200000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (256770873647945371 / 500000000000000000)) (a := (23721111237994699 / 50000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (513541747295890741 / 1000000000000000000)) (a := (47442222475989371 / 100000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS16_hz49 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B (8798731750618993 / 12500000000000000) (703898540049519497 / 1000000000000000000) (kdot ((597649456550647161 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (501835694046807003 / 1000000000000000000)) (a := (232557542824410527 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (250917847023403501 / 500000000000000000)) (a := (232557542824410483 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS16_hz50 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B (697973431267234781 / 1000000000000000000) (703898540049519497 / 1000000000000000000) (kdot (nc1 x c)) := bkdot (lowCoarseS16_hz46 hx hc) (lowCoarseS16_hz48 hx hc).1 (lowCoarseS16_hz49 hx hc).2

theorem lowCoarseS16_hz51 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B (529 / 2500) (2209 / 10000) (c^2) := bsq (lowCoarseS16_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS16_hz52 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B (7791 / 10000) (1971 / 2500) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS16_hz51 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS16_hz53 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B (882666414904294407 / 1000000000000000000) (221979728804231131 / 250000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (lowCoarseS16_hz52 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS16_hz54 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B (575631429640768847 / 1000000000000000000) (18195292454460967 / 31250000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (lowCoarseS16_hz53 hx hc) (lowCoarseS16_hz47 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS16_hz55 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B (575631429640768847 / 1000000000000000000) (18195292454460967 / 31250000000000000) (npa c) := by
    convert (lowCoarseS16_hz54 hx hc) using 1 <;>
      norm_num [npa] <;> ring

theorem lowCoarseS16_hz56 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B (140480723033220253 / 500000000000000000) (2261066950745073 / 8000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (lowCoarseS16_hz53 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS16_hz57 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B (299989274728963513 / 1000000000000000000) (308200663174561003 / 1000000000000000000) (c * (kdot c)) := bmul (lowCoarseS16_hz1 hx hc) (lowCoarseS16_hz47 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS16_hz58 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B (-27239217108120497 / 1000000000000000000) (-4338976471457347 / 250000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (lowCoarseS16_hz56 hx hc) (lowCoarseS16_hz57 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS16_hz59 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B (-27239217108120497 / 1000000000000000000) (-4338976471457347 / 250000000000000000) (npp c) := by
    convert (lowCoarseS16_hz58 hx hc) using 1 <;>
      norm_num [npp] <;> ring

theorem lowCoarseS16_hz60 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B 0 (23 / 4000) ((46 : ℝ) * x) := bmul (bpoint (46 : ℝ)) (lowCoarseS16_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS16_hz61 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B (9591663046625439083 / 1000000000000000000) (2399353261656359771 / 250000000000000000) ((√(92 : ℝ)) + ((46 : ℝ) * x)) := badd (lowCoarseS16_hz3 hx hc) (lowCoarseS16_hz60 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS16_hz62 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B (28774989139876317249 / 250000000000000000) (7198059784969079313 / 62500000000000000) ((12 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (bpoint (12 : ℝ)) (lowCoarseS16_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS16_hz63 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B 0 (14396119569938159 / 1000000000000000000) (((12 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS16_hz62 hx hc) (lowCoarseS16_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS16_hz64 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B 0 (14396119569938159 / 1000000000000000000) (nr1 x) := by
    convert (lowCoarseS16_hz63 hx hc) using 1 <;>
      norm_num [nr1] <;> ring

theorem lowCoarseS16_hz65 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B (9591663046625439083 / 125000000000000000) (2399353261656359771 / 31250000000000000) ((8 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (bpoint (8 : ℝ)) (lowCoarseS16_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS16_hz66 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B 0 (59983831541409 / 6250000000000000) (((8 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS16_hz65 hx hc) (lowCoarseS16_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS16_hz67 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B 0 (59983831541409 / 6250000000000000) (nrpp x) := by
    convert (lowCoarseS16_hz66 hx hc) using 1 <;>
      norm_num [nrpp] <;> ring

theorem lowCoarseS16_hz68 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B 0 (847791247890659 / 500000000000000000) (ne0 x) := by
    convert (lowCoarseS16_hz4 hx hc) using 1 <;>
      norm_num [ne0] <;> ring

theorem lowCoarseS16_hz69 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B (575631429640768847 / 1000000000000000000) (596645478112689103 / 1000000000000000000) ((npa c) + (nr1 x)) := badd (lowCoarseS16_hz55 hx hc) (lowCoarseS16_hz64 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS16_hz70 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B (575631429640768847 / 1000000000000000000) (597658867365061667 / 1000000000000000000) (((npa c) + (nr1 x)) / (nam x)) := bdiv (lowCoarseS16_hz69 hx hc) (lowCoarseS16_hz12 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS16_hz71 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B (575631429640768847 / 1000000000000000000) (119870889972168597 / 200000000000000000) ((((npa c) + (nr1 x)) / (nam x)) + (ne0 x)) := badd (lowCoarseS16_hz70 hx hc) (lowCoarseS16_hz68 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS16_hz72 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B (575631429640768847 / 1000000000000000000) (119870889972168597 / 200000000000000000) (nlam x c) := by
    convert (lowCoarseS16_hz71 hx hc) using 1 <;>
      norm_num [nlam] <;> ring

theorem lowCoarseS16_hz73 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS16_hz74 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B 0 (59947894041409 / 100000000000000000) ((√(23 : ℝ)) * x) := bmul (lowCoarseS16_hz73 hx hc) (lowCoarseS16_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS16_hz75 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B (1 / 2) (50059947894041409 / 100000000000000000) (((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)) := badd (bpoint ((1 / 2) : ℝ)) (lowCoarseS16_hz74 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS16_hz76 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B (176776695296636881 / 250000000000000000) (353765274914177413 / 500000000000000000) (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) := bsqrt (lowCoarseS16_hz75 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS16_hz77 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B 0 (59947894041409 / 50000000000000000) ((√(92 : ℝ)) * x) := bmul (lowCoarseS16_hz3 hx hc) (lowCoarseS16_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS16_hz78 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B (176776695296636881 / 250000000000000000) (354364753854591503 / 500000000000000000) ((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x)) := badd (lowCoarseS16_hz76 hx hc) (lowCoarseS16_hz77 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS16_hz79 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B (499999999999999999 / 1000000000000000000) (251148757548850447 / 500000000000000000) (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2) := bsq (lowCoarseS16_hz78 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS16_hz80 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B (499999999999999999 / 125000000000000000) (251148757548850447 / 62500000000000000) ((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) := bmul (bpoint (8 : ℝ)) (lowCoarseS16_hz79 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS16_hz81 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B (7673330437300351251 / 200000000000000000) (1928302689874485209 / 50000000000000000) (((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (lowCoarseS16_hz80 hx hc) (lowCoarseS16_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS16_hz82 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B 0 (2410378362343107 / 500000000000000000) ((((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS16_hz81 hx hc) (lowCoarseS16_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS16_hz83 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B 0 (2410378362343107 / 500000000000000000) (nrs x) := by
    convert (lowCoarseS16_hz82 hx hc) using 1 <;>
      norm_num [nrs] <;> ring

theorem lowCoarseS16_hz84 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B (-27239217108120497 / 1000000000000000000) (-1939623209800987 / 250000000000000000) ((npp c) + (nrpp x)) := badd (lowCoarseS16_hz59 hx hc) (lowCoarseS16_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS16_hz85 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B (-19173645154497913 / 1000000000000000000) (-1939623209800987 / 500000000000000000) (if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) := bweaken (bfirst (lowCoarseS16_hz84 hx hc) (lowCoarseS16_hz50 hx hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem lowCoarseS16_hz86 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B (66270308558055083 / 200000000000000000) (89806439141998437 / 250000000000000000) ((nlam x c)^2) := bsq (lowCoarseS16_hz72 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS16_hz87 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B (339449144802939521 / 1000000000000000000) (357184872915283889 / 1000000000000000000) ((nc1 x c)^2) := bsq (lowCoarseS16_hz46 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS16_hz88 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B (642815127084716111 / 1000000000000000000) (660550855197060479 / 1000000000000000000) ((1 : ℝ) - ((nc1 x c)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS16_hz87 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS16_hz89 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B (400878761935799023 / 500000000000000000) (101592849711257091 / 125000000000000000) (√((1 : ℝ) - ((nc1 x c)^2))) := bsqrt (lowCoarseS16_hz88 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS16_hz90 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B (2518795546955355703 / 1000000000000000000) (510661360496219559 / 200000000000000000) (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))) := bmul pi_mem (lowCoarseS16_hz89 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS16_hz91 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B (129773493129887363 / 1000000000000000000) (142618068783794317 / 1000000000000000000) (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2))))) := bdiv (lowCoarseS16_hz86 hx hc) (lowCoarseS16_hz90 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS16_hz92 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B (2211996959507789 / 20000000000000000) (138738822364192343 / 1000000000000000000) ((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) := badd (lowCoarseS16_hz85 hx hc) (lowCoarseS16_hz91 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS16_hz93 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B 0 (2875000000001 / 1000000000000000000) ((ne0 x)^2) := bsq (lowCoarseS16_hz68 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS16_hz94 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B (2211996959507789 / 20000000000000000) (17342712170524043 / 125000000000000000) (((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) + ((ne0 x)^2)) := badd (lowCoarseS16_hz92 hx hc) (lowCoarseS16_hz93 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS16_hz95 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B (2211996959507789 / 20000000000000000) (71781227044439279 / 500000000000000000) ((((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) + ((ne0 x)^2)) + (nrs x)) := badd (lowCoarseS16_hz94 hx hc) (lowCoarseS16_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS16_hz96 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B (2211996959507789 / 20000000000000000) (71781227044439279 / 500000000000000000) (nu x c) := by
    convert (lowCoarseS16_hz95 hx hc) using 1 <;>
      norm_num [nu] <;> ring

theorem lowCoarseS16_hz97 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B (-36836630154745937 / 1000000000000000000) (-4338976471457347 / 250000000000000000) ((npp c) - (nrpp x)) := bsub (lowCoarseS16_hz59 hx hc) (lowCoarseS16_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS16_hz98 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B (-36836630154745937 / 1000000000000000000) (-4338976471457347 / 250000000000000000) (min ((npp c) - (nrpp x)) (0 : ℝ)) := bweaken (bmin (lowCoarseS16_hz97 hx hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem lowCoarseS16_hz99 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B (-25929250186269771 / 1000000000000000000) (-12113961183883533 / 1000000000000000000) ((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) := bmul (lowCoarseS16_hz50 hx hc) (lowCoarseS16_hz98 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS16_hz100 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B (-6483031296567443 / 250000000000000000) (-12113961183883533 / 1000000000000000000) (((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) - ((ne0 x)^2)) := bsub (lowCoarseS16_hz99 hx hc) (lowCoarseS16_hz93 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS16_hz101 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B (-15376440955477993 / 500000000000000000) (-12113961183883533 / 1000000000000000000) ((((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) - ((ne0 x)^2)) - (nrs x)) := bsub (lowCoarseS16_hz100 hx hc) (lowCoarseS16_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS16_hz102 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B (-15376440955477993 / 500000000000000000) (-12113961183883533 / 1000000000000000000) (nl x c) := by
    convert (lowCoarseS16_hz101 hx hc) using 1 <;>
      norm_num [nl] <;> ring

theorem lowCoarseS16_hz103 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B 0 (71781227044439279 / 500000000000000000) |(nu x c)| := bweaken (babs (lowCoarseS16_hz96 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS16_hz104 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B 0 (15376440955477993 / 500000000000000000) |(nl x c)| := bweaken (babs (lowCoarseS16_hz102 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS16_hz105 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B 0 (71781227044439279 / 500000000000000000) (max |(nu x c)| |(nl x c)|) := bweaken (bmax (lowCoarseS16_hz103 hx hc) (lowCoarseS16_hz104 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS16_hz106 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) : B 0 (71781227044439279 / 500000000000000000) (ns x c) := by
    convert (lowCoarseS16_hz105 hx hc) using 1 <;>
      norm_num [ns] <;> ring

theorem lowCoarseS16 {x c : ℝ}
    (hx : B 0 (1/8000) x) (hc : B (23 / 50) (47 / 100) c) :
    0 < nam x ∧ 0 ≤ ndm x c ∧ ndm x c ^ 2 ≤ 2 * nap x ^ 2 ∧ nc1 x c < 1 ∧
    0 ≤ npa c - nr1 x ∧ ne0 x ≤ (npa c - nr1 x) / nap x ∧ ns x c ≤ (1 / 5) := by
  refine ⟨lt_of_lt_of_le (by norm_num) (lowCoarseS16_hz12 hx hc).1,
    le_trans (by norm_num) (lowCoarseS16_hz38 hx hc).1, ?_,
    lt_of_le_of_lt (lowCoarseS16_hz46 hx hc).2 (by norm_num), ?_, ?_, (lowCoarseS16_hz106 hx hc).2.trans (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (lowCoarseS16_hz38 hx hc).1) (lowCoarseS16_hz38 hx hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) (lowCoarseS16_hz6 hx hc).1 2
    nlinarith only [h1,h2]
  · linarith only [(lowCoarseS16_hz55 hx hc).1,(lowCoarseS16_hz64 hx hc).2]
  · have hap : 0 < nap x := lt_of_lt_of_le (by norm_num) (lowCoarseS16_hz6 hx hc).1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul (lowCoarseS16_hz68 hx hc).2 (lowCoarseS16_hz6 hx hc).2 (le_trans (by norm_num) (lowCoarseS16_hz6 hx hc).1) (by norm_num)
    linarith only [h,(lowCoarseS16_hz55 hx hc).1,(lowCoarseS16_hz64 hx hc).2]

theorem lowCoarseS17_hz0 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B 0 (1 / 8000) x := hx

theorem lowCoarseS17_hz1 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B (47 / 100) (12 / 25) c := hc

theorem lowCoarseS17_hz2 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B (6782329983125268139 / 500000000000000000) (13564659966250536279 / 1000000000000000000) (√(184 : ℝ)) := bsqrt (bpoint (184 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS17_hz3 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS17_hz4 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B 0 (847791247890659 / 500000000000000000) ((√(184 : ℝ)) * x) := bmul (lowCoarseS17_hz2 hx hc) (lowCoarseS17_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS17_hz5 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B 1 (500847791247890659 / 500000000000000000) ((1 : ℝ) + ((√(184 : ℝ)) * x)) := badd (bpoint (1 : ℝ)) (lowCoarseS17_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS17_hz6 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B 1 (500847791247890659 / 500000000000000000) (nap x) := by
    convert (lowCoarseS17_hz5 hx hc) using 1 <;>
      norm_num [nap] <;> ring

theorem lowCoarseS17_hz7 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B 0 (1 / 64000000) (x^2) := bsq (lowCoarseS17_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS17_hz8 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B 0 (1 / 32000000) ((2 : ℝ) * (x^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS17_hz7 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS17_hz9 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B (31999999 / 32000000) 1 ((1 : ℝ) - ((2 : ℝ) * (x^2))) := bsub (bpoint (1 : ℝ)) (lowCoarseS17_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS17_hz10 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B (999999984374999877 / 1000000000000000000) 1 (√((1 : ℝ) - ((2 : ℝ) * (x^2)))) := bsqrt (lowCoarseS17_hz9 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS17_hz11 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B (998304401879218559 / 1000000000000000000) 1 ((√((1 : ℝ) - ((2 : ℝ) * (x^2)))) - ((√(184 : ℝ)) * x)) := bsub (lowCoarseS17_hz10 hx hc) (lowCoarseS17_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS17_hz12 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B (998304401879218559 / 1000000000000000000) 1 (nam x) := by
    convert (lowCoarseS17_hz11 hx hc) using 1 <;>
      norm_num [nam] <;> ring

theorem lowCoarseS17_hz13 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B (131149218372080969 / 200000000000000000) (655746091860768091 / 1000000000000000000) (kdot ((47 / 100))) := by
    constructor
    · apply bkdot_lower (q := (600453343472309121 / 1000000000000000000)) (a := (540752774390463831 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (938208349175483 / 1562500000000000)) (a := (4224631049921041 / 7812500000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS17_hz14 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B (2209 / 10000) (2209 / 10000) (((47 / 100) : ℝ)^2) := bsq (bpoint ((47 / 100) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS17_hz15 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B (7791 / 10000) (7791 / 10000) ((1 : ℝ) - (((47 / 100) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS17_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS17_hz16 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B (882666414904294407 / 1000000000000000000) (110333301863036801 / 125000000000000000) (√((1 : ℝ) - (((47 / 100) : ℝ)^2))) := bsqrt (lowCoarseS17_hz15 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS17_hz17 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B (140480723033220253 / 500000000000000000) (70240361516610127 / 250000000000000000) ((√((1 : ℝ) - (((47 / 100) : ℝ)^2))) / Real.pi) := bdiv (lowCoarseS17_hz16 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS17_hz18 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B (308200663174390277 / 1000000000000000000) (308200663174561003 / 1000000000000000000) (((47 / 100) : ℝ) * (kdot ((47 / 100)))) := bmul (bpoint ((47 / 100) : ℝ)) (lowCoarseS17_hz13 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS17_hz19 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B (589162109240830783 / 1000000000000000000) (589162109241001511 / 1000000000000000000) (((√((1 : ℝ) - (((47 / 100) : ℝ)^2))) / Real.pi) + (((47 / 100) : ℝ) * (kdot ((47 / 100))))) := badd (lowCoarseS17_hz17 hx hc) (lowCoarseS17_hz18 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS17_hz20 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B (589162109240830783 / 1000000000000000000) (589162109241001511 / 1000000000000000000) (kappa ((47 / 100))) := by rw [kappa_eq]; exact (lowCoarseS17_hz19 hx hc)

theorem lowCoarseS17_hz21 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B (659363344522858571 / 1000000000000000000) (82420418065381437 / 125000000000000000) (kdot ((12 / 25))) := by
    constructor
    · apply bkdot_lower (q := (296374489181909579 / 500000000000000000)) (a := (535070807195192459 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (592748978363819157 / 1000000000000000000)) (a := (267535403597444707 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS17_hz22 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B (144 / 625) (144 / 625) (((12 / 25) : ℝ)^2) := bsq (bpoint ((12 / 25) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS17_hz23 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B (481 / 625) (481 / 625) ((1 : ℝ) - (((12 / 25) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS17_hz22 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS17_hz24 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B (6853660062331659 / 7812500000000000) (877268487978452353 / 1000000000000000000) (√((1 : ℝ) - (((12 / 25) : ℝ)^2))) := bsqrt (lowCoarseS17_hz23 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS17_hz25 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B (279243232561047303 / 1000000000000000000) (34905404070130913 / 125000000000000000) ((√((1 : ℝ) - (((12 / 25) : ℝ)^2))) / Real.pi) := bdiv (lowCoarseS17_hz24 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS17_hz26 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B (158247202685486057 / 500000000000000000) (316494405371064719 / 1000000000000000000) (((12 / 25) : ℝ) * (kdot ((12 / 25)))) := bmul (bpoint ((12 / 25) : ℝ)) (lowCoarseS17_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS17_hz27 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B (595737637932019417 / 1000000000000000000) (595737637932112023 / 1000000000000000000) (((√((1 : ℝ) - (((12 / 25) : ℝ)^2))) / Real.pi) + (((12 / 25) : ℝ) * (kdot ((12 / 25))))) := badd (lowCoarseS17_hz25 hx hc) (lowCoarseS17_hz26 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS17_hz28 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B (595737637932019417 / 1000000000000000000) (595737637932112023 / 1000000000000000000) (kappa ((12 / 25))) := by rw [kappa_eq]; exact (lowCoarseS17_hz27 hx hc)

theorem lowCoarseS17_hz29 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B (589162109240830783 / 1000000000000000000) (595737637932112023 / 1000000000000000000) (kappa c) := bkappa (lowCoarseS17_hz1 hx hc) (by norm_num) (by norm_num) (lowCoarseS17_hz20 hx hc).1 (lowCoarseS17_hz28 hx hc).2

theorem lowCoarseS17_hz30 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B (404262362067887977 / 1000000000000000000) (410837890759169217 / 1000000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (lowCoarseS17_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS17_hz31 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B (404262362067887977 / 500000000000000000) (410837890759169217 / 500000000000000000) ((2 : ℝ) * ((1 : ℝ) - (kappa c))) := bmul (bpoint (2 : ℝ)) (lowCoarseS17_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS17_hz32 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B 0 (1 / 8000000) ((8 : ℝ) * (x^2)) := bmul (bpoint (8 : ℝ)) (lowCoarseS17_hz7 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS17_hz33 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B (404262299567887977 / 500000000000000000) (410837890759169217 / 500000000000000000) (((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2))) := bsub (lowCoarseS17_hz31 hx hc) (lowCoarseS17_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS17_hz34 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B (179835991852106841 / 200000000000000000) (453231668553273767 / 500000000000000000) (√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) := bsqrt (lowCoarseS17_hz33 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS17_hz35 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B (6782329983125268139 / 250000000000000000) (13564659966250536279 / 500000000000000000) ((2 : ℝ) * (√(184 : ℝ))) := bmul (bpoint (2 : ℝ)) (lowCoarseS17_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS17_hz36 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B 0 (678232998312527 / 200000000000000000) (((2 : ℝ) * (√(184 : ℝ))) * x) := bmul (lowCoarseS17_hz35 hx hc) (lowCoarseS17_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS17_hz37 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B (89578879426897157 / 100000000000000000) (453231668553273767 / 500000000000000000) ((√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) - (((2 : ℝ) * (√(184 : ℝ))) * x)) := bsub (lowCoarseS17_hz34 hx hc) (lowCoarseS17_hz36 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS17_hz38 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B (89578879426897157 / 100000000000000000) (453231668553273767 / 500000000000000000) (ndm x c) := by
    convert (lowCoarseS17_hz37 hx hc) using 1 <;>
      norm_num [ndm] <;> ring

theorem lowCoarseS17_hz39 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B 1 (1003394039991562637 / 1000000000000000000) ((nap x)^2) := bsq (lowCoarseS17_hz6 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS17_hz40 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B 2 (1003394039991562637 / 500000000000000000) ((2 : ℝ) * ((nap x)^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS17_hz39 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS17_hz41 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B (50152347746116117 / 62500000000000000) (205418945379584609 / 250000000000000000) ((ndm x c)^2) := bsq (lowCoarseS17_hz38 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS17_hz42 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B (294581054620415391 / 250000000000000000) (602175258022633701 / 500000000000000000) (((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) := bsub (lowCoarseS17_hz40 hx hc) (lowCoarseS17_hz41 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS17_hz43 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B (199322335762284863 / 200000000000000000) 1 ((nam x)^2) := bsq (lowCoarseS17_hz12 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS17_hz44 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B (199322335762284863 / 100000000000000000) 2 ((2 : ℝ) * ((nam x)^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS17_hz43 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS17_hz45 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B (294581054620415391 / 500000000000000000) (604222558118923453 / 1000000000000000000) ((((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) / ((2 : ℝ) * ((nam x)^2))) := bdiv (lowCoarseS17_hz42 hx hc) (lowCoarseS17_hz44 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS17_hz46 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B (294581054620415391 / 500000000000000000) (604222558118923453 / 1000000000000000000) (nc1 x c) := by
    convert (lowCoarseS17_hz45 hx hc) using 1 <;>
      norm_num [nc1] <;> ring

theorem lowCoarseS17_hz47 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B (131149218372080969 / 200000000000000000) (82420418065381437 / 125000000000000000) (kdot c) := bkdot (lowCoarseS17_hz1 hx hc) (lowCoarseS17_hz13 hx hc).1 (lowCoarseS17_hz21 hx hc).2

theorem lowCoarseS17_hz48 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B (700542063623857133 / 1000000000000000000) (17513551590596431 / 25000000000000000) (kdot ((294581054620415391 / 500000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (254226693501225551 / 500000000000000000)) (a := (47038742648922507 / 100000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (508453387002451101 / 1000000000000000000)) (a := (470387426489224903 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS17_hz49 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B (706516213760414881 / 1000000000000000000) (706516213760414917 / 1000000000000000000) (kdot ((604222558118923453 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (124174728107007681 / 250000000000000000)) (a := (461003253398998929 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (496698912428030723 / 1000000000000000000)) (a := (3688026027191991 / 8000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS17_hz50 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B (700542063623857133 / 1000000000000000000) (706516213760414917 / 1000000000000000000) (kdot (nc1 x c)) := bkdot (lowCoarseS17_hz46 hx hc) (lowCoarseS17_hz48 hx hc).1 (lowCoarseS17_hz49 hx hc).2

theorem lowCoarseS17_hz51 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B (2209 / 10000) (144 / 625) (c^2) := bsq (lowCoarseS17_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS17_hz52 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B (481 / 625) (7791 / 10000) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS17_hz51 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS17_hz53 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B (6853660062331659 / 7812500000000000) (110333301863036801 / 125000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (lowCoarseS17_hz52 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS17_hz54 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B (575265382504156679 / 1000000000000000000) (58199787942946699 / 100000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (lowCoarseS17_hz53 hx hc) (lowCoarseS17_hz47 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS17_hz55 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B (575265382504156679 / 1000000000000000000) (58199787942946699 / 100000000000000000) (npa c) := by
    convert (lowCoarseS17_hz54 hx hc) using 1 <;>
      norm_num [npa] <;> ring

theorem lowCoarseS17_hz56 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B (279243232561047303 / 1000000000000000000) (70240361516610127 / 250000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (lowCoarseS17_hz53 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS17_hz57 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B (308200663174390277 / 1000000000000000000) (316494405371064719 / 1000000000000000000) (c * (kdot c)) := bmul (lowCoarseS17_hz1 hx hc) (lowCoarseS17_hz47 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS17_hz58 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B (-4656396601252177 / 125000000000000000) (-27239217107949769 / 1000000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (lowCoarseS17_hz56 hx hc) (lowCoarseS17_hz57 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS17_hz59 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B (-4656396601252177 / 125000000000000000) (-27239217107949769 / 1000000000000000000) (npp c) := by
    convert (lowCoarseS17_hz58 hx hc) using 1 <;>
      norm_num [npp] <;> ring

theorem lowCoarseS17_hz60 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B 0 (23 / 4000) ((46 : ℝ) * x) := bmul (bpoint (46 : ℝ)) (lowCoarseS17_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS17_hz61 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B (9591663046625439083 / 1000000000000000000) (2399353261656359771 / 250000000000000000) ((√(92 : ℝ)) + ((46 : ℝ) * x)) := badd (lowCoarseS17_hz3 hx hc) (lowCoarseS17_hz60 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS17_hz62 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B (28774989139876317249 / 250000000000000000) (7198059784969079313 / 62500000000000000) ((12 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (bpoint (12 : ℝ)) (lowCoarseS17_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS17_hz63 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B 0 (14396119569938159 / 1000000000000000000) (((12 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS17_hz62 hx hc) (lowCoarseS17_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS17_hz64 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B 0 (14396119569938159 / 1000000000000000000) (nr1 x) := by
    convert (lowCoarseS17_hz63 hx hc) using 1 <;>
      norm_num [nr1] <;> ring

theorem lowCoarseS17_hz65 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B (9591663046625439083 / 125000000000000000) (2399353261656359771 / 31250000000000000) ((8 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (bpoint (8 : ℝ)) (lowCoarseS17_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS17_hz66 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B 0 (59983831541409 / 6250000000000000) (((8 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS17_hz65 hx hc) (lowCoarseS17_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS17_hz67 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B 0 (59983831541409 / 6250000000000000) (nrpp x) := by
    convert (lowCoarseS17_hz66 hx hc) using 1 <;>
      norm_num [nrpp] <;> ring

theorem lowCoarseS17_hz68 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B 0 (847791247890659 / 500000000000000000) (ne0 x) := by
    convert (lowCoarseS17_hz4 hx hc) using 1 <;>
      norm_num [ne0] <;> ring

theorem lowCoarseS17_hz69 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B (575265382504156679 / 1000000000000000000) (596393998999405149 / 1000000000000000000) ((npa c) + (nr1 x)) := badd (lowCoarseS17_hz55 hx hc) (lowCoarseS17_hz64 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS17_hz70 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B (575265382504156679 / 1000000000000000000) (59740696112002201 / 100000000000000000) (((npa c) + (nr1 x)) / (nam x)) := bdiv (lowCoarseS17_hz69 hx hc) (lowCoarseS17_hz12 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS17_hz71 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B (575265382504156679 / 1000000000000000000) (9360977243996927 / 15625000000000000) ((((npa c) + (nr1 x)) / (nam x)) + (ne0 x)) := badd (lowCoarseS17_hz70 hx hc) (lowCoarseS17_hz68 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS17_hz72 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B (575265382504156679 / 1000000000000000000) (9360977243996927 / 15625000000000000) (nlam x c) := by
    convert (lowCoarseS17_hz71 hx hc) using 1 <;>
      norm_num [nlam] <;> ring

theorem lowCoarseS17_hz73 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS17_hz74 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B 0 (59947894041409 / 100000000000000000) ((√(23 : ℝ)) * x) := bmul (lowCoarseS17_hz73 hx hc) (lowCoarseS17_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS17_hz75 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B (1 / 2) (50059947894041409 / 100000000000000000) (((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)) := badd (bpoint ((1 / 2) : ℝ)) (lowCoarseS17_hz74 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS17_hz76 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B (176776695296636881 / 250000000000000000) (353765274914177413 / 500000000000000000) (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) := bsqrt (lowCoarseS17_hz75 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS17_hz77 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B 0 (59947894041409 / 50000000000000000) ((√(92 : ℝ)) * x) := bmul (lowCoarseS17_hz3 hx hc) (lowCoarseS17_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS17_hz78 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B (176776695296636881 / 250000000000000000) (354364753854591503 / 500000000000000000) ((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x)) := badd (lowCoarseS17_hz76 hx hc) (lowCoarseS17_hz77 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS17_hz79 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B (499999999999999999 / 1000000000000000000) (251148757548850447 / 500000000000000000) (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2) := bsq (lowCoarseS17_hz78 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS17_hz80 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B (499999999999999999 / 125000000000000000) (251148757548850447 / 62500000000000000) ((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) := bmul (bpoint (8 : ℝ)) (lowCoarseS17_hz79 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS17_hz81 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B (7673330437300351251 / 200000000000000000) (1928302689874485209 / 50000000000000000) (((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (lowCoarseS17_hz80 hx hc) (lowCoarseS17_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS17_hz82 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B 0 (2410378362343107 / 500000000000000000) ((((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS17_hz81 hx hc) (lowCoarseS17_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS17_hz83 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B 0 (2410378362343107 / 500000000000000000) (nrs x) := by
    convert (lowCoarseS17_hz82 hx hc) using 1 <;>
      norm_num [nrs] <;> ring

theorem lowCoarseS17_hz84 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B (-4656396601252177 / 125000000000000000) (-17641804061324329 / 1000000000000000000) ((npp c) + (nrpp x)) := badd (lowCoarseS17_hz59 hx hc) (lowCoarseS17_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS17_hz85 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B (-26318557571868421 / 1000000000000000000) (-2205225507665541 / 250000000000000000) (if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) := bweaken (bfirst (lowCoarseS17_hz84 hx hc) (lowCoarseS17_hz50 hx hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem lowCoarseS17_hz86 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B (330930260307653693 / 1000000000000000000) (358923857766925529 / 1000000000000000000) ((nlam x c)^2) := bsq (lowCoarseS17_hz72 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS17_hz87 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B (347111990965104623 / 1000000000000000000) (36508489973977583 / 100000000000000000) ((nc1 x c)^2) := bsq (lowCoarseS17_hz46 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS17_hz88 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B (63491510026022417 / 100000000000000000) (652888009034895377 / 1000000000000000000) ((1 : ℝ) - ((nc1 x c)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS17_hz87 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS17_hz89 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B (199203899977545647 / 250000000000000000) (808014856939459609 / 1000000000000000000) (√((1 : ℝ) - ((nc1 x c)^2))) := bsqrt (lowCoarseS17_hz88 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS17_hz90 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B (2503270034943573531 / 1000000000000000000) (2538453538552414073 / 1000000000000000000) (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))) := bmul pi_mem (lowCoarseS17_hz89 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS17_hz91 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B (130366877030324119 / 1000000000000000000) (8961374840624617 / 62500000000000000) (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2))))) := bdiv (lowCoarseS17_hz86 hx hc) (lowCoarseS17_hz90 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS17_hz92 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B (52024159729227849 / 500000000000000000) (33640273854832927 / 250000000000000000) ((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) := badd (lowCoarseS17_hz85 hx hc) (lowCoarseS17_hz91 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS17_hz93 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B 0 (2875000000001 / 1000000000000000000) ((ne0 x)^2) := bsq (lowCoarseS17_hz68 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS17_hz94 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B (52024159729227849 / 500000000000000000) (134563970419331709 / 1000000000000000000) (((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) + ((ne0 x)^2)) := badd (lowCoarseS17_hz92 hx hc) (lowCoarseS17_hz93 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS17_hz95 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B (52024159729227849 / 500000000000000000) (139384727144017923 / 1000000000000000000) ((((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) + ((ne0 x)^2)) + (nrs x)) := badd (lowCoarseS17_hz94 hx hc) (lowCoarseS17_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS17_hz96 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B (52024159729227849 / 500000000000000000) (139384727144017923 / 1000000000000000000) (nu x c) := by
    convert (lowCoarseS17_hz95 hx hc) using 1 <;>
      norm_num [nu] <;> ring

theorem lowCoarseS17_hz97 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B (-5856073232080357 / 125000000000000000) (-27239217107949769 / 1000000000000000000) ((npp c) - (nrpp x)) := bsub (lowCoarseS17_hz59 hx hc) (lowCoarseS17_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS17_hz98 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B (-5856073232080357 / 125000000000000000) (-27239217107949769 / 1000000000000000000) (min ((npp c) - (nrpp x)) (0 : ℝ)) := bweaken (bmin (lowCoarseS17_hz97 hx hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem lowCoarseS17_hz99 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B (-8274821374866259 / 250000000000000000) (-4770554341075351 / 250000000000000000) ((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) := bmul (lowCoarseS17_hz50 hx hc) (lowCoarseS17_hz98 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS17_hz100 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B (-33102160499465037 / 1000000000000000000) (-4770554341075351 / 250000000000000000) (((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) - ((ne0 x)^2)) := bsub (lowCoarseS17_hz99 hx hc) (lowCoarseS17_hz93 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS17_hz101 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B (-37922917224151251 / 1000000000000000000) (-4770554341075351 / 250000000000000000) ((((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) - ((ne0 x)^2)) - (nrs x)) := bsub (lowCoarseS17_hz100 hx hc) (lowCoarseS17_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS17_hz102 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B (-37922917224151251 / 1000000000000000000) (-4770554341075351 / 250000000000000000) (nl x c) := by
    convert (lowCoarseS17_hz101 hx hc) using 1 <;>
      norm_num [nl] <;> ring

theorem lowCoarseS17_hz103 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B 0 (139384727144017923 / 1000000000000000000) |(nu x c)| := bweaken (babs (lowCoarseS17_hz96 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS17_hz104 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B 0 (37922917224151251 / 1000000000000000000) |(nl x c)| := bweaken (babs (lowCoarseS17_hz102 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS17_hz105 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B 0 (139384727144017923 / 1000000000000000000) (max |(nu x c)| |(nl x c)|) := bweaken (bmax (lowCoarseS17_hz103 hx hc) (lowCoarseS17_hz104 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS17_hz106 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) : B 0 (139384727144017923 / 1000000000000000000) (ns x c) := by
    convert (lowCoarseS17_hz105 hx hc) using 1 <;>
      norm_num [ns] <;> ring

theorem lowCoarseS17 {x c : ℝ}
    (hx : B 0 (1/8000) x) (hc : B (47 / 100) (12 / 25) c) :
    0 < nam x ∧ 0 ≤ ndm x c ∧ ndm x c ^ 2 ≤ 2 * nap x ^ 2 ∧ nc1 x c < 1 ∧
    0 ≤ npa c - nr1 x ∧ ne0 x ≤ (npa c - nr1 x) / nap x ∧ ns x c ≤ (1 / 5) := by
  refine ⟨lt_of_lt_of_le (by norm_num) (lowCoarseS17_hz12 hx hc).1,
    le_trans (by norm_num) (lowCoarseS17_hz38 hx hc).1, ?_,
    lt_of_le_of_lt (lowCoarseS17_hz46 hx hc).2 (by norm_num), ?_, ?_, (lowCoarseS17_hz106 hx hc).2.trans (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (lowCoarseS17_hz38 hx hc).1) (lowCoarseS17_hz38 hx hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) (lowCoarseS17_hz6 hx hc).1 2
    nlinarith only [h1,h2]
  · linarith only [(lowCoarseS17_hz55 hx hc).1,(lowCoarseS17_hz64 hx hc).2]
  · have hap : 0 < nap x := lt_of_lt_of_le (by norm_num) (lowCoarseS17_hz6 hx hc).1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul (lowCoarseS17_hz68 hx hc).2 (lowCoarseS17_hz6 hx hc).2 (le_trans (by norm_num) (lowCoarseS17_hz6 hx hc).1) (by norm_num)
    linarith only [h,(lowCoarseS17_hz55 hx hc).1,(lowCoarseS17_hz64 hx hc).2]

theorem lowCoarseS18_hz0 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B 0 (1 / 8000) x := hx

theorem lowCoarseS18_hz1 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B (12 / 25) (49 / 100) c := hc

theorem lowCoarseS18_hz2 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B (6782329983125268139 / 500000000000000000) (13564659966250536279 / 1000000000000000000) (√(184 : ℝ)) := bsqrt (bpoint (184 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS18_hz3 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS18_hz4 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B 0 (847791247890659 / 500000000000000000) ((√(184 : ℝ)) * x) := bmul (lowCoarseS18_hz2 hx hc) (lowCoarseS18_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS18_hz5 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B 1 (500847791247890659 / 500000000000000000) ((1 : ℝ) + ((√(184 : ℝ)) * x)) := badd (bpoint (1 : ℝ)) (lowCoarseS18_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS18_hz6 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B 1 (500847791247890659 / 500000000000000000) (nap x) := by
    convert (lowCoarseS18_hz5 hx hc) using 1 <;>
      norm_num [nap] <;> ring

theorem lowCoarseS18_hz7 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B 0 (1 / 64000000) (x^2) := bsq (lowCoarseS18_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS18_hz8 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B 0 (1 / 32000000) ((2 : ℝ) * (x^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS18_hz7 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS18_hz9 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B (31999999 / 32000000) 1 ((1 : ℝ) - ((2 : ℝ) * (x^2))) := bsub (bpoint (1 : ℝ)) (lowCoarseS18_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS18_hz10 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B (999999984374999877 / 1000000000000000000) 1 (√((1 : ℝ) - ((2 : ℝ) * (x^2)))) := bsqrt (lowCoarseS18_hz9 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS18_hz11 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B (998304401879218559 / 1000000000000000000) 1 ((√((1 : ℝ) - ((2 : ℝ) * (x^2)))) - ((√(184 : ℝ)) * x)) := bsub (lowCoarseS18_hz10 hx hc) (lowCoarseS18_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS18_hz12 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B (998304401879218559 / 1000000000000000000) 1 (nam x) := by
    convert (lowCoarseS18_hz11 hx hc) using 1 <;>
      norm_num [nam] <;> ring

theorem lowCoarseS18_hz13 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B (659363344522858571 / 1000000000000000000) (82420418065381437 / 125000000000000000) (kdot ((12 / 25))) := by
    constructor
    · apply bkdot_lower (q := (296374489181909579 / 500000000000000000)) (a := (535070807195192459 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (592748978363819157 / 1000000000000000000)) (a := (267535403597444707 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS18_hz14 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B (144 / 625) (144 / 625) (((12 / 25) : ℝ)^2) := bsq (bpoint ((12 / 25) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS18_hz15 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B (481 / 625) (481 / 625) ((1 : ℝ) - (((12 / 25) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS18_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS18_hz16 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B (6853660062331659 / 7812500000000000) (877268487978452353 / 1000000000000000000) (√((1 : ℝ) - (((12 / 25) : ℝ)^2))) := bsqrt (lowCoarseS18_hz15 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS18_hz17 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B (279243232561047303 / 1000000000000000000) (34905404070130913 / 125000000000000000) ((√((1 : ℝ) - (((12 / 25) : ℝ)^2))) / Real.pi) := bdiv (lowCoarseS18_hz16 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS18_hz18 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B (158247202685486057 / 500000000000000000) (316494405371064719 / 1000000000000000000) (((12 / 25) : ℝ) * (kdot ((12 / 25)))) := bmul (bpoint ((12 / 25) : ℝ)) (lowCoarseS18_hz13 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS18_hz19 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B (595737637932019417 / 1000000000000000000) (595737637932112023 / 1000000000000000000) (((√((1 : ℝ) - (((12 / 25) : ℝ)^2))) / Real.pi) + (((12 / 25) : ℝ) * (kdot ((12 / 25))))) := badd (lowCoarseS18_hz17 hx hc) (lowCoarseS18_hz18 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS18_hz20 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B (595737637932019417 / 1000000000000000000) (595737637932112023 / 1000000000000000000) (kappa ((12 / 25))) := by rw [kappa_eq]; exact (lowCoarseS18_hz19 hx hc)

theorem lowCoarseS18_hz21 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B (331501615486170743 / 500000000000000000) (331501615486221571 / 500000000000000000) (kdot ((49 / 100))) := by
    constructor
    · apply bkdot_lower (q := (117009722535288643 / 200000000000000000)) (a := (529353286930394177 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (292524306338221607 / 500000000000000000)) (a := (529353286930234499 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS18_hz22 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B (2401 / 10000) (2401 / 10000) (((49 / 100) : ℝ)^2) := bsq (bpoint ((49 / 100) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS18_hz23 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B (7599 / 10000) (7599 / 10000) ((1 : ℝ) - (((49 / 100) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS18_hz22 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS18_hz24 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B (87172243288790039 / 100000000000000000) (871722432887900391 / 1000000000000000000) (√((1 : ℝ) - (((49 / 100) : ℝ)^2))) := bsqrt (lowCoarseS18_hz23 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS18_hz25 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B (11099114735856187 / 40000000000000000) (69369467099101169 / 250000000000000000) ((√((1 : ℝ) - (((49 / 100) : ℝ)^2))) / Real.pi) := bdiv (lowCoarseS18_hz24 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS18_hz26 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B (10152236974263979 / 31250000000000000) (16243579158824857 / 50000000000000000) (((49 / 100) : ℝ) * (kdot ((49 / 100)))) := bmul (bpoint ((49 / 100) : ℝ)) (lowCoarseS18_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS18_hz27 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B (602349451572852003 / 1000000000000000000) (75293681446612727 / 125000000000000000) (((√((1 : ℝ) - (((49 / 100) : ℝ)^2))) / Real.pi) + (((49 / 100) : ℝ) * (kdot ((49 / 100))))) := badd (lowCoarseS18_hz25 hx hc) (lowCoarseS18_hz26 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS18_hz28 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B (602349451572852003 / 1000000000000000000) (75293681446612727 / 125000000000000000) (kappa ((49 / 100))) := by rw [kappa_eq]; exact (lowCoarseS18_hz27 hx hc)

theorem lowCoarseS18_hz29 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B (595737637932019417 / 1000000000000000000) (75293681446612727 / 125000000000000000) (kappa c) := bkappa (lowCoarseS18_hz1 hx hc) (by norm_num) (by norm_num) (lowCoarseS18_hz20 hx hc).1 (lowCoarseS18_hz28 hx hc).2

theorem lowCoarseS18_hz30 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B (49706318553387273 / 125000000000000000) (404262362067980583 / 1000000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (lowCoarseS18_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS18_hz31 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B (49706318553387273 / 62500000000000000) (404262362067980583 / 500000000000000000) ((2 : ℝ) * ((1 : ℝ) - (kappa c))) := bmul (bpoint (2 : ℝ)) (lowCoarseS18_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS18_hz32 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B 0 (1 / 8000000) ((8 : ℝ) * (x^2)) := bmul (bpoint (8 : ℝ)) (lowCoarseS18_hz7 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS18_hz33 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B (49706310740887273 / 62500000000000000) (404262362067980583 / 500000000000000000) (((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2))) := bsub (lowCoarseS18_hz31 hx hc) (lowCoarseS18_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS18_hz34 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B (111474560708808439 / 125000000000000000) (56198751798025713 / 62500000000000000) (√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) := bsqrt (lowCoarseS18_hz33 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS18_hz35 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B (6782329983125268139 / 250000000000000000) (13564659966250536279 / 500000000000000000) ((2 : ℝ) * (√(184 : ℝ))) := bmul (bpoint (2 : ℝ)) (lowCoarseS18_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS18_hz36 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B 0 (678232998312527 / 200000000000000000) (((2 : ℝ) * (√(184 : ℝ))) * x) := bmul (lowCoarseS18_hz35 hx hc) (lowCoarseS18_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS18_hz37 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B (888405320678904877 / 1000000000000000000) (56198751798025713 / 62500000000000000) ((√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) - (((2 : ℝ) * (√(184 : ℝ))) * x)) := bsub (lowCoarseS18_hz34 hx hc) (lowCoarseS18_hz36 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS18_hz38 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B (888405320678904877 / 1000000000000000000) (56198751798025713 / 62500000000000000) (ndm x c) := by
    convert (lowCoarseS18_hz37 hx hc) using 1 <;>
      norm_num [ndm] <;> ring

theorem lowCoarseS18_hz39 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B 1 (1003394039991562637 / 1000000000000000000) ((nap x)^2) := bsq (lowCoarseS18_hz6 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS18_hz40 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B 2 (1003394039991562637 / 500000000000000000) ((2 : ℝ) * ((nap x)^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS18_hz39 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS18_hz41 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B (789264013810587809 / 1000000000000000000) (50532795258497573 / 62500000000000000) ((ndm x c)^2) := bsq (lowCoarseS18_hz38 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS18_hz42 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B (74467204741502427 / 62500000000000000) (243504813234507493 / 200000000000000000) (((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) := bsub (lowCoarseS18_hz40 hx hc) (lowCoarseS18_hz41 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS18_hz43 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B (199322335762284863 / 200000000000000000) 1 ((nam x)^2) := bsq (lowCoarseS18_hz12 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS18_hz44 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B (199322335762284863 / 100000000000000000) 2 ((2 : ℝ) * ((nam x)^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS18_hz43 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS18_hz45 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B (74467204741502427 / 125000000000000000) (610831727170093443 / 1000000000000000000) ((((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) / ((2 : ℝ) * ((nam x)^2))) := bdiv (lowCoarseS18_hz42 hx hc) (lowCoarseS18_hz44 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS18_hz46 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B (74467204741502427 / 125000000000000000) (610831727170093443 / 1000000000000000000) (nc1 x c) := by
    convert (lowCoarseS18_hz45 hx hc) using 1 <;>
      norm_num [nc1] <;> ring

theorem lowCoarseS18_hz47 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B (659363344522858571 / 1000000000000000000) (331501615486221571 / 500000000000000000) (kdot c) := bkdot (lowCoarseS18_hz1 hx hc) (lowCoarseS18_hz13 hx hc).1 (lowCoarseS18_hz21 hx hc).2

theorem lowCoarseS18_hz48 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B (140628038350182921 / 200000000000000000) (703140191750914671 / 1000000000000000000) (kdot ((74467204741502427 / 125000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (62915973853882413 / 125000000000000000)) (a := (466306296370700689 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (503327790831059303 / 1000000000000000000)) (a := (466306296370700587 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS18_hz49 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B (354582407166698633 / 500000000000000000) (88645601791674661 / 125000000000000000) (kdot ((610831727170093443 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (24576137621871213 / 50000000000000000)) (a := (456842841347811341 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (491522752437424259 / 1000000000000000000)) (a := (114210710336952827 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS18_hz50 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B (140628038350182921 / 200000000000000000) (88645601791674661 / 125000000000000000) (kdot (nc1 x c)) := bkdot (lowCoarseS18_hz46 hx hc) (lowCoarseS18_hz48 hx hc).1 (lowCoarseS18_hz49 hx hc).2

theorem lowCoarseS18_hz51 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B (144 / 625) (2401 / 10000) (c^2) := bsq (lowCoarseS18_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS18_hz52 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B (7599 / 10000) (481 / 625) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS18_hz51 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS18_hz53 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B (87172243288790039 / 100000000000000000) (877268487978452353 / 1000000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (lowCoarseS18_hz52 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS18_hz54 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B (574781818844569123 / 1000000000000000000) (290815920980011903 / 500000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (lowCoarseS18_hz53 hx hc) (lowCoarseS18_hz47 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS18_hz55 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B (574781818844569123 / 1000000000000000000) (290815920980011903 / 500000000000000000) (npa c) := by
    convert (lowCoarseS18_hz54 hx hc) using 1 <;>
      norm_num [npa] <;> ring

theorem lowCoarseS18_hz56 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B (11099114735856187 / 40000000000000000) (34905404070130913 / 125000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (lowCoarseS18_hz53 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS18_hz57 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B (158247202685486057 / 500000000000000000) (16243579158824857 / 50000000000000000) (c * (kdot c)) := bmul (lowCoarseS18_hz1 hx hc) (lowCoarseS18_hz47 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS18_hz58 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B (-9478742956018493 / 200000000000000000) (-3725117280992481 / 100000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (lowCoarseS18_hz56 hx hc) (lowCoarseS18_hz57 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS18_hz59 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B (-9478742956018493 / 200000000000000000) (-3725117280992481 / 100000000000000000) (npp c) := by
    convert (lowCoarseS18_hz58 hx hc) using 1 <;>
      norm_num [npp] <;> ring

theorem lowCoarseS18_hz60 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B 0 (23 / 4000) ((46 : ℝ) * x) := bmul (bpoint (46 : ℝ)) (lowCoarseS18_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS18_hz61 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B (9591663046625439083 / 1000000000000000000) (2399353261656359771 / 250000000000000000) ((√(92 : ℝ)) + ((46 : ℝ) * x)) := badd (lowCoarseS18_hz3 hx hc) (lowCoarseS18_hz60 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS18_hz62 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B (28774989139876317249 / 250000000000000000) (7198059784969079313 / 62500000000000000) ((12 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (bpoint (12 : ℝ)) (lowCoarseS18_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS18_hz63 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B 0 (14396119569938159 / 1000000000000000000) (((12 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS18_hz62 hx hc) (lowCoarseS18_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS18_hz64 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B 0 (14396119569938159 / 1000000000000000000) (nr1 x) := by
    convert (lowCoarseS18_hz63 hx hc) using 1 <;>
      norm_num [nr1] <;> ring

theorem lowCoarseS18_hz65 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B (9591663046625439083 / 125000000000000000) (2399353261656359771 / 31250000000000000) ((8 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (bpoint (8 : ℝ)) (lowCoarseS18_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS18_hz66 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B 0 (59983831541409 / 6250000000000000) (((8 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS18_hz65 hx hc) (lowCoarseS18_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS18_hz67 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B 0 (59983831541409 / 6250000000000000) (nrpp x) := by
    convert (lowCoarseS18_hz66 hx hc) using 1 <;>
      norm_num [nrpp] <;> ring

theorem lowCoarseS18_hz68 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B 0 (847791247890659 / 500000000000000000) (ne0 x) := by
    convert (lowCoarseS18_hz4 hx hc) using 1 <;>
      norm_num [ne0] <;> ring

theorem lowCoarseS18_hz69 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B (574781818844569123 / 1000000000000000000) (119205592305992393 / 200000000000000000) ((npa c) + (nr1 x)) := badd (lowCoarseS18_hz55 hx hc) (lowCoarseS18_hz64 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS18_hz70 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B (574781818844569123 / 1000000000000000000) (597040301943968943 / 1000000000000000000) (((npa c) + (nr1 x)) / (nam x)) := bdiv (lowCoarseS18_hz69 hx hc) (lowCoarseS18_hz12 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS18_hz71 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B (574781818844569123 / 1000000000000000000) (598735884439750261 / 1000000000000000000) ((((npa c) + (nr1 x)) / (nam x)) + (ne0 x)) := badd (lowCoarseS18_hz70 hx hc) (lowCoarseS18_hz68 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS18_hz72 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B (574781818844569123 / 1000000000000000000) (598735884439750261 / 1000000000000000000) (nlam x c) := by
    convert (lowCoarseS18_hz71 hx hc) using 1 <;>
      norm_num [nlam] <;> ring

theorem lowCoarseS18_hz73 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS18_hz74 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B 0 (59947894041409 / 100000000000000000) ((√(23 : ℝ)) * x) := bmul (lowCoarseS18_hz73 hx hc) (lowCoarseS18_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS18_hz75 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B (1 / 2) (50059947894041409 / 100000000000000000) (((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)) := badd (bpoint ((1 / 2) : ℝ)) (lowCoarseS18_hz74 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS18_hz76 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B (176776695296636881 / 250000000000000000) (353765274914177413 / 500000000000000000) (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) := bsqrt (lowCoarseS18_hz75 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS18_hz77 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B 0 (59947894041409 / 50000000000000000) ((√(92 : ℝ)) * x) := bmul (lowCoarseS18_hz3 hx hc) (lowCoarseS18_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS18_hz78 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B (176776695296636881 / 250000000000000000) (354364753854591503 / 500000000000000000) ((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x)) := badd (lowCoarseS18_hz76 hx hc) (lowCoarseS18_hz77 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS18_hz79 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B (499999999999999999 / 1000000000000000000) (251148757548850447 / 500000000000000000) (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2) := bsq (lowCoarseS18_hz78 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS18_hz80 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B (499999999999999999 / 125000000000000000) (251148757548850447 / 62500000000000000) ((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) := bmul (bpoint (8 : ℝ)) (lowCoarseS18_hz79 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS18_hz81 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B (7673330437300351251 / 200000000000000000) (1928302689874485209 / 50000000000000000) (((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (lowCoarseS18_hz80 hx hc) (lowCoarseS18_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS18_hz82 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B 0 (2410378362343107 / 500000000000000000) ((((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS18_hz81 hx hc) (lowCoarseS18_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS18_hz83 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B 0 (2410378362343107 / 500000000000000000) (nrs x) := by
    convert (lowCoarseS18_hz82 hx hc) using 1 <;>
      norm_num [nrs] <;> ring

theorem lowCoarseS18_hz84 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B (-9478742956018493 / 200000000000000000) (-2765375976329937 / 100000000000000000) ((npp c) + (nrpp x)) := badd (lowCoarseS18_hz59 hx hc) (lowCoarseS18_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS18_hz85 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B (-1680497747129713 / 50000000000000000) (-2765375976329937 / 200000000000000000) (if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) := bweaken (bfirst (lowCoarseS18_hz84 hx hc) (lowCoarseS18_hz50 hx hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem lowCoarseS18_hz86 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B (82593534818567769 / 250000000000000000) (358484659315849979 / 1000000000000000000) ((nlam x c)^2) := bsq (lowCoarseS18_hz72 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS18_hz87 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B (177451666624410929 / 500000000000000000) (373115398917599473 / 1000000000000000000) ((nc1 x c)^2) := bsq (lowCoarseS18_hz46 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS18_hz88 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B (626884601082400527 / 1000000000000000000) (322548333375589071 / 500000000000000000) ((1 : ℝ) - ((nc1 x c)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS18_hz87 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS18_hz89 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B (1266816710803479 / 1600000000000000) (401589550023148057 / 500000000000000000) (√((1 : ℝ) - ((nc1 x c)^2))) := bsqrt (lowCoarseS18_hz88 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS18_hz90 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B (621847198766405513 / 250000000000000000) (504652312044461087 / 200000000000000000) (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))) := bmul pi_mem (lowCoarseS18_hz89 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS18_hz91 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B (1636642354494773 / 12500000000000000) (144120878902002319 / 1000000000000000000) (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2))))) := bdiv (lowCoarseS18_hz86 hx hc) (lowCoarseS18_hz90 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS18_hz92 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B (4866071670849379 / 50000000000000000) (65146999510176317 / 500000000000000000) ((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) := badd (lowCoarseS18_hz85 hx hc) (lowCoarseS18_hz91 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS18_hz93 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B 0 (2875000000001 / 1000000000000000000) ((ne0 x)^2) := bsq (lowCoarseS18_hz68 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS18_hz94 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B (4866071670849379 / 50000000000000000) (26059374804070527 / 200000000000000000) (((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) + ((ne0 x)^2)) := badd (lowCoarseS18_hz92 hx hc) (lowCoarseS18_hz93 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS18_hz95 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B (4866071670849379 / 50000000000000000) (135117630745038849 / 1000000000000000000) ((((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) + ((ne0 x)^2)) + (nrs x)) := badd (lowCoarseS18_hz94 hx hc) (lowCoarseS18_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS18_hz96 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B (4866071670849379 / 50000000000000000) (135117630745038849 / 1000000000000000000) (nu x c) := by
    convert (lowCoarseS18_hz95 hx hc) using 1 <;>
      norm_num [nu] <;> ring

theorem lowCoarseS18_hz97 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B (-11398225565343581 / 200000000000000000) (-3725117280992481 / 100000000000000000) ((npp c) - (nrpp x)) := bsub (lowCoarseS18_hz59 hx hc) (lowCoarseS18_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS18_hz98 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B (-11398225565343581 / 200000000000000000) (-3725117280992481 / 100000000000000000) (min ((npp c) - (nrpp x)) (0 : ℝ)) := bweaken (bmin (lowCoarseS18_hz97 hx hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem lowCoarseS18_hz99 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B (-8083220516777063 / 200000000000000000) (-26192796792516987 / 1000000000000000000) ((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) := bmul (lowCoarseS18_hz50 hx hc) (lowCoarseS18_hz98 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS18_hz100 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B (-10104744395971329 / 250000000000000000) (-26192796792516987 / 1000000000000000000) (((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) - ((ne0 x)^2)) := bsub (lowCoarseS18_hz99 hx hc) (lowCoarseS18_hz93 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS18_hz101 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B (-4523973430857153 / 100000000000000000) (-26192796792516987 / 1000000000000000000) ((((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) - ((ne0 x)^2)) - (nrs x)) := bsub (lowCoarseS18_hz100 hx hc) (lowCoarseS18_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS18_hz102 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B (-4523973430857153 / 100000000000000000) (-26192796792516987 / 1000000000000000000) (nl x c) := by
    convert (lowCoarseS18_hz101 hx hc) using 1 <;>
      norm_num [nl] <;> ring

theorem lowCoarseS18_hz103 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B 0 (135117630745038849 / 1000000000000000000) |(nu x c)| := bweaken (babs (lowCoarseS18_hz96 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS18_hz104 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B 0 (4523973430857153 / 100000000000000000) |(nl x c)| := bweaken (babs (lowCoarseS18_hz102 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS18_hz105 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B 0 (135117630745038849 / 1000000000000000000) (max |(nu x c)| |(nl x c)|) := bweaken (bmax (lowCoarseS18_hz103 hx hc) (lowCoarseS18_hz104 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS18_hz106 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) : B 0 (135117630745038849 / 1000000000000000000) (ns x c) := by
    convert (lowCoarseS18_hz105 hx hc) using 1 <;>
      norm_num [ns] <;> ring

theorem lowCoarseS18 {x c : ℝ}
    (hx : B 0 (1/8000) x) (hc : B (12 / 25) (49 / 100) c) :
    0 < nam x ∧ 0 ≤ ndm x c ∧ ndm x c ^ 2 ≤ 2 * nap x ^ 2 ∧ nc1 x c < 1 ∧
    0 ≤ npa c - nr1 x ∧ ne0 x ≤ (npa c - nr1 x) / nap x ∧ ns x c ≤ (1 / 5) := by
  refine ⟨lt_of_lt_of_le (by norm_num) (lowCoarseS18_hz12 hx hc).1,
    le_trans (by norm_num) (lowCoarseS18_hz38 hx hc).1, ?_,
    lt_of_le_of_lt (lowCoarseS18_hz46 hx hc).2 (by norm_num), ?_, ?_, (lowCoarseS18_hz106 hx hc).2.trans (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (lowCoarseS18_hz38 hx hc).1) (lowCoarseS18_hz38 hx hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) (lowCoarseS18_hz6 hx hc).1 2
    nlinarith only [h1,h2]
  · linarith only [(lowCoarseS18_hz55 hx hc).1,(lowCoarseS18_hz64 hx hc).2]
  · have hap : 0 < nap x := lt_of_lt_of_le (by norm_num) (lowCoarseS18_hz6 hx hc).1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul (lowCoarseS18_hz68 hx hc).2 (lowCoarseS18_hz6 hx hc).2 (le_trans (by norm_num) (lowCoarseS18_hz6 hx hc).1) (by norm_num)
    linarith only [h,(lowCoarseS18_hz55 hx hc).1,(lowCoarseS18_hz64 hx hc).2]

theorem lowCoarseS19_hz0 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B 0 (1 / 8000) x := hx

theorem lowCoarseS19_hz1 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B (49 / 100) (1 / 2) c := hc

theorem lowCoarseS19_hz2 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B (6782329983125268139 / 500000000000000000) (13564659966250536279 / 1000000000000000000) (√(184 : ℝ)) := bsqrt (bpoint (184 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS19_hz3 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS19_hz4 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B 0 (847791247890659 / 500000000000000000) ((√(184 : ℝ)) * x) := bmul (lowCoarseS19_hz2 hx hc) (lowCoarseS19_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS19_hz5 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B 1 (500847791247890659 / 500000000000000000) ((1 : ℝ) + ((√(184 : ℝ)) * x)) := badd (bpoint (1 : ℝ)) (lowCoarseS19_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS19_hz6 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B 1 (500847791247890659 / 500000000000000000) (nap x) := by
    convert (lowCoarseS19_hz5 hx hc) using 1 <;>
      norm_num [nap] <;> ring

theorem lowCoarseS19_hz7 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B 0 (1 / 64000000) (x^2) := bsq (lowCoarseS19_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS19_hz8 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B 0 (1 / 32000000) ((2 : ℝ) * (x^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS19_hz7 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS19_hz9 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B (31999999 / 32000000) 1 ((1 : ℝ) - ((2 : ℝ) * (x^2))) := bsub (bpoint (1 : ℝ)) (lowCoarseS19_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS19_hz10 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B (999999984374999877 / 1000000000000000000) 1 (√((1 : ℝ) - ((2 : ℝ) * (x^2)))) := bsqrt (lowCoarseS19_hz9 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS19_hz11 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B (998304401879218559 / 1000000000000000000) 1 ((√((1 : ℝ) - ((2 : ℝ) * (x^2)))) - ((√(184 : ℝ)) * x)) := bsub (lowCoarseS19_hz10 hx hc) (lowCoarseS19_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS19_hz12 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B (998304401879218559 / 1000000000000000000) 1 (nam x) := by
    convert (lowCoarseS19_hz11 hx hc) using 1 <;>
      norm_num [nam] <;> ring

theorem lowCoarseS19_hz13 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B (331501615486170743 / 500000000000000000) (331501615486221571 / 500000000000000000) (kdot ((49 / 100))) := by
    constructor
    · apply bkdot_lower (q := (117009722535288643 / 200000000000000000)) (a := (529353286930394177 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (292524306338221607 / 500000000000000000)) (a := (529353286930234499 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS19_hz14 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B (2401 / 10000) (2401 / 10000) (((49 / 100) : ℝ)^2) := bsq (bpoint ((49 / 100) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS19_hz15 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B (7599 / 10000) (7599 / 10000) ((1 : ℝ) - (((49 / 100) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS19_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS19_hz16 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B (87172243288790039 / 100000000000000000) (871722432887900391 / 1000000000000000000) (√((1 : ℝ) - (((49 / 100) : ℝ)^2))) := bsqrt (lowCoarseS19_hz15 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS19_hz17 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B (11099114735856187 / 40000000000000000) (69369467099101169 / 250000000000000000) ((√((1 : ℝ) - (((49 / 100) : ℝ)^2))) / Real.pi) := bdiv (lowCoarseS19_hz16 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS19_hz18 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B (10152236974263979 / 31250000000000000) (16243579158824857 / 50000000000000000) (((49 / 100) : ℝ) * (kdot ((49 / 100)))) := bmul (bpoint ((49 / 100) : ℝ)) (lowCoarseS19_hz13 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS19_hz19 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B (602349451572852003 / 1000000000000000000) (75293681446612727 / 125000000000000000) (((√((1 : ℝ) - (((49 / 100) : ℝ)^2))) / Real.pi) + (((49 / 100) : ℝ) * (kdot ((49 / 100))))) := badd (lowCoarseS19_hz17 hx hc) (lowCoarseS19_hz18 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS19_hz20 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B (602349451572852003 / 1000000000000000000) (75293681446612727 / 125000000000000000) (kappa ((49 / 100))) := by rw [kappa_eq]; exact (lowCoarseS19_hz19 hx hc)

theorem lowCoarseS19_hz21 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B (26666666666666409 / 40000000000000000) (133333333333342669 / 200000000000000000) (kdot ((1 / 2))) := by
    constructor
    · apply bkdot_lower (q := (115470053837925153 / 200000000000000000)) (a := (523598775598308991 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (144337567297406441 / 250000000000000000)) (a := (523598775598225551 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS19_hz22 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B (1 / 4) (1 / 4) (((1 / 2) : ℝ)^2) := bsq (bpoint ((1 / 2) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS19_hz23 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B (3 / 4) (3 / 4) ((1 : ℝ) - (((1 / 2) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS19_hz22 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS19_hz24 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B (433012701892219323 / 500000000000000000) (866025403784438647 / 1000000000000000000) (√((1 : ℝ) - (((1 / 2) : ℝ)^2))) := bsqrt (lowCoarseS19_hz23 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS19_hz25 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B (34458055963862003 / 125000000000000000) (11026577908435841 / 40000000000000000) ((√((1 : ℝ) - (((1 / 2) : ℝ)^2))) / Real.pi) := bdiv (lowCoarseS19_hz24 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS19_hz26 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B (5208333333333283 / 15625000000000000) (333333333333356673 / 1000000000000000000) (((1 / 2) : ℝ) * (kdot ((1 / 2)))) := bmul (bpoint ((1 / 2) : ℝ)) (lowCoarseS19_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS19_hz27 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B (76124722630528267 / 125000000000000000) (304498890522126349 / 500000000000000000) (((√((1 : ℝ) - (((1 / 2) : ℝ)^2))) / Real.pi) + (((1 / 2) : ℝ) * (kdot ((1 / 2))))) := badd (lowCoarseS19_hz25 hx hc) (lowCoarseS19_hz26 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS19_hz28 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B (76124722630528267 / 125000000000000000) (304498890522126349 / 500000000000000000) (kappa ((1 / 2))) := by rw [kappa_eq]; exact (lowCoarseS19_hz27 hx hc)

theorem lowCoarseS19_hz29 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B (602349451572852003 / 1000000000000000000) (304498890522126349 / 500000000000000000) (kappa c) := bkappa (lowCoarseS19_hz1 hx hc) (by norm_num) (by norm_num) (lowCoarseS19_hz20 hx hc).1 (lowCoarseS19_hz28 hx hc).2

theorem lowCoarseS19_hz30 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B (195501109477873651 / 500000000000000000) (397650548427147997 / 1000000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (lowCoarseS19_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS19_hz31 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B (195501109477873651 / 250000000000000000) (397650548427147997 / 500000000000000000) ((2 : ℝ) * ((1 : ℝ) - (kappa c))) := bmul (bpoint (2 : ℝ)) (lowCoarseS19_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS19_hz32 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B 0 (1 / 8000000) ((8 : ℝ) * (x^2)) := bmul (bpoint (8 : ℝ)) (lowCoarseS19_hz7 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS19_hz33 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B (195501078227873651 / 250000000000000000) (397650548427147997 / 500000000000000000) (((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2))) := bsub (lowCoarseS19_hz31 hx hc) (lowCoarseS19_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS19_hz34 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B (884310077354936967 / 1000000000000000000) (891796555753775041 / 1000000000000000000) (√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) := bsqrt (lowCoarseS19_hz33 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS19_hz35 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B (6782329983125268139 / 250000000000000000) (13564659966250536279 / 500000000000000000) ((2 : ℝ) * (√(184 : ℝ))) := bmul (bpoint (2 : ℝ)) (lowCoarseS19_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS19_hz36 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B 0 (678232998312527 / 200000000000000000) (((2 : ℝ) * (√(184 : ℝ))) * x) := bmul (lowCoarseS19_hz35 hx hc) (lowCoarseS19_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS19_hz37 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B (220229728090843583 / 250000000000000000) (891796555753775041 / 1000000000000000000) ((√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) - (((2 : ℝ) * (√(184 : ℝ))) * x)) := bsub (lowCoarseS19_hz34 hx hc) (lowCoarseS19_hz36 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS19_hz38 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B (220229728090843583 / 250000000000000000) (891796555753775041 / 1000000000000000000) (ndm x c) := by
    convert (lowCoarseS19_hz37 hx hc) using 1 <;>
      norm_num [ndm] <;> ring

theorem lowCoarseS19_hz39 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B 1 (1003394039991562637 / 1000000000000000000) ((nap x)^2) := bsq (lowCoarseS19_hz6 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS19_hz40 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B 2 (1003394039991562637 / 500000000000000000) ((2 : ℝ) * ((nap x)^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS19_hz39 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS19_hz41 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B (388009065079735193 / 500000000000000000) (198825274213573999 / 250000000000000000) ((ndm x c)^2) := bsq (lowCoarseS19_hz38 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS19_hz42 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B (301174725786426001 / 250000000000000000) (153846243727956861 / 125000000000000000) (((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) := bsub (lowCoarseS19_hz40 hx hc) (lowCoarseS19_hz41 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS19_hz43 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B (199322335762284863 / 200000000000000000) 1 ((nam x)^2) := bsq (lowCoarseS19_hz12 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS19_hz44 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B (199322335762284863 / 100000000000000000) 2 ((2 : ℝ) * ((nam x)^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS19_hz43 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS19_hz45 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B (301174725786426001 / 500000000000000000) (154369296486106257 / 250000000000000000) ((((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) / ((2 : ℝ) * ((nam x)^2))) := bdiv (lowCoarseS19_hz42 hx hc) (lowCoarseS19_hz44 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS19_hz46 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B (301174725786426001 / 500000000000000000) (154369296486106257 / 250000000000000000) (nc1 x c) := by
    convert (lowCoarseS19_hz45 hx hc) using 1 <;>
      norm_num [nc1] <;> ring

theorem lowCoarseS19_hz47 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B (331501615486170743 / 500000000000000000) (133333333333342669 / 200000000000000000) (kdot c) := bkdot (lowCoarseS19_hz1 hx hc) (lowCoarseS19_hz13 hx hc).1 (lowCoarseS19_hz21 hx hc).2

theorem lowCoarseS19_hz48 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B (705768614921056909 / 1000000000000000000) (14115372298421139 / 20000000000000000) (kdot ((301174725786426001 / 500000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (3891904771018149 / 7812500000000000)) (a := (722152467046529 / 1562500000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (498163810690323071 / 1000000000000000000)) (a := (462177578909778497 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS19_hz49 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B (711845213170917587 / 1000000000000000000) (889806516463647 / 1250000000000000) (kdot ((154369296486106257 / 250000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (486305956594718961 / 1000000000000000000)) (a := (45263248069948911 / 100000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (6078824457433987 / 12500000000000000)) (a := (45263248069948909 / 100000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS19_hz50 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B (705768614921056909 / 1000000000000000000) (889806516463647 / 1250000000000000) (kdot (nc1 x c)) := bkdot (lowCoarseS19_hz46 hx hc) (lowCoarseS19_hz48 hx hc).1 (lowCoarseS19_hz49 hx hc).2

theorem lowCoarseS19_hz51 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B (2401 / 10000) (1 / 4) (c^2) := bsq (lowCoarseS19_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS19_hz52 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B (3 / 4) (7599 / 10000) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS19_hz51 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS19_hz53 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B (433012701892219323 / 500000000000000000) (871722432887900391 / 1000000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (lowCoarseS19_hz52 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS19_hz54 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B (287088820406604737 / 500000000000000000) (116229657718394857 / 200000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (lowCoarseS19_hz53 hx hc) (lowCoarseS19_hz47 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS19_hz55 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B (287088820406604737 / 500000000000000000) (116229657718394857 / 200000000000000000) (npa c) := by
    convert (lowCoarseS19_hz54 hx hc) using 1 <;>
      norm_num [npa] <;> ring

theorem lowCoarseS19_hz56 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B (34458055963862003 / 125000000000000000) (69369467099101169 / 250000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (lowCoarseS19_hz53 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS19_hz57 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B (10152236974263979 / 31250000000000000) (333333333333356673 / 1000000000000000000) (c * (kdot c)) := bmul (lowCoarseS19_hz1 hx hc) (lowCoarseS19_hz47 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS19_hz58 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B (-57668885622460649 / 1000000000000000000) (-11848428695010663 / 250000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (lowCoarseS19_hz56 hx hc) (lowCoarseS19_hz57 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS19_hz59 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B (-57668885622460649 / 1000000000000000000) (-11848428695010663 / 250000000000000000) (npp c) := by
    convert (lowCoarseS19_hz58 hx hc) using 1 <;>
      norm_num [npp] <;> ring

theorem lowCoarseS19_hz60 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B 0 (23 / 4000) ((46 : ℝ) * x) := bmul (bpoint (46 : ℝ)) (lowCoarseS19_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS19_hz61 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B (9591663046625439083 / 1000000000000000000) (2399353261656359771 / 250000000000000000) ((√(92 : ℝ)) + ((46 : ℝ) * x)) := badd (lowCoarseS19_hz3 hx hc) (lowCoarseS19_hz60 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS19_hz62 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B (28774989139876317249 / 250000000000000000) (7198059784969079313 / 62500000000000000) ((12 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (bpoint (12 : ℝ)) (lowCoarseS19_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS19_hz63 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B 0 (14396119569938159 / 1000000000000000000) (((12 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS19_hz62 hx hc) (lowCoarseS19_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS19_hz64 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B 0 (14396119569938159 / 1000000000000000000) (nr1 x) := by
    convert (lowCoarseS19_hz63 hx hc) using 1 <;>
      norm_num [nr1] <;> ring

theorem lowCoarseS19_hz65 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B (9591663046625439083 / 125000000000000000) (2399353261656359771 / 31250000000000000) ((8 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (bpoint (8 : ℝ)) (lowCoarseS19_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS19_hz66 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B 0 (59983831541409 / 6250000000000000) (((8 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS19_hz65 hx hc) (lowCoarseS19_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS19_hz67 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B 0 (59983831541409 / 6250000000000000) (nrpp x) := by
    convert (lowCoarseS19_hz66 hx hc) using 1 <;>
      norm_num [nrpp] <;> ring

theorem lowCoarseS19_hz68 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B 0 (847791247890659 / 500000000000000000) (ne0 x) := by
    convert (lowCoarseS19_hz4 hx hc) using 1 <;>
      norm_num [ne0] <;> ring

theorem lowCoarseS19_hz69 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B (287088820406604737 / 500000000000000000) (148886102040478111 / 250000000000000000) ((npa c) + (nr1 x)) := badd (lowCoarseS19_hz55 hx hc) (lowCoarseS19_hz64 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS19_hz70 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B (287088820406604737 / 500000000000000000) (59655592727113441 / 100000000000000000) (((npa c) + (nr1 x)) / (nam x)) := bdiv (lowCoarseS19_hz69 hx hc) (lowCoarseS19_hz12 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS19_hz71 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B (287088820406604737 / 500000000000000000) (37390719360432233 / 62500000000000000) ((((npa c) + (nr1 x)) / (nam x)) + (ne0 x)) := badd (lowCoarseS19_hz70 hx hc) (lowCoarseS19_hz68 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS19_hz72 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B (287088820406604737 / 500000000000000000) (37390719360432233 / 62500000000000000) (nlam x c) := by
    convert (lowCoarseS19_hz71 hx hc) using 1 <;>
      norm_num [nlam] <;> ring

theorem lowCoarseS19_hz73 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS19_hz74 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B 0 (59947894041409 / 100000000000000000) ((√(23 : ℝ)) * x) := bmul (lowCoarseS19_hz73 hx hc) (lowCoarseS19_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS19_hz75 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B (1 / 2) (50059947894041409 / 100000000000000000) (((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)) := badd (bpoint ((1 / 2) : ℝ)) (lowCoarseS19_hz74 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS19_hz76 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B (176776695296636881 / 250000000000000000) (353765274914177413 / 500000000000000000) (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) := bsqrt (lowCoarseS19_hz75 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS19_hz77 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B 0 (59947894041409 / 50000000000000000) ((√(92 : ℝ)) * x) := bmul (lowCoarseS19_hz3 hx hc) (lowCoarseS19_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS19_hz78 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B (176776695296636881 / 250000000000000000) (354364753854591503 / 500000000000000000) ((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x)) := badd (lowCoarseS19_hz76 hx hc) (lowCoarseS19_hz77 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS19_hz79 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B (499999999999999999 / 1000000000000000000) (251148757548850447 / 500000000000000000) (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2) := bsq (lowCoarseS19_hz78 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS19_hz80 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B (499999999999999999 / 125000000000000000) (251148757548850447 / 62500000000000000) ((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) := bmul (bpoint (8 : ℝ)) (lowCoarseS19_hz79 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS19_hz81 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B (7673330437300351251 / 200000000000000000) (1928302689874485209 / 50000000000000000) (((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (lowCoarseS19_hz80 hx hc) (lowCoarseS19_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS19_hz82 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B 0 (2410378362343107 / 500000000000000000) ((((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS19_hz81 hx hc) (lowCoarseS19_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS19_hz83 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B 0 (2410378362343107 / 500000000000000000) (nrs x) := by
    convert (lowCoarseS19_hz82 hx hc) using 1 <;>
      norm_num [nrs] <;> ring

theorem lowCoarseS19_hz84 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B (-57668885622460649 / 1000000000000000000) (-9449075433354303 / 250000000000000000) ((npp c) + (nrpp x)) := badd (lowCoarseS19_hz59 hx hc) (lowCoarseS19_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS19_hz85 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B (-20525660089624883 / 500000000000000000) (-9449075433354303 / 500000000000000000) (if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) := bweaken (bfirst (lowCoarseS19_hz84 hx hc) (lowCoarseS19_hz50 hx hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem lowCoarseS19_hz86 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B (329679963209822993 / 1000000000000000000) (71580973787678813 / 200000000000000000) ((nlam x c)^2) := bsq (lowCoarseS19_hz72 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS19_hz87 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B (362824861810115579 / 1000000000000000000) (190639037580923021 / 500000000000000000) ((nc1 x c)^2) := bsq (lowCoarseS19_hz46 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS19_hz88 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B (309360962419076979 / 500000000000000000) (637175138189884421 / 1000000000000000000) ((1 : ℝ) - ((nc1 x c)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS19_hz87 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS19_hz89 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B (786588790180837727 / 1000000000000000000) (798232508853081241 / 1000000000000000000) (√((1 : ℝ) - ((nc1 x c)^2))) := bsqrt (lowCoarseS19_hz88 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS19_hz90 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B (1235570782314101547 / 500000000000000000) (125386069283469481 / 50000000000000000) (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))) := bmul pi_mem (lowCoarseS19_hz89 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS19_hz91 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B (16433243197081733 / 125000000000000000) (72416909266030421 / 500000000000000000) (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2))))) := bdiv (lowCoarseS19_hz86 hx hc) (lowCoarseS19_hz90 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS19_hz92 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B (45207312698702049 / 500000000000000000) (31483916916338059 / 250000000000000000) ((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) := badd (lowCoarseS19_hz85 hx hc) (lowCoarseS19_hz91 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS19_hz93 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B 0 (2875000000001 / 1000000000000000000) ((ne0 x)^2) := bsq (lowCoarseS19_hz68 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS19_hz94 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B (45207312698702049 / 500000000000000000) (125938542665352237 / 1000000000000000000) (((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) + ((ne0 x)^2)) := badd (lowCoarseS19_hz92 hx hc) (lowCoarseS19_hz93 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS19_hz95 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B (45207312698702049 / 500000000000000000) (130759299390038451 / 1000000000000000000) ((((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) + ((ne0 x)^2)) + (nrs x)) := badd (lowCoarseS19_hz94 hx hc) (lowCoarseS19_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS19_hz96 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B (45207312698702049 / 500000000000000000) (130759299390038451 / 1000000000000000000) (nu x c) := by
    convert (lowCoarseS19_hz95 hx hc) using 1 <;>
      norm_num [nu] <;> ring

theorem lowCoarseS19_hz97 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B (-67266298669086089 / 1000000000000000000) (-11848428695010663 / 250000000000000000) ((npp c) - (nrpp x)) := bsub (lowCoarseS19_hz59 hx hc) (lowCoarseS19_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS19_hz98 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B (-67266298669086089 / 1000000000000000000) (-11848428695010663 / 250000000000000000) (min ((npp c) - (nrpp x)) (0 : ℝ)) := bweaken (bmin (lowCoarseS19_hz97 hx hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem lowCoarseS19_hz99 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B (-23941596357657099 / 500000000000000000) (-1337959857450973 / 40000000000000000) ((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) := bmul (lowCoarseS19_hz50 hx hc) (lowCoarseS19_hz98 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS19_hz100 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B (-47886067715314199 / 1000000000000000000) (-1337959857450973 / 40000000000000000) (((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) - ((ne0 x)^2)) := bsub (lowCoarseS19_hz99 hx hc) (lowCoarseS19_hz93 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS19_hz101 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B (-52706824440000413 / 1000000000000000000) (-1337959857450973 / 40000000000000000) ((((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) - ((ne0 x)^2)) - (nrs x)) := bsub (lowCoarseS19_hz100 hx hc) (lowCoarseS19_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS19_hz102 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B (-52706824440000413 / 1000000000000000000) (-1337959857450973 / 40000000000000000) (nl x c) := by
    convert (lowCoarseS19_hz101 hx hc) using 1 <;>
      norm_num [nl] <;> ring

theorem lowCoarseS19_hz103 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B 0 (130759299390038451 / 1000000000000000000) |(nu x c)| := bweaken (babs (lowCoarseS19_hz96 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS19_hz104 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B 0 (52706824440000413 / 1000000000000000000) |(nl x c)| := bweaken (babs (lowCoarseS19_hz102 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS19_hz105 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B 0 (130759299390038451 / 1000000000000000000) (max |(nu x c)| |(nl x c)|) := bweaken (bmax (lowCoarseS19_hz103 hx hc) (lowCoarseS19_hz104 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS19_hz106 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) : B 0 (130759299390038451 / 1000000000000000000) (ns x c) := by
    convert (lowCoarseS19_hz105 hx hc) using 1 <;>
      norm_num [ns] <;> ring

theorem lowCoarseS19 {x c : ℝ}
    (hx : B 0 (1/8000) x) (hc : B (49 / 100) (1 / 2) c) :
    0 < nam x ∧ 0 ≤ ndm x c ∧ ndm x c ^ 2 ≤ 2 * nap x ^ 2 ∧ nc1 x c < 1 ∧
    0 ≤ npa c - nr1 x ∧ ne0 x ≤ (npa c - nr1 x) / nap x ∧ ns x c ≤ (1 / 5) := by
  refine ⟨lt_of_lt_of_le (by norm_num) (lowCoarseS19_hz12 hx hc).1,
    le_trans (by norm_num) (lowCoarseS19_hz38 hx hc).1, ?_,
    lt_of_le_of_lt (lowCoarseS19_hz46 hx hc).2 (by norm_num), ?_, ?_, (lowCoarseS19_hz106 hx hc).2.trans (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (lowCoarseS19_hz38 hx hc).1) (lowCoarseS19_hz38 hx hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) (lowCoarseS19_hz6 hx hc).1 2
    nlinarith only [h1,h2]
  · linarith only [(lowCoarseS19_hz55 hx hc).1,(lowCoarseS19_hz64 hx hc).2]
  · have hap : 0 < nap x := lt_of_lt_of_le (by norm_num) (lowCoarseS19_hz6 hx hc).1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul (lowCoarseS19_hz68 hx hc).2 (lowCoarseS19_hz6 hx hc).2 (le_trans (by norm_num) (lowCoarseS19_hz6 hx hc).1) (by norm_num)
    linarith only [h,(lowCoarseS19_hz55 hx hc).1,(lowCoarseS19_hz64 hx hc).2]

theorem lowCoarseS20_hz0 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B 0 (1 / 8000) x := hx

theorem lowCoarseS20_hz1 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B (1 / 2) (51 / 100) c := hc

theorem lowCoarseS20_hz2 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B (6782329983125268139 / 500000000000000000) (13564659966250536279 / 1000000000000000000) (√(184 : ℝ)) := bsqrt (bpoint (184 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS20_hz3 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS20_hz4 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B 0 (847791247890659 / 500000000000000000) ((√(184 : ℝ)) * x) := bmul (lowCoarseS20_hz2 hx hc) (lowCoarseS20_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS20_hz5 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B 1 (500847791247890659 / 500000000000000000) ((1 : ℝ) + ((√(184 : ℝ)) * x)) := badd (bpoint (1 : ℝ)) (lowCoarseS20_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS20_hz6 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B 1 (500847791247890659 / 500000000000000000) (nap x) := by
    convert (lowCoarseS20_hz5 hx hc) using 1 <;>
      norm_num [nap] <;> ring

theorem lowCoarseS20_hz7 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B 0 (1 / 64000000) (x^2) := bsq (lowCoarseS20_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS20_hz8 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B 0 (1 / 32000000) ((2 : ℝ) * (x^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS20_hz7 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS20_hz9 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B (31999999 / 32000000) 1 ((1 : ℝ) - ((2 : ℝ) * (x^2))) := bsub (bpoint (1 : ℝ)) (lowCoarseS20_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS20_hz10 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B (999999984374999877 / 1000000000000000000) 1 (√((1 : ℝ) - ((2 : ℝ) * (x^2)))) := bsqrt (lowCoarseS20_hz9 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS20_hz11 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B (998304401879218559 / 1000000000000000000) 1 ((√((1 : ℝ) - ((2 : ℝ) * (x^2)))) - ((√(184 : ℝ)) * x)) := bsub (lowCoarseS20_hz10 hx hc) (lowCoarseS20_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS20_hz12 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B (998304401879218559 / 1000000000000000000) 1 (nam x) := by
    convert (lowCoarseS20_hz11 hx hc) using 1 <;>
      norm_num [nam] <;> ring

theorem lowCoarseS20_hz13 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B (26666666666666409 / 40000000000000000) (133333333333342669 / 200000000000000000) (kdot ((1 / 2))) := by
    constructor
    · apply bkdot_lower (q := (115470053837925153 / 200000000000000000)) (a := (523598775598308991 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (144337567297406441 / 250000000000000000)) (a := (523598775598225551 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS20_hz14 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B (1 / 4) (1 / 4) (((1 / 2) : ℝ)^2) := bsq (bpoint ((1 / 2) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS20_hz15 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B (3 / 4) (3 / 4) ((1 : ℝ) - (((1 / 2) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS20_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS20_hz16 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B (433012701892219323 / 500000000000000000) (866025403784438647 / 1000000000000000000) (√((1 : ℝ) - (((1 / 2) : ℝ)^2))) := bsqrt (lowCoarseS20_hz15 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS20_hz17 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B (34458055963862003 / 125000000000000000) (11026577908435841 / 40000000000000000) ((√((1 : ℝ) - (((1 / 2) : ℝ)^2))) / Real.pi) := bdiv (lowCoarseS20_hz16 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS20_hz18 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B (5208333333333283 / 15625000000000000) (333333333333356673 / 1000000000000000000) (((1 / 2) : ℝ) * (kdot ((1 / 2)))) := bmul (bpoint ((1 / 2) : ℝ)) (lowCoarseS20_hz13 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS20_hz19 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B (76124722630528267 / 125000000000000000) (304498890522126349 / 500000000000000000) (((√((1 : ℝ) - (((1 / 2) : ℝ)^2))) / Real.pi) + (((1 / 2) : ℝ) * (kdot ((1 / 2))))) := badd (lowCoarseS20_hz17 hx hc) (lowCoarseS20_hz18 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS20_hz20 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B (76124722630528267 / 125000000000000000) (304498890522126349 / 500000000000000000) (kappa ((1 / 2))) := by rw [kappa_eq]; exact (lowCoarseS20_hz19 hx hc)

theorem lowCoarseS20_hz21 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B (335177304839959399 / 500000000000000000) (167588652419986579 / 250000000000000000) (kdot ((51 / 100))) := by
    constructor
    · apply bkdot_lower (q := (569651921139811611 / 1000000000000000000)) (a := (258902884129826761 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (56965192113981161 / 100000000000000000)) (a := (258902884129805149 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS20_hz22 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B (2601 / 10000) (2601 / 10000) (((51 / 100) : ℝ)^2) := bsq (bpoint ((51 / 100) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS20_hz23 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B (7399 / 10000) (7399 / 10000) ((1 : ℝ) - (((51 / 100) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS20_hz22 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS20_hz24 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B (860174400921115531 / 1000000000000000000) (215043600230278883 / 250000000000000000) (√((1 : ℝ) - (((51 / 100) : ℝ)^2))) := bsqrt (lowCoarseS20_hz23 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS20_hz25 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B (27380201565541061 / 100000000000000000) (273802015655410611 / 1000000000000000000) ((√((1 : ℝ) - (((51 / 100) : ℝ)^2))) / Real.pi) := bdiv (lowCoarseS20_hz24 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS20_hz26 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B (170940425468379293 / 500000000000000000) (170940425468386311 / 500000000000000000) (((51 / 100) : ℝ) * (kdot ((51 / 100)))) := bmul (bpoint ((51 / 100) : ℝ)) (lowCoarseS20_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS20_hz27 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B (153920716648042299 / 250000000000000000) (615682866592183233 / 1000000000000000000) (((√((1 : ℝ) - (((51 / 100) : ℝ)^2))) / Real.pi) + (((51 / 100) : ℝ) * (kdot ((51 / 100))))) := badd (lowCoarseS20_hz25 hx hc) (lowCoarseS20_hz26 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS20_hz28 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B (153920716648042299 / 250000000000000000) (615682866592183233 / 1000000000000000000) (kappa ((51 / 100))) := by rw [kappa_eq]; exact (lowCoarseS20_hz27 hx hc)

theorem lowCoarseS20_hz29 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B (76124722630528267 / 125000000000000000) (615682866592183233 / 1000000000000000000) (kappa c) := bkappa (lowCoarseS20_hz1 hx hc) (by norm_num) (by norm_num) (lowCoarseS20_hz20 hx hc).1 (lowCoarseS20_hz28 hx hc).2

theorem lowCoarseS20_hz30 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B (384317133407816767 / 1000000000000000000) (48875277369471733 / 125000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (lowCoarseS20_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS20_hz31 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B (384317133407816767 / 500000000000000000) (48875277369471733 / 62500000000000000) ((2 : ℝ) * ((1 : ℝ) - (kappa c))) := bmul (bpoint (2 : ℝ)) (lowCoarseS20_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS20_hz32 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B 0 (1 / 8000000) ((8 : ℝ) * (x^2)) := bmul (bpoint (8 : ℝ)) (lowCoarseS20_hz7 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS20_hz33 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B (384317070907816767 / 500000000000000000) (48875277369471733 / 62500000000000000) (((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2))) := bsub (lowCoarseS20_hz31 hx hc) (lowCoarseS20_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS20_hz34 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B (219179455842643007 / 250000000000000000) (442155074015765347 / 500000000000000000) (√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) := bsqrt (lowCoarseS20_hz33 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS20_hz35 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B (6782329983125268139 / 250000000000000000) (13564659966250536279 / 500000000000000000) ((2 : ℝ) * (√(184 : ℝ))) := bmul (bpoint (2 : ℝ)) (lowCoarseS20_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS20_hz36 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B 0 (678232998312527 / 200000000000000000) (((2 : ℝ) * (√(184 : ℝ))) * x) := bmul (lowCoarseS20_hz35 hx hc) (lowCoarseS20_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS20_hz37 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B (873326658379009393 / 1000000000000000000) (442155074015765347 / 500000000000000000) ((√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) - (((2 : ℝ) * (√(184 : ℝ))) * x)) := bsub (lowCoarseS20_hz34 hx hc) (lowCoarseS20_hz36 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS20_hz38 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B (873326658379009393 / 1000000000000000000) (442155074015765347 / 500000000000000000) (ndm x c) := by
    convert (lowCoarseS20_hz37 hx hc) using 1 <;>
      norm_num [ndm] <;> ring

theorem lowCoarseS20_hz39 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B 1 (1003394039991562637 / 1000000000000000000) ((nap x)^2) := bsq (lowCoarseS20_hz6 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS20_hz40 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B 2 (1003394039991562637 / 500000000000000000) ((2 : ℝ) * ((nap x)^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS20_hz39 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS20_hz41 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B (762699452235446977 / 1000000000000000000) (78200443791154773 / 100000000000000000) ((ndm x c)^2) := bsq (lowCoarseS20_hz38 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS20_hz42 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B (121799556208845227 / 100000000000000000) (1244088627747678297 / 1000000000000000000) (((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) := bsub (lowCoarseS20_hz40 hx hc) (lowCoarseS20_hz41 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS20_hz43 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B (199322335762284863 / 200000000000000000) 1 ((nam x)^2) := bsq (lowCoarseS20_hz12 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS20_hz44 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B (199322335762284863 / 100000000000000000) 2 ((2 : ℝ) * ((nam x)^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS20_hz43 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS20_hz45 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B (121799556208845227 / 200000000000000000) (624159165599684279 / 1000000000000000000) ((((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) / ((2 : ℝ) * ((nam x)^2))) := bdiv (lowCoarseS20_hz42 hx hc) (lowCoarseS20_hz44 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS20_hz46 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B (121799556208845227 / 200000000000000000) (624159165599684279 / 1000000000000000000) (nc1 x c) := by
    convert (lowCoarseS20_hz45 hx hc) using 1 <;>
      norm_num [nc1] <;> ring

theorem lowCoarseS20_hz47 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B (26666666666666409 / 40000000000000000) (167588652419986579 / 250000000000000000) (kdot c) := bkdot (lowCoarseS20_hz1 hx hc) (lowCoarseS20_hz13 hx hc).1 (lowCoarseS20_hz21 hx hc).2

theorem lowCoarseS20_hz48 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B (708428173536144027 / 1000000000000000000) (708428173536144053 / 1000000000000000000) (kdot ((121799556208845227 / 200000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (492960235490516693 / 1000000000000000000)) (a := (57249994250787999 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (123240058872629173 / 250000000000000000)) (a := (228999977003151977 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS20_hz49 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B (89319790987733201 / 125000000000000000) (357279163950932809 / 500000000000000000) (kdot ((624159165599684279 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (481047196703497487 / 1000000000000000000)) (a := (448370730045942833 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (240523598351748743 / 500000000000000000)) (a := (22418536502297141 / 50000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS20_hz50 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B (708428173536144027 / 1000000000000000000) (357279163950932809 / 500000000000000000) (kdot (nc1 x c)) := bkdot (lowCoarseS20_hz46 hx hc) (lowCoarseS20_hz48 hx hc).1 (lowCoarseS20_hz49 hx hc).2

theorem lowCoarseS20_hz51 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B (1 / 4) (2601 / 10000) (c^2) := bsq (lowCoarseS20_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS20_hz52 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B (7399 / 10000) (3 / 4) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS20_hz51 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS20_hz53 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B (860174400921115531 / 1000000000000000000) (866025403784438647 / 1000000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (lowCoarseS20_hz52 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS20_hz54 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B (573449600614071479 / 1000000000000000000) (580544121526835273 / 1000000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (lowCoarseS20_hz53 hx hc) (lowCoarseS20_hz47 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS20_hz55 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B (573449600614071479 / 1000000000000000000) (580544121526835273 / 1000000000000000000) (npa c) := by
    convert (lowCoarseS20_hz54 hx hc) using 1 <;>
      norm_num [npa] <;> ring

theorem lowCoarseS20_hz56 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B (27380201565541061 / 100000000000000000) (11026577908435841 / 40000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (lowCoarseS20_hz53 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS20_hz57 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B (5208333333333283 / 15625000000000000) (170940425468386311 / 500000000000000000) (c * (kdot c)) := bmul (lowCoarseS20_hz1 hx hc) (lowCoarseS20_hz47 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS20_hz58 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B (-17019708820340503 / 250000000000000000) (-57668885622434087 / 1000000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (lowCoarseS20_hz56 hx hc) (lowCoarseS20_hz57 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS20_hz59 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B (-17019708820340503 / 250000000000000000) (-57668885622434087 / 1000000000000000000) (npp c) := by
    convert (lowCoarseS20_hz58 hx hc) using 1 <;>
      norm_num [npp] <;> ring

theorem lowCoarseS20_hz60 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B 0 (23 / 4000) ((46 : ℝ) * x) := bmul (bpoint (46 : ℝ)) (lowCoarseS20_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS20_hz61 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B (9591663046625439083 / 1000000000000000000) (2399353261656359771 / 250000000000000000) ((√(92 : ℝ)) + ((46 : ℝ) * x)) := badd (lowCoarseS20_hz3 hx hc) (lowCoarseS20_hz60 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS20_hz62 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B (28774989139876317249 / 250000000000000000) (7198059784969079313 / 62500000000000000) ((12 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (bpoint (12 : ℝ)) (lowCoarseS20_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS20_hz63 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B 0 (14396119569938159 / 1000000000000000000) (((12 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS20_hz62 hx hc) (lowCoarseS20_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS20_hz64 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B 0 (14396119569938159 / 1000000000000000000) (nr1 x) := by
    convert (lowCoarseS20_hz63 hx hc) using 1 <;>
      norm_num [nr1] <;> ring

theorem lowCoarseS20_hz65 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B (9591663046625439083 / 125000000000000000) (2399353261656359771 / 31250000000000000) ((8 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (bpoint (8 : ℝ)) (lowCoarseS20_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS20_hz66 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B 0 (59983831541409 / 6250000000000000) (((8 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS20_hz65 hx hc) (lowCoarseS20_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS20_hz67 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B 0 (59983831541409 / 6250000000000000) (nrpp x) := by
    convert (lowCoarseS20_hz66 hx hc) using 1 <;>
      norm_num [nrpp] <;> ring

theorem lowCoarseS20_hz68 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B 0 (847791247890659 / 500000000000000000) (ne0 x) := by
    convert (lowCoarseS20_hz4 hx hc) using 1 <;>
      norm_num [ne0] <;> ring

theorem lowCoarseS20_hz69 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B (573449600614071479 / 1000000000000000000) (74367530137096679 / 125000000000000000) ((npa c) + (nr1 x)) := badd (lowCoarseS20_hz55 hx hc) (lowCoarseS20_hz64 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS20_hz70 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B (573449600614071479 / 1000000000000000000) (148987683510373127 / 250000000000000000) (((npa c) + (nr1 x)) / (nam x)) := bdiv (lowCoarseS20_hz69 hx hc) (lowCoarseS20_hz12 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS20_hz71 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B (573449600614071479 / 1000000000000000000) (298823158268636913 / 500000000000000000) ((((npa c) + (nr1 x)) / (nam x)) + (ne0 x)) := badd (lowCoarseS20_hz70 hx hc) (lowCoarseS20_hz68 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS20_hz72 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B (573449600614071479 / 1000000000000000000) (298823158268636913 / 500000000000000000) (nlam x c) := by
    convert (lowCoarseS20_hz71 hx hc) using 1 <;>
      norm_num [nlam] <;> ring

theorem lowCoarseS20_hz73 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS20_hz74 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B 0 (59947894041409 / 100000000000000000) ((√(23 : ℝ)) * x) := bmul (lowCoarseS20_hz73 hx hc) (lowCoarseS20_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS20_hz75 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B (1 / 2) (50059947894041409 / 100000000000000000) (((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)) := badd (bpoint ((1 / 2) : ℝ)) (lowCoarseS20_hz74 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS20_hz76 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B (176776695296636881 / 250000000000000000) (353765274914177413 / 500000000000000000) (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) := bsqrt (lowCoarseS20_hz75 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS20_hz77 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B 0 (59947894041409 / 50000000000000000) ((√(92 : ℝ)) * x) := bmul (lowCoarseS20_hz3 hx hc) (lowCoarseS20_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS20_hz78 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B (176776695296636881 / 250000000000000000) (354364753854591503 / 500000000000000000) ((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x)) := badd (lowCoarseS20_hz76 hx hc) (lowCoarseS20_hz77 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS20_hz79 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B (499999999999999999 / 1000000000000000000) (251148757548850447 / 500000000000000000) (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2) := bsq (lowCoarseS20_hz78 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS20_hz80 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B (499999999999999999 / 125000000000000000) (251148757548850447 / 62500000000000000) ((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) := bmul (bpoint (8 : ℝ)) (lowCoarseS20_hz79 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS20_hz81 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B (7673330437300351251 / 200000000000000000) (1928302689874485209 / 50000000000000000) (((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (lowCoarseS20_hz80 hx hc) (lowCoarseS20_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS20_hz82 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B 0 (2410378362343107 / 500000000000000000) ((((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS20_hz81 hx hc) (lowCoarseS20_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS20_hz83 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B 0 (2410378362343107 / 500000000000000000) (nrs x) := by
    convert (lowCoarseS20_hz82 hx hc) using 1 <;>
      norm_num [nrs] <;> ring

theorem lowCoarseS20_hz84 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B (-17019708820340503 / 250000000000000000) (-48071472575808647 / 1000000000000000000) ((npp c) + (nrpp x)) := badd (lowCoarseS20_hz59 hx hc) (lowCoarseS20_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS20_hz85 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B (-1945851948166263 / 40000000000000000) (-24035736287904323 / 1000000000000000000) (if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) := bweaken (bfirst (lowCoarseS20_hz84 hx hc) (lowCoarseS20_hz50 hx hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem lowCoarseS20_hz86 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B (41105555555554761 / 125000000000000000) (178590559835285651 / 500000000000000000) ((nlam x c)^2) := bsq (lowCoarseS20_hz72 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS20_hz87 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B (370878297316791197 / 1000000000000000000) (48696833000261763 / 125000000000000000) ((nc1 x c)^2) := bsq (lowCoarseS20_hz46 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS20_hz88 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B (76303166999738237 / 125000000000000000) (629121702683208803 / 1000000000000000000) ((1 : ℝ) - ((nc1 x c)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS20_hz87 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS20_hz89 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B (781297213612019671 / 1000000000000000000) (793171925047280531 / 1000000000000000000) (√((1 : ℝ) - ((nc1 x c)^2))) := bsqrt (lowCoarseS20_hz88 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS20_hz90 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B (613629396638424101 / 250000000000000000) (2491823092762210633 / 1000000000000000000) (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))) := bmul pi_mem (lowCoarseS20_hz89 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS20_hz91 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B (131969418454947681 / 1000000000000000000) (14551988611826449 / 100000000000000000) (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2))))) := bdiv (lowCoarseS20_hz86 hx hc) (lowCoarseS20_hz90 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS20_hz92 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B (41661559875395553 / 500000000000000000) (121484149830360167 / 1000000000000000000) ((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) := badd (lowCoarseS20_hz85 hx hc) (lowCoarseS20_hz91 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS20_hz93 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B 0 (2875000000001 / 1000000000000000000) ((ne0 x)^2) := bsq (lowCoarseS20_hz68 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS20_hz94 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B (41661559875395553 / 500000000000000000) (15185878103795021 / 125000000000000000) (((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) + ((ne0 x)^2)) := badd (lowCoarseS20_hz92 hx hc) (lowCoarseS20_hz93 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS20_hz95 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B (41661559875395553 / 500000000000000000) (63153890777523191 / 500000000000000000) ((((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) + ((ne0 x)^2)) + (nrs x)) := badd (lowCoarseS20_hz94 hx hc) (lowCoarseS20_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS20_hz96 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B (41661559875395553 / 500000000000000000) (63153890777523191 / 500000000000000000) (nu x c) := by
    convert (lowCoarseS20_hz95 hx hc) using 1 <;>
      norm_num [nu] <;> ring

theorem lowCoarseS20_hz97 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B (-19419062081996863 / 250000000000000000) (-57668885622434087 / 1000000000000000000) ((npp c) - (nrpp x)) := bsub (lowCoarseS20_hz59 hx hc) (lowCoarseS20_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS20_hz98 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B (-19419062081996863 / 250000000000000000) (-57668885622434087 / 1000000000000000000) (min ((npp c) - (nrpp x)) (0 : ℝ)) := bweaken (bmin (lowCoarseS20_hz97 hx hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem lowCoarseS20_hz99 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B (-55504210122936799 / 1000000000000000000) (-2553391456960361 / 62500000000000000) ((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) := bmul (lowCoarseS20_hz50 hx hc) (lowCoarseS20_hz98 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS20_hz100 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B (-69383856403671 / 1250000000000000) (-2553391456960361 / 62500000000000000) (((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) - ((ne0 x)^2)) := bsub (lowCoarseS20_hz99 hx hc) (lowCoarseS20_hz93 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS20_hz101 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B (-30163920923811507 / 500000000000000000) (-2553391456960361 / 62500000000000000) ((((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) - ((ne0 x)^2)) - (nrs x)) := bsub (lowCoarseS20_hz100 hx hc) (lowCoarseS20_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS20_hz102 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B (-30163920923811507 / 500000000000000000) (-2553391456960361 / 62500000000000000) (nl x c) := by
    convert (lowCoarseS20_hz101 hx hc) using 1 <;>
      norm_num [nl] <;> ring

theorem lowCoarseS20_hz103 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B 0 (63153890777523191 / 500000000000000000) |(nu x c)| := bweaken (babs (lowCoarseS20_hz96 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS20_hz104 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B 0 (30163920923811507 / 500000000000000000) |(nl x c)| := bweaken (babs (lowCoarseS20_hz102 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS20_hz105 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B 0 (63153890777523191 / 500000000000000000) (max |(nu x c)| |(nl x c)|) := bweaken (bmax (lowCoarseS20_hz103 hx hc) (lowCoarseS20_hz104 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS20_hz106 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) : B 0 (63153890777523191 / 500000000000000000) (ns x c) := by
    convert (lowCoarseS20_hz105 hx hc) using 1 <;>
      norm_num [ns] <;> ring

theorem lowCoarseS20 {x c : ℝ}
    (hx : B 0 (1/8000) x) (hc : B (1 / 2) (51 / 100) c) :
    0 < nam x ∧ 0 ≤ ndm x c ∧ ndm x c ^ 2 ≤ 2 * nap x ^ 2 ∧ nc1 x c < 1 ∧
    0 ≤ npa c - nr1 x ∧ ne0 x ≤ (npa c - nr1 x) / nap x ∧ ns x c ≤ (1 / 5) := by
  refine ⟨lt_of_lt_of_le (by norm_num) (lowCoarseS20_hz12 hx hc).1,
    le_trans (by norm_num) (lowCoarseS20_hz38 hx hc).1, ?_,
    lt_of_le_of_lt (lowCoarseS20_hz46 hx hc).2 (by norm_num), ?_, ?_, (lowCoarseS20_hz106 hx hc).2.trans (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (lowCoarseS20_hz38 hx hc).1) (lowCoarseS20_hz38 hx hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) (lowCoarseS20_hz6 hx hc).1 2
    nlinarith only [h1,h2]
  · linarith only [(lowCoarseS20_hz55 hx hc).1,(lowCoarseS20_hz64 hx hc).2]
  · have hap : 0 < nap x := lt_of_lt_of_le (by norm_num) (lowCoarseS20_hz6 hx hc).1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul (lowCoarseS20_hz68 hx hc).2 (lowCoarseS20_hz6 hx hc).2 (le_trans (by norm_num) (lowCoarseS20_hz6 hx hc).1) (by norm_num)
    linarith only [h,(lowCoarseS20_hz55 hx hc).1,(lowCoarseS20_hz64 hx hc).2]

theorem lowCoarseS21_hz0 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B 0 (1 / 8000) x := hx

theorem lowCoarseS21_hz1 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B (51 / 100) (13 / 25) c := hc

theorem lowCoarseS21_hz2 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B (6782329983125268139 / 500000000000000000) (13564659966250536279 / 1000000000000000000) (√(184 : ℝ)) := bsqrt (bpoint (184 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS21_hz3 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS21_hz4 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B 0 (847791247890659 / 500000000000000000) ((√(184 : ℝ)) * x) := bmul (lowCoarseS21_hz2 hx hc) (lowCoarseS21_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS21_hz5 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B 1 (500847791247890659 / 500000000000000000) ((1 : ℝ) + ((√(184 : ℝ)) * x)) := badd (bpoint (1 : ℝ)) (lowCoarseS21_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS21_hz6 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B 1 (500847791247890659 / 500000000000000000) (nap x) := by
    convert (lowCoarseS21_hz5 hx hc) using 1 <;>
      norm_num [nap] <;> ring

theorem lowCoarseS21_hz7 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B 0 (1 / 64000000) (x^2) := bsq (lowCoarseS21_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS21_hz8 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B 0 (1 / 32000000) ((2 : ℝ) * (x^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS21_hz7 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS21_hz9 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B (31999999 / 32000000) 1 ((1 : ℝ) - ((2 : ℝ) * (x^2))) := bsub (bpoint (1 : ℝ)) (lowCoarseS21_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS21_hz10 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B (999999984374999877 / 1000000000000000000) 1 (√((1 : ℝ) - ((2 : ℝ) * (x^2)))) := bsqrt (lowCoarseS21_hz9 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS21_hz11 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B (998304401879218559 / 1000000000000000000) 1 ((√((1 : ℝ) - ((2 : ℝ) * (x^2)))) - ((√(184 : ℝ)) * x)) := bsub (lowCoarseS21_hz10 hx hc) (lowCoarseS21_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS21_hz12 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B (998304401879218559 / 1000000000000000000) 1 (nam x) := by
    convert (lowCoarseS21_hz11 hx hc) using 1 <;>
      norm_num [nam] <;> ring

theorem lowCoarseS21_hz13 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B (335177304839959399 / 500000000000000000) (167588652419986579 / 250000000000000000) (kdot ((51 / 100))) := by
    constructor
    · apply bkdot_lower (q := (569651921139811611 / 1000000000000000000)) (a := (258902884129826761 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (56965192113981161 / 100000000000000000)) (a := (258902884129805149 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS21_hz14 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B (2601 / 10000) (2601 / 10000) (((51 / 100) : ℝ)^2) := bsq (bpoint ((51 / 100) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS21_hz15 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B (7399 / 10000) (7399 / 10000) ((1 : ℝ) - (((51 / 100) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS21_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS21_hz16 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B (860174400921115531 / 1000000000000000000) (215043600230278883 / 250000000000000000) (√((1 : ℝ) - (((51 / 100) : ℝ)^2))) := bsqrt (lowCoarseS21_hz15 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS21_hz17 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B (27380201565541061 / 100000000000000000) (273802015655410611 / 1000000000000000000) ((√((1 : ℝ) - (((51 / 100) : ℝ)^2))) / Real.pi) := bdiv (lowCoarseS21_hz16 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS21_hz18 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B (170940425468379293 / 500000000000000000) (170940425468386311 / 500000000000000000) (((51 / 100) : ℝ) * (kdot ((51 / 100)))) := bmul (bpoint ((51 / 100) : ℝ)) (lowCoarseS21_hz13 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS21_hz19 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B (153920716648042299 / 250000000000000000) (615682866592183233 / 1000000000000000000) (((√((1 : ℝ) - (((51 / 100) : ℝ)^2))) / Real.pi) + (((51 / 100) : ℝ) * (kdot ((51 / 100))))) := badd (lowCoarseS21_hz17 hx hc) (lowCoarseS21_hz18 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS21_hz20 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B (153920716648042299 / 250000000000000000) (615682866592183233 / 1000000000000000000) (kappa ((51 / 100))) := by rw [kappa_eq]; exact (lowCoarseS21_hz19 hx hc)

theorem lowCoarseS21_hz21 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B (674068063875522049 / 1000000000000000000) (26962722555021447 / 40000000000000000) (kdot ((13 / 25))) := by
    constructor
    · apply bkdot_lower (q := (28097574347450819 / 50000000000000000)) (a := (255986344024739419 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (561951486949016379 / 1000000000000000000)) (a := (10239453760989133 / 20000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS21_hz22 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B (169 / 625) (169 / 625) (((13 / 25) : ℝ)^2) := bsq (bpoint ((13 / 25) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS21_hz23 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B (456 / 625) (456 / 625) ((1 : ℝ) - (((13 / 25) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS21_hz22 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS21_hz24 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B (13346347815039139 / 15625000000000000) (854166260162504897 / 1000000000000000000) (√((1 : ℝ) - (((13 / 25) : ℝ)^2))) := bsqrt (lowCoarseS21_hz23 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS21_hz25 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B (54377913010872213 / 200000000000000000) (135944782527180533 / 500000000000000000) ((√((1 : ℝ) - (((13 / 25) : ℝ)^2))) / Real.pi) := bdiv (lowCoarseS21_hz24 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS21_hz26 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B (70103078643054293 / 200000000000000000) (350515393215278811 / 1000000000000000000) (((13 / 25) : ℝ) * (kdot ((13 / 25)))) := bmul (bpoint ((13 / 25) : ℝ)) (lowCoarseS21_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS21_hz27 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B (62240495826963253 / 100000000000000000) (622404958269639877 / 1000000000000000000) (((√((1 : ℝ) - (((13 / 25) : ℝ)^2))) / Real.pi) + (((13 / 25) : ℝ) * (kdot ((13 / 25))))) := badd (lowCoarseS21_hz25 hx hc) (lowCoarseS21_hz26 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS21_hz28 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B (62240495826963253 / 100000000000000000) (622404958269639877 / 1000000000000000000) (kappa ((13 / 25))) := by rw [kappa_eq]; exact (lowCoarseS21_hz27 hx hc)

theorem lowCoarseS21_hz29 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B (153920716648042299 / 250000000000000000) (622404958269639877 / 1000000000000000000) (kappa c) := bkappa (lowCoarseS21_hz1 hx hc) (by norm_num) (by norm_num) (lowCoarseS21_hz20 hx hc).1 (lowCoarseS21_hz28 hx hc).2

theorem lowCoarseS21_hz30 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B (377595041730360123 / 1000000000000000000) (96079283351957701 / 250000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (lowCoarseS21_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS21_hz31 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B (377595041730360123 / 500000000000000000) (96079283351957701 / 125000000000000000) ((2 : ℝ) * ((1 : ℝ) - (kappa c))) := bmul (bpoint (2 : ℝ)) (lowCoarseS21_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS21_hz32 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B 0 (1 / 8000000) ((8 : ℝ) * (x^2)) := bmul (bpoint (8 : ℝ)) (lowCoarseS21_hz7 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS21_hz33 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B (377594979230360123 / 500000000000000000) (96079283351957701 / 125000000000000000) (((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2))) := bsub (lowCoarseS21_hz31 hx hc) (lowCoarseS21_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS21_hz34 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B (434508330892723001 / 500000000000000000) (109589736832400107 / 125000000000000000) (√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) := bsqrt (lowCoarseS21_hz33 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS21_hz35 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B (6782329983125268139 / 250000000000000000) (13564659966250536279 / 500000000000000000) ((2 : ℝ) * (√(184 : ℝ))) := bmul (bpoint (2 : ℝ)) (lowCoarseS21_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS21_hz36 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B 0 (678232998312527 / 200000000000000000) (((2 : ℝ) * (√(184 : ℝ))) * x) := bmul (lowCoarseS21_hz35 hx hc) (lowCoarseS21_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS21_hz37 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B (865625496793883367 / 1000000000000000000) (109589736832400107 / 125000000000000000) ((√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) - (((2 : ℝ) * (√(184 : ℝ))) * x)) := bsub (lowCoarseS21_hz34 hx hc) (lowCoarseS21_hz36 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS21_hz38 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B (865625496793883367 / 1000000000000000000) (109589736832400107 / 125000000000000000) (ndm x c) := by
    convert (lowCoarseS21_hz37 hx hc) using 1 <;>
      norm_num [ndm] <;> ring

theorem lowCoarseS21_hz39 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B 1 (1003394039991562637 / 1000000000000000000) ((nap x)^2) := bsq (lowCoarseS21_hz6 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS21_hz40 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B 2 (1003394039991562637 / 500000000000000000) ((2 : ℝ) * ((nap x)^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS21_hz39 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS21_hz41 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B (749307500699657383 / 1000000000000000000) (768634266815661609 / 1000000000000000000) ((ndm x c)^2) := bsq (lowCoarseS21_hz38 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS21_hz42 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B (1231365733184338391 / 1000000000000000000) (1257480579283467891 / 1000000000000000000) (((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) := bsub (lowCoarseS21_hz40 hx hc) (lowCoarseS21_hz41 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS21_hz43 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B (199322335762284863 / 200000000000000000) 1 ((nam x)^2) := bsq (lowCoarseS21_hz12 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS21_hz44 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B (199322335762284863 / 100000000000000000) 2 ((2 : ℝ) * ((nam x)^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS21_hz43 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS21_hz45 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B (123136573318433839 / 200000000000000000) (157719476655034809 / 250000000000000000) ((((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) / ((2 : ℝ) * ((nam x)^2))) := bdiv (lowCoarseS21_hz42 hx hc) (lowCoarseS21_hz44 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS21_hz46 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B (123136573318433839 / 200000000000000000) (157719476655034809 / 250000000000000000) (nc1 x c) := by
    convert (lowCoarseS21_hz45 hx hc) using 1 <;>
      norm_num [nc1] <;> ring

theorem lowCoarseS21_hz47 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B (335177304839959399 / 500000000000000000) (26962722555021447 / 40000000000000000) (kdot c) := bkdot (lowCoarseS21_hz1 hx hc) (lowCoarseS21_hz13 hx hc).1 (lowCoarseS21_hz21 hx hc).2

theorem lowCoarseS21_hz48 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B (177779938003315693 / 250000000000000000) (177779938003315697 / 250000000000000000) (kdot ((123136573318433839 / 200000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (243857893384775827 / 500000000000000000)) (a := (226886016210582833 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (487715786769551653 / 1000000000000000000)) (a := (453772032421165643 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS21_hz49 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B (143461025148578987 / 200000000000000000) (717305125742894941 / 1000000000000000000) (kdot ((157719476655034809 / 250000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (118936267187256291 / 250000000000000000)) (a := (88811214017361163 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (475745068749025163 / 1000000000000000000)) (a := (444056070086805807 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS21_hz50 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B (177779938003315693 / 250000000000000000) (717305125742894941 / 1000000000000000000) (kdot (nc1 x c)) := bkdot (lowCoarseS21_hz46 hx hc) (lowCoarseS21_hz48 hx hc).1 (lowCoarseS21_hz49 hx hc).2

theorem lowCoarseS21_hz51 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B (2601 / 10000) (169 / 625) (c^2) := bsq (lowCoarseS21_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS21_hz52 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B (456 / 625) (7399 / 10000) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS21_hz51 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS21_hz53 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B (13346347815039139 / 15625000000000000) (215043600230278883 / 250000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (lowCoarseS21_hz52 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS21_hz54 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B (286297144966495971 / 500000000000000000) (36238505814012223 / 62500000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (lowCoarseS21_hz53 hx hc) (lowCoarseS21_hz47 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS21_hz55 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B (286297144966495971 / 500000000000000000) (36238505814012223 / 62500000000000000) (npa c) := by
    convert (lowCoarseS21_hz54 hx hc) using 1 <;>
      norm_num [npa] <;> ring

theorem lowCoarseS21_hz56 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B (54377913010872213 / 200000000000000000) (273802015655410611 / 1000000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (lowCoarseS21_hz53 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS21_hz57 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B (170940425468379293 / 500000000000000000) (350515393215278811 / 1000000000000000000) (c * (kdot c)) := bmul (lowCoarseS21_hz1 hx hc) (lowCoarseS21_hz47 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS21_hz58 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B (-39312914080458873 / 500000000000000000) (-2723153411253919 / 40000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (lowCoarseS21_hz56 hx hc) (lowCoarseS21_hz57 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS21_hz59 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B (-39312914080458873 / 500000000000000000) (-2723153411253919 / 40000000000000000) (npp c) := by
    convert (lowCoarseS21_hz58 hx hc) using 1 <;>
      norm_num [npp] <;> ring

theorem lowCoarseS21_hz60 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B 0 (23 / 4000) ((46 : ℝ) * x) := bmul (bpoint (46 : ℝ)) (lowCoarseS21_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS21_hz61 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B (9591663046625439083 / 1000000000000000000) (2399353261656359771 / 250000000000000000) ((√(92 : ℝ)) + ((46 : ℝ) * x)) := badd (lowCoarseS21_hz3 hx hc) (lowCoarseS21_hz60 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS21_hz62 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B (28774989139876317249 / 250000000000000000) (7198059784969079313 / 62500000000000000) ((12 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (bpoint (12 : ℝ)) (lowCoarseS21_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS21_hz63 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B 0 (14396119569938159 / 1000000000000000000) (((12 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS21_hz62 hx hc) (lowCoarseS21_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS21_hz64 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B 0 (14396119569938159 / 1000000000000000000) (nr1 x) := by
    convert (lowCoarseS21_hz63 hx hc) using 1 <;>
      norm_num [nr1] <;> ring

theorem lowCoarseS21_hz65 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B (9591663046625439083 / 125000000000000000) (2399353261656359771 / 31250000000000000) ((8 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (bpoint (8 : ℝ)) (lowCoarseS21_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS21_hz66 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B 0 (59983831541409 / 6250000000000000) (((8 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS21_hz65 hx hc) (lowCoarseS21_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS21_hz67 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B 0 (59983831541409 / 6250000000000000) (nrpp x) := by
    convert (lowCoarseS21_hz66 hx hc) using 1 <;>
      norm_num [nrpp] <;> ring

theorem lowCoarseS21_hz68 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B 0 (847791247890659 / 500000000000000000) (ne0 x) := by
    convert (lowCoarseS21_hz4 hx hc) using 1 <;>
      norm_num [ne0] <;> ring

theorem lowCoarseS21_hz69 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B (286297144966495971 / 500000000000000000) (594212212594133727 / 1000000000000000000) ((npa c) + (nr1 x)) := badd (lowCoarseS21_hz55 hx hc) (lowCoarseS21_hz64 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS21_hz70 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B (286297144966495971 / 500000000000000000) (595221468998416211 / 1000000000000000000) (((npa c) + (nr1 x)) / (nam x)) := bdiv (lowCoarseS21_hz69 hx hc) (lowCoarseS21_hz12 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS21_hz71 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B (286297144966495971 / 500000000000000000) (596917051494197529 / 1000000000000000000) ((((npa c) + (nr1 x)) / (nam x)) + (ne0 x)) := badd (lowCoarseS21_hz70 hx hc) (lowCoarseS21_hz68 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS21_hz72 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B (286297144966495971 / 500000000000000000) (596917051494197529 / 1000000000000000000) (nlam x c) := by
    convert (lowCoarseS21_hz71 hx hc) using 1 <;>
      norm_num [nlam] <;> ring

theorem lowCoarseS21_hz73 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS21_hz74 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B 0 (59947894041409 / 100000000000000000) ((√(23 : ℝ)) * x) := bmul (lowCoarseS21_hz73 hx hc) (lowCoarseS21_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS21_hz75 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B (1 / 2) (50059947894041409 / 100000000000000000) (((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)) := badd (bpoint ((1 / 2) : ℝ)) (lowCoarseS21_hz74 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS21_hz76 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B (176776695296636881 / 250000000000000000) (353765274914177413 / 500000000000000000) (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) := bsqrt (lowCoarseS21_hz75 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS21_hz77 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B 0 (59947894041409 / 50000000000000000) ((√(92 : ℝ)) * x) := bmul (lowCoarseS21_hz3 hx hc) (lowCoarseS21_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS21_hz78 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B (176776695296636881 / 250000000000000000) (354364753854591503 / 500000000000000000) ((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x)) := badd (lowCoarseS21_hz76 hx hc) (lowCoarseS21_hz77 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS21_hz79 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B (499999999999999999 / 1000000000000000000) (251148757548850447 / 500000000000000000) (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2) := bsq (lowCoarseS21_hz78 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS21_hz80 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B (499999999999999999 / 125000000000000000) (251148757548850447 / 62500000000000000) ((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) := bmul (bpoint (8 : ℝ)) (lowCoarseS21_hz79 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS21_hz81 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B (7673330437300351251 / 200000000000000000) (1928302689874485209 / 50000000000000000) (((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (lowCoarseS21_hz80 hx hc) (lowCoarseS21_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS21_hz82 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B 0 (2410378362343107 / 500000000000000000) ((((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS21_hz81 hx hc) (lowCoarseS21_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS21_hz83 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B 0 (2410378362343107 / 500000000000000000) (nrs x) := by
    convert (lowCoarseS21_hz82 hx hc) using 1 <;>
      norm_num [nrs] <;> ring

theorem lowCoarseS21_hz84 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B (-39312914080458873 / 500000000000000000) (-11696284446944507 / 200000000000000000) ((npp c) + (nrpp x)) := badd (lowCoarseS21_hz59 hx hc) (lowCoarseS21_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS21_hz85 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B (-28199354777803177 / 500000000000000000) (-29240711117361267 / 1000000000000000000) (if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) := bweaken (bfirst (lowCoarseS21_hz84 hx hc) (lowCoarseS21_hz50 hx hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem lowCoarseS21_hz86 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B (327864220863867237 / 1000000000000000000) (71261993272905293 / 200000000000000000) ((nlam x c)^2) := bsq (lowCoarseS21_hz72 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS21_hz87 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B (37906539221515081 / 100000000000000000) (199003466530704561 / 500000000000000000) ((nc1 x c)^2) := bsq (lowCoarseS21_hz46 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS21_hz88 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B (300996533469295439 / 500000000000000000) (62093460778484919 / 100000000000000000) ((1 : ℝ) - ((nc1 x c)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS21_hz87 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS21_hz89 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B (775882121806264381 / 1000000000000000000) (787994040450084363 / 1000000000000000000) (√((1 : ℝ) - ((nc1 x c)^2))) := bsqrt (lowCoarseS21_hz88 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS21_hz90 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B (1218752786959110649 / 500000000000000000) (1237778144275261703 / 500000000000000000) (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))) := bmul pi_mem (lowCoarseS21_hz89 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS21_hz91 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B (66220312254712823 / 500000000000000000) (18272264183573141 / 125000000000000000) (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2))))) := bdiv (lowCoarseS21_hz86 hx hc) (lowCoarseS21_hz90 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS21_hz92 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B (19010478738454823 / 250000000000000000) (116937402351223861 / 1000000000000000000) ((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) := badd (lowCoarseS21_hz85 hx hc) (lowCoarseS21_hz91 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS21_hz93 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B 0 (2875000000001 / 1000000000000000000) ((ne0 x)^2) := bsq (lowCoarseS21_hz68 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS21_hz94 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B (19010478738454823 / 250000000000000000) (58470138675611931 / 500000000000000000) (((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) + ((ne0 x)^2)) := badd (lowCoarseS21_hz92 hx hc) (lowCoarseS21_hz93 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS21_hz95 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B (19010478738454823 / 250000000000000000) (30440258518977519 / 250000000000000000) ((((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) + ((ne0 x)^2)) + (nrs x)) := badd (lowCoarseS21_hz94 hx hc) (lowCoarseS21_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS21_hz96 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B (19010478738454823 / 250000000000000000) (30440258518977519 / 250000000000000000) (nu x c) := by
    convert (lowCoarseS21_hz95 hx hc) using 1 <;>
      norm_num [nu] <;> ring

theorem lowCoarseS21_hz97 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B (-44111620603771593 / 500000000000000000) (-2723153411253919 / 40000000000000000) ((npp c) - (nrpp x)) := bsub (lowCoarseS21_hz59 hx hc) (lowCoarseS21_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS21_hz98 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B (-44111620603771593 / 500000000000000000) (-2723153411253919 / 40000000000000000) (min ((npp c) - (nrpp x)) (0 : ℝ)) := bweaken (bmin (lowCoarseS21_hz97 hx hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem lowCoarseS21_hz99 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B (-15820745781955629 / 250000000000000000) (-756440694728499 / 15625000000000000) ((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) := bmul (lowCoarseS21_hz50 hx hc) (lowCoarseS21_hz98 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS21_hz100 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B (-63285858127822517 / 1000000000000000000) (-756440694728499 / 15625000000000000) (((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) - ((ne0 x)^2)) := bsub (lowCoarseS21_hz99 hx hc) (lowCoarseS21_hz93 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS21_hz101 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B (-68106614852508731 / 1000000000000000000) (-756440694728499 / 15625000000000000) ((((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) - ((ne0 x)^2)) - (nrs x)) := bsub (lowCoarseS21_hz100 hx hc) (lowCoarseS21_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS21_hz102 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B (-68106614852508731 / 1000000000000000000) (-756440694728499 / 15625000000000000) (nl x c) := by
    convert (lowCoarseS21_hz101 hx hc) using 1 <;>
      norm_num [nl] <;> ring

theorem lowCoarseS21_hz103 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B 0 (30440258518977519 / 250000000000000000) |(nu x c)| := bweaken (babs (lowCoarseS21_hz96 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS21_hz104 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B 0 (68106614852508731 / 1000000000000000000) |(nl x c)| := bweaken (babs (lowCoarseS21_hz102 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS21_hz105 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B 0 (30440258518977519 / 250000000000000000) (max |(nu x c)| |(nl x c)|) := bweaken (bmax (lowCoarseS21_hz103 hx hc) (lowCoarseS21_hz104 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS21_hz106 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) : B 0 (30440258518977519 / 250000000000000000) (ns x c) := by
    convert (lowCoarseS21_hz105 hx hc) using 1 <;>
      norm_num [ns] <;> ring

theorem lowCoarseS21 {x c : ℝ}
    (hx : B 0 (1/8000) x) (hc : B (51 / 100) (13 / 25) c) :
    0 < nam x ∧ 0 ≤ ndm x c ∧ ndm x c ^ 2 ≤ 2 * nap x ^ 2 ∧ nc1 x c < 1 ∧
    0 ≤ npa c - nr1 x ∧ ne0 x ≤ (npa c - nr1 x) / nap x ∧ ns x c ≤ (1 / 5) := by
  refine ⟨lt_of_lt_of_le (by norm_num) (lowCoarseS21_hz12 hx hc).1,
    le_trans (by norm_num) (lowCoarseS21_hz38 hx hc).1, ?_,
    lt_of_le_of_lt (lowCoarseS21_hz46 hx hc).2 (by norm_num), ?_, ?_, (lowCoarseS21_hz106 hx hc).2.trans (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (lowCoarseS21_hz38 hx hc).1) (lowCoarseS21_hz38 hx hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) (lowCoarseS21_hz6 hx hc).1 2
    nlinarith only [h1,h2]
  · linarith only [(lowCoarseS21_hz55 hx hc).1,(lowCoarseS21_hz64 hx hc).2]
  · have hap : 0 < nap x := lt_of_lt_of_le (by norm_num) (lowCoarseS21_hz6 hx hc).1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul (lowCoarseS21_hz68 hx hc).2 (lowCoarseS21_hz6 hx hc).2 (le_trans (by norm_num) (lowCoarseS21_hz6 hx hc).1) (by norm_num)
    linarith only [h,(lowCoarseS21_hz55 hx hc).1,(lowCoarseS21_hz64 hx hc).2]

theorem lowCoarseS22_hz0 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B 0 (1 / 8000) x := hx

theorem lowCoarseS22_hz1 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B (13 / 25) (53 / 100) c := hc

theorem lowCoarseS22_hz2 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B (6782329983125268139 / 500000000000000000) (13564659966250536279 / 1000000000000000000) (√(184 : ℝ)) := bsqrt (bpoint (184 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS22_hz3 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS22_hz4 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B 0 (847791247890659 / 500000000000000000) ((√(184 : ℝ)) * x) := bmul (lowCoarseS22_hz2 hx hc) (lowCoarseS22_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS22_hz5 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B 1 (500847791247890659 / 500000000000000000) ((1 : ℝ) + ((√(184 : ℝ)) * x)) := badd (bpoint (1 : ℝ)) (lowCoarseS22_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS22_hz6 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B 1 (500847791247890659 / 500000000000000000) (nap x) := by
    convert (lowCoarseS22_hz5 hx hc) using 1 <;>
      norm_num [nap] <;> ring

theorem lowCoarseS22_hz7 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B 0 (1 / 64000000) (x^2) := bsq (lowCoarseS22_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS22_hz8 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B 0 (1 / 32000000) ((2 : ℝ) * (x^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS22_hz7 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS22_hz9 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B (31999999 / 32000000) 1 ((1 : ℝ) - ((2 : ℝ) * (x^2))) := bsub (bpoint (1 : ℝ)) (lowCoarseS22_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS22_hz10 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B (999999984374999877 / 1000000000000000000) 1 (√((1 : ℝ) - ((2 : ℝ) * (x^2)))) := bsqrt (lowCoarseS22_hz9 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS22_hz11 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B (998304401879218559 / 1000000000000000000) 1 ((√((1 : ℝ) - ((2 : ℝ) * (x^2)))) - ((√(184 : ℝ)) * x)) := bsub (lowCoarseS22_hz10 hx hc) (lowCoarseS22_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS22_hz12 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B (998304401879218559 / 1000000000000000000) 1 (nam x) := by
    convert (lowCoarseS22_hz11 hx hc) using 1 <;>
      norm_num [nam] <;> ring

theorem lowCoarseS22_hz13 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B (674068063875522049 / 1000000000000000000) (26962722555021447 / 40000000000000000) (kdot ((13 / 25))) := by
    constructor
    · apply bkdot_lower (q := (28097574347450819 / 50000000000000000)) (a := (255986344024739419 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (561951486949016379 / 1000000000000000000)) (a := (10239453760989133 / 20000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS22_hz14 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B (169 / 625) (169 / 625) (((13 / 25) : ℝ)^2) := bsq (bpoint ((13 / 25) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS22_hz15 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B (456 / 625) (456 / 625) ((1 : ℝ) - (((13 / 25) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS22_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS22_hz16 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B (13346347815039139 / 15625000000000000) (854166260162504897 / 1000000000000000000) (√((1 : ℝ) - (((13 / 25) : ℝ)^2))) := bsqrt (lowCoarseS22_hz15 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS22_hz17 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B (54377913010872213 / 200000000000000000) (135944782527180533 / 500000000000000000) ((√((1 : ℝ) - (((13 / 25) : ℝ)^2))) / Real.pi) := bdiv (lowCoarseS22_hz16 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS22_hz18 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B (70103078643054293 / 200000000000000000) (350515393215278811 / 1000000000000000000) (((13 / 25) : ℝ) * (kdot ((13 / 25)))) := bmul (bpoint ((13 / 25) : ℝ)) (lowCoarseS22_hz13 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS22_hz19 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B (62240495826963253 / 100000000000000000) (622404958269639877 / 1000000000000000000) (((√((1 : ℝ) - (((13 / 25) : ℝ)^2))) / Real.pi) + (((13 / 25) : ℝ) * (kdot ((13 / 25))))) := badd (lowCoarseS22_hz17 hx hc) (lowCoarseS22_hz18 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS22_hz20 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B (62240495826963253 / 100000000000000000) (622404958269639877 / 1000000000000000000) (kappa ((13 / 25))) := by rw [kappa_eq]; exact (lowCoarseS22_hz19 hx hc)

theorem lowCoarseS22_hz21 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B (338904041188233601 / 500000000000000000) (42363005148529649 / 62500000000000000) (kdot ((53 / 100))) := by
    constructor
    · apply bkdot_lower (q := (554246824513826269 / 1000000000000000000)) (a := (126524470181512309 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (138561706128456567 / 250000000000000000)) (a := (101219576145207591 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS22_hz22 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B (2809 / 10000) (2809 / 10000) (((53 / 100) : ℝ)^2) := bsq (bpoint ((53 / 100) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS22_hz23 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B (7191 / 10000) (7191 / 10000) ((1 : ℝ) - (((53 / 100) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS22_hz22 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS22_hz24 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B (84799764150615419 / 100000000000000000) (847997641506154191 / 1000000000000000000) (√((1 : ℝ) - (((53 / 100) : ℝ)^2))) := bsqrt (lowCoarseS22_hz23 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS22_hz25 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B (16870377046996679 / 62500000000000000) (53985206550389373 / 200000000000000000) ((√((1 : ℝ) - (((53 / 100) : ℝ)^2))) / Real.pi) := bdiv (lowCoarseS22_hz24 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS22_hz26 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B (359238283659527617 / 1000000000000000000) (11226196364360357 / 31250000000000000) (((53 / 100) : ℝ) * (kdot ((53 / 100)))) := bmul (bpoint ((53 / 100) : ℝ)) (lowCoarseS22_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS22_hz27 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B (629164316411474481 / 1000000000000000000) (629164316411478289 / 1000000000000000000) (((√((1 : ℝ) - (((53 / 100) : ℝ)^2))) / Real.pi) + (((53 / 100) : ℝ) * (kdot ((53 / 100))))) := badd (lowCoarseS22_hz25 hx hc) (lowCoarseS22_hz26 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS22_hz28 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B (629164316411474481 / 1000000000000000000) (629164316411478289 / 1000000000000000000) (kappa ((53 / 100))) := by rw [kappa_eq]; exact (lowCoarseS22_hz27 hx hc)

theorem lowCoarseS22_hz29 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B (62240495826963253 / 100000000000000000) (629164316411478289 / 1000000000000000000) (kappa c) := bkappa (lowCoarseS22_hz1 hx hc) (by norm_num) (by norm_num) (lowCoarseS22_hz20 hx hc).1 (lowCoarseS22_hz28 hx hc).2

theorem lowCoarseS22_hz30 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B (370835683588521711 / 1000000000000000000) (37759504173036747 / 100000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (lowCoarseS22_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS22_hz31 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B (370835683588521711 / 500000000000000000) (37759504173036747 / 50000000000000000) ((2 : ℝ) * ((1 : ℝ) - (kappa c))) := bmul (bpoint (2 : ℝ)) (lowCoarseS22_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS22_hz32 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B 0 (1 / 8000000) ((8 : ℝ) * (x^2)) := bmul (bpoint (8 : ℝ)) (lowCoarseS22_hz7 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS22_hz33 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B (370835621088521711 / 500000000000000000) (37759504173036747 / 50000000000000000) (((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2))) := bsub (lowCoarseS22_hz31 hx hc) (lowCoarseS22_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS22_hz34 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B (86120336865170437 / 100000000000000000) (217254183426455413 / 250000000000000000) (√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) := bsqrt (lowCoarseS22_hz33 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS22_hz35 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B (6782329983125268139 / 250000000000000000) (13564659966250536279 / 500000000000000000) ((2 : ℝ) * (√(184 : ℝ))) := bmul (bpoint (2 : ℝ)) (lowCoarseS22_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS22_hz36 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B 0 (678232998312527 / 200000000000000000) (((2 : ℝ) * (√(184 : ℝ))) * x) := bmul (lowCoarseS22_hz35 hx hc) (lowCoarseS22_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS22_hz37 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B (171562440732028347 / 200000000000000000) (217254183426455413 / 250000000000000000) ((√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) - (((2 : ℝ) * (√(184 : ℝ))) * x)) := bsub (lowCoarseS22_hz34 hx hc) (lowCoarseS22_hz36 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS22_hz38 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B (171562440732028347 / 200000000000000000) (217254183426455413 / 250000000000000000) (ndm x c) := by
    convert (lowCoarseS22_hz37 hx hc) using 1 <;>
      norm_num [ndm] <;> ring

theorem lowCoarseS22_hz39 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B 1 (1003394039991562637 / 1000000000000000000) ((nap x)^2) := bsq (lowCoarseS22_hz6 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS22_hz40 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B 2 (1003394039991562637 / 500000000000000000) ((2 : ℝ) * ((nap x)^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS22_hz39 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS22_hz41 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B (735841776748268481 / 1000000000000000000) (377595041730367471 / 500000000000000000) ((ndm x c)^2) := bsq (lowCoarseS22_hz38 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS22_hz42 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B (622404958269632529 / 500000000000000000) (1270946303234856793 / 1000000000000000000) (((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) := bsub (lowCoarseS22_hz40 hx hc) (lowCoarseS22_hz41 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS22_hz43 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B (199322335762284863 / 200000000000000000) 1 ((nam x)^2) := bsq (lowCoarseS22_hz12 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS22_hz44 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B (199322335762284863 / 100000000000000000) 2 ((2 : ℝ) * ((nam x)^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS22_hz43 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS22_hz45 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B (622404958269632529 / 1000000000000000000) (159408414813908327 / 250000000000000000) ((((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) / ((2 : ℝ) * ((nam x)^2))) := bdiv (lowCoarseS22_hz42 hx hc) (lowCoarseS22_hz44 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS22_hz46 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B (622404958269632529 / 1000000000000000000) (159408414813908327 / 250000000000000000) (nc1 x c) := by
    convert (lowCoarseS22_hz45 hx hc) using 1 <;>
      norm_num [nc1] <;> ring

theorem lowCoarseS22_hz47 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B (674068063875522049 / 1000000000000000000) (42363005148529649 / 62500000000000000) (kdot c) := bkdot (lowCoarseS22_hz1 hx hc) (lowCoarseS22_hz13 hx hc).1 (lowCoarseS22_hz21 hx hc).2

theorem lowCoarseS22_hz48 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B (17846107048461717 / 25000000000000000) (71384428193846869 / 100000000000000000) (kdot ((622404958269632529 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (482429113908555249 / 1000000000000000000)) (a := (112373087705602363 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (30151819619284703 / 62500000000000000)) (a := (224746175411204719 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS22_hz49 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B (360043313591355999 / 500000000000000000) (720086627182712003 / 1000000000000000000) (kdot ((159408414813908327 / 250000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (470398087300758183 / 1000000000000000000)) (a := (54960862230270807 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (235199043650379091 / 500000000000000000)) (a := (8793737956843329 / 20000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS22_hz50 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B (17846107048461717 / 25000000000000000) (720086627182712003 / 1000000000000000000) (kdot (nc1 x c)) := bkdot (lowCoarseS22_hz46 hx hc) (lowCoarseS22_hz48 hx hc).1 (lowCoarseS22_hz49 hx hc).2

theorem lowCoarseS22_hz51 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B (169 / 625) (2809 / 10000) (c^2) := bsq (lowCoarseS22_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS22_hz52 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B (7191 / 10000) (456 / 625) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS22_hz51 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS22_hz53 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B (84799764150615419 / 100000000000000000) (854166260162504897 / 1000000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (lowCoarseS22_hz52 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS22_hz54 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B (57160812838106239 / 100000000000000000) (57896079483143217 / 100000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (lowCoarseS22_hz53 hx hc) (lowCoarseS22_hz47 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS22_hz55 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B (57160812838106239 / 100000000000000000) (57896079483143217 / 100000000000000000) (npa c) := by
    convert (lowCoarseS22_hz54 hx hc) using 1 <;>
      norm_num [npa] <;> ring

theorem lowCoarseS22_hz56 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B (16870377046996679 / 62500000000000000) (135944782527180533 / 500000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (lowCoarseS22_hz53 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS22_hz57 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B (70103078643054293 / 200000000000000000) (11226196364360357 / 31250000000000000) (c * (kdot c)) := bmul (lowCoarseS22_hz1 hx hc) (lowCoarseS22_hz47 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS22_hz58 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B (-1116403136344807 / 12500000000000000) (-78625828160910399 / 1000000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (lowCoarseS22_hz56 hx hc) (lowCoarseS22_hz57 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS22_hz59 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B (-1116403136344807 / 12500000000000000) (-78625828160910399 / 1000000000000000000) (npp c) := by
    convert (lowCoarseS22_hz58 hx hc) using 1 <;>
      norm_num [npp] <;> ring

theorem lowCoarseS22_hz60 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B 0 (23 / 4000) ((46 : ℝ) * x) := bmul (bpoint (46 : ℝ)) (lowCoarseS22_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS22_hz61 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B (9591663046625439083 / 1000000000000000000) (2399353261656359771 / 250000000000000000) ((√(92 : ℝ)) + ((46 : ℝ) * x)) := badd (lowCoarseS22_hz3 hx hc) (lowCoarseS22_hz60 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS22_hz62 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B (28774989139876317249 / 250000000000000000) (7198059784969079313 / 62500000000000000) ((12 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (bpoint (12 : ℝ)) (lowCoarseS22_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS22_hz63 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B 0 (14396119569938159 / 1000000000000000000) (((12 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS22_hz62 hx hc) (lowCoarseS22_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS22_hz64 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B 0 (14396119569938159 / 1000000000000000000) (nr1 x) := by
    convert (lowCoarseS22_hz63 hx hc) using 1 <;>
      norm_num [nr1] <;> ring

theorem lowCoarseS22_hz65 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B (9591663046625439083 / 125000000000000000) (2399353261656359771 / 31250000000000000) ((8 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (bpoint (8 : ℝ)) (lowCoarseS22_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS22_hz66 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B 0 (59983831541409 / 6250000000000000) (((8 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS22_hz65 hx hc) (lowCoarseS22_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS22_hz67 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B 0 (59983831541409 / 6250000000000000) (nrpp x) := by
    convert (lowCoarseS22_hz66 hx hc) using 1 <;>
      norm_num [nrpp] <;> ring

theorem lowCoarseS22_hz68 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B 0 (847791247890659 / 500000000000000000) (ne0 x) := by
    convert (lowCoarseS22_hz4 hx hc) using 1 <;>
      norm_num [ne0] <;> ring

theorem lowCoarseS22_hz69 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B (57160812838106239 / 100000000000000000) (593356914401370329 / 1000000000000000000) ((npa c) + (nr1 x)) := badd (lowCoarseS22_hz55 hx hc) (lowCoarseS22_hz64 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS22_hz70 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B (57160812838106239 / 100000000000000000) (594364718100440227 / 1000000000000000000) (((npa c) + (nr1 x)) / (nam x)) := bdiv (lowCoarseS22_hz69 hx hc) (lowCoarseS22_hz12 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS22_hz71 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B (57160812838106239 / 100000000000000000) (119212060119244309 / 200000000000000000) ((((npa c) + (nr1 x)) / (nam x)) + (ne0 x)) := badd (lowCoarseS22_hz70 hx hc) (lowCoarseS22_hz68 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS22_hz72 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B (57160812838106239 / 100000000000000000) (119212060119244309 / 200000000000000000) (nlam x c) := by
    convert (lowCoarseS22_hz71 hx hc) using 1 <;>
      norm_num [nlam] <;> ring

theorem lowCoarseS22_hz73 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS22_hz74 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B 0 (59947894041409 / 100000000000000000) ((√(23 : ℝ)) * x) := bmul (lowCoarseS22_hz73 hx hc) (lowCoarseS22_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS22_hz75 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B (1 / 2) (50059947894041409 / 100000000000000000) (((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)) := badd (bpoint ((1 / 2) : ℝ)) (lowCoarseS22_hz74 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS22_hz76 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B (176776695296636881 / 250000000000000000) (353765274914177413 / 500000000000000000) (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) := bsqrt (lowCoarseS22_hz75 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS22_hz77 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B 0 (59947894041409 / 50000000000000000) ((√(92 : ℝ)) * x) := bmul (lowCoarseS22_hz3 hx hc) (lowCoarseS22_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS22_hz78 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B (176776695296636881 / 250000000000000000) (354364753854591503 / 500000000000000000) ((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x)) := badd (lowCoarseS22_hz76 hx hc) (lowCoarseS22_hz77 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS22_hz79 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B (499999999999999999 / 1000000000000000000) (251148757548850447 / 500000000000000000) (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2) := bsq (lowCoarseS22_hz78 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS22_hz80 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B (499999999999999999 / 125000000000000000) (251148757548850447 / 62500000000000000) ((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) := bmul (bpoint (8 : ℝ)) (lowCoarseS22_hz79 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS22_hz81 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B (7673330437300351251 / 200000000000000000) (1928302689874485209 / 50000000000000000) (((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (lowCoarseS22_hz80 hx hc) (lowCoarseS22_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS22_hz82 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B 0 (2410378362343107 / 500000000000000000) ((((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS22_hz81 hx hc) (lowCoarseS22_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS22_hz83 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B 0 (2410378362343107 / 500000000000000000) (nrs x) := by
    convert (lowCoarseS22_hz82 hx hc) using 1 <;>
      norm_num [nrs] <;> ring

theorem lowCoarseS22_hz84 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B (-1116403136344807 / 12500000000000000) (-69028415114284959 / 1000000000000000000) ((npp c) + (nrpp x)) := badd (lowCoarseS22_hz59 hx hc) (lowCoarseS22_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS22_hz85 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B (-2572502300885547 / 40000000000000000) (-34514207557142479 / 1000000000000000000) (if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) := bweaken (bfirst (lowCoarseS22_hz84 hx hc) (lowCoarseS22_hz50 hx hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem lowCoarseS22_hz86 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B (163367926215650551 / 500000000000000000) (355287881946857987 / 1000000000000000000) ((nlam x c)^2) := bsq (lowCoarseS22_hz72 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS22_hz87 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B (387387932078623009 / 1000000000000000000) (81315336683145817 / 200000000000000000) ((nc1 x c)^2) := bsq (lowCoarseS22_hz46 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS22_hz88 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B (118684663316854183 / 200000000000000000) (612612067921376991 / 1000000000000000000) ((1 : ℝ) - ((nc1 x c)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS22_hz87 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS22_hz89 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B (385169870506595737 / 500000000000000000) (782695386418865377 / 1000000000000000000) (√((1 : ℝ) - ((nc1 x c)^2))) := bsqrt (lowCoarseS22_hz88 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS22_hz90 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B (2420093671135306281 / 1000000000000000000) (307363759496516487 / 125000000000000000) (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))) := bmul pi_mem (lowCoarseS22_hz89 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS22_hz91 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B (8304895317850477 / 62500000000000000) (73403745934384953 / 500000000000000000) (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2))))) := bdiv (lowCoarseS22_hz86 hx hc) (lowCoarseS22_hz90 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS22_hz92 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B (68565767563468957 / 1000000000000000000) (112293284311627427 / 1000000000000000000) ((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) := badd (lowCoarseS22_hz85 hx hc) (lowCoarseS22_hz91 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS22_hz93 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B 0 (2875000000001 / 1000000000000000000) ((ne0 x)^2) := bsq (lowCoarseS22_hz68 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS22_hz94 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B (68565767563468957 / 1000000000000000000) (28074039827906857 / 250000000000000000) (((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) + ((ne0 x)^2)) := badd (lowCoarseS22_hz92 hx hc) (lowCoarseS22_hz93 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS22_hz95 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B (68565767563468957 / 1000000000000000000) (58558458018156821 / 500000000000000000) ((((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) + ((ne0 x)^2)) + (nrs x)) := badd (lowCoarseS22_hz94 hx hc) (lowCoarseS22_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS22_hz96 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B (68565767563468957 / 1000000000000000000) (58558458018156821 / 500000000000000000) (nu x c) := by
    convert (lowCoarseS22_hz95 hx hc) using 1 <;>
      norm_num [nu] <;> ring

theorem lowCoarseS22_hz97 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B (-9890966395421 / 100000000000000) (-78625828160910399 / 1000000000000000000) ((npp c) - (nrpp x)) := bsub (lowCoarseS22_hz59 hx hc) (lowCoarseS22_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS22_hz98 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B (-9890966395421 / 100000000000000) (-78625828160910399 / 1000000000000000000) (min ((npp c) - (nrpp x)) (0 : ℝ)) := bweaken (bmin (lowCoarseS22_hz97 hx hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem lowCoarseS22_hz99 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B (-14244705262512509 / 200000000000000000) (-56126597845342513 / 1000000000000000000) ((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) := bmul (lowCoarseS22_hz50 hx hc) (lowCoarseS22_hz98 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS22_hz100 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B (-35613200656281273 / 500000000000000000) (-56126597845342513 / 1000000000000000000) (((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) - ((ne0 x)^2)) := bsub (lowCoarseS22_hz99 hx hc) (lowCoarseS22_hz93 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS22_hz101 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B (-1901178950931219 / 25000000000000000) (-56126597845342513 / 1000000000000000000) ((((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) - ((ne0 x)^2)) - (nrs x)) := bsub (lowCoarseS22_hz100 hx hc) (lowCoarseS22_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS22_hz102 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B (-1901178950931219 / 25000000000000000) (-56126597845342513 / 1000000000000000000) (nl x c) := by
    convert (lowCoarseS22_hz101 hx hc) using 1 <;>
      norm_num [nl] <;> ring

theorem lowCoarseS22_hz103 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B 0 (58558458018156821 / 500000000000000000) |(nu x c)| := bweaken (babs (lowCoarseS22_hz96 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS22_hz104 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B 0 (1901178950931219 / 25000000000000000) |(nl x c)| := bweaken (babs (lowCoarseS22_hz102 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS22_hz105 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B 0 (58558458018156821 / 500000000000000000) (max |(nu x c)| |(nl x c)|) := bweaken (bmax (lowCoarseS22_hz103 hx hc) (lowCoarseS22_hz104 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS22_hz106 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) : B 0 (58558458018156821 / 500000000000000000) (ns x c) := by
    convert (lowCoarseS22_hz105 hx hc) using 1 <;>
      norm_num [ns] <;> ring

theorem lowCoarseS22 {x c : ℝ}
    (hx : B 0 (1/8000) x) (hc : B (13 / 25) (53 / 100) c) :
    0 < nam x ∧ 0 ≤ ndm x c ∧ ndm x c ^ 2 ≤ 2 * nap x ^ 2 ∧ nc1 x c < 1 ∧
    0 ≤ npa c - nr1 x ∧ ne0 x ≤ (npa c - nr1 x) / nap x ∧ ns x c ≤ (1 / 5) := by
  refine ⟨lt_of_lt_of_le (by norm_num) (lowCoarseS22_hz12 hx hc).1,
    le_trans (by norm_num) (lowCoarseS22_hz38 hx hc).1, ?_,
    lt_of_le_of_lt (lowCoarseS22_hz46 hx hc).2 (by norm_num), ?_, ?_, (lowCoarseS22_hz106 hx hc).2.trans (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (lowCoarseS22_hz38 hx hc).1) (lowCoarseS22_hz38 hx hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) (lowCoarseS22_hz6 hx hc).1 2
    nlinarith only [h1,h2]
  · linarith only [(lowCoarseS22_hz55 hx hc).1,(lowCoarseS22_hz64 hx hc).2]
  · have hap : 0 < nap x := lt_of_lt_of_le (by norm_num) (lowCoarseS22_hz6 hx hc).1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul (lowCoarseS22_hz68 hx hc).2 (lowCoarseS22_hz6 hx hc).2 (le_trans (by norm_num) (lowCoarseS22_hz6 hx hc).1) (by norm_num)
    linarith only [h,(lowCoarseS22_hz55 hx hc).1,(lowCoarseS22_hz64 hx hc).2]

theorem lowCoarseS23_hz0 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B 0 (1 / 8000) x := hx

theorem lowCoarseS23_hz1 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B (53 / 100) (27 / 50) c := hc

theorem lowCoarseS23_hz2 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B (6782329983125268139 / 500000000000000000) (13564659966250536279 / 1000000000000000000) (√(184 : ℝ)) := bsqrt (bpoint (184 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS23_hz3 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS23_hz4 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B 0 (847791247890659 / 500000000000000000) ((√(184 : ℝ)) * x) := bmul (lowCoarseS23_hz2 hx hc) (lowCoarseS23_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS23_hz5 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B 1 (500847791247890659 / 500000000000000000) ((1 : ℝ) + ((√(184 : ℝ)) * x)) := badd (bpoint (1 : ℝ)) (lowCoarseS23_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS23_hz6 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B 1 (500847791247890659 / 500000000000000000) (nap x) := by
    convert (lowCoarseS23_hz5 hx hc) using 1 <;>
      norm_num [nap] <;> ring

theorem lowCoarseS23_hz7 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B 0 (1 / 64000000) (x^2) := bsq (lowCoarseS23_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS23_hz8 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B 0 (1 / 32000000) ((2 : ℝ) * (x^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS23_hz7 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS23_hz9 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B (31999999 / 32000000) 1 ((1 : ℝ) - ((2 : ℝ) * (x^2))) := bsub (bpoint (1 : ℝ)) (lowCoarseS23_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS23_hz10 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B (999999984374999877 / 1000000000000000000) 1 (√((1 : ℝ) - ((2 : ℝ) * (x^2)))) := bsqrt (lowCoarseS23_hz9 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS23_hz11 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B (998304401879218559 / 1000000000000000000) 1 ((√((1 : ℝ) - ((2 : ℝ) * (x^2)))) - ((√(184 : ℝ)) * x)) := bsub (lowCoarseS23_hz10 hx hc) (lowCoarseS23_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS23_hz12 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B (998304401879218559 / 1000000000000000000) 1 (nam x) := by
    convert (lowCoarseS23_hz11 hx hc) using 1 <;>
      norm_num [nam] <;> ring

theorem lowCoarseS23_hz13 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B (338904041188233601 / 500000000000000000) (42363005148529649 / 62500000000000000) (kdot ((53 / 100))) := by
    constructor
    · apply bkdot_lower (q := (554246824513826269 / 1000000000000000000)) (a := (126524470181512309 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (138561706128456567 / 250000000000000000)) (a := (101219576145207591 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS23_hz14 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B (2809 / 10000) (2809 / 10000) (((53 / 100) : ℝ)^2) := bsq (bpoint ((53 / 100) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS23_hz15 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B (7191 / 10000) (7191 / 10000) ((1 : ℝ) - (((53 / 100) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS23_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS23_hz16 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B (84799764150615419 / 100000000000000000) (847997641506154191 / 1000000000000000000) (√((1 : ℝ) - (((53 / 100) : ℝ)^2))) := bsqrt (lowCoarseS23_hz15 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS23_hz17 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B (16870377046996679 / 62500000000000000) (53985206550389373 / 200000000000000000) ((√((1 : ℝ) - (((53 / 100) : ℝ)^2))) / Real.pi) := bdiv (lowCoarseS23_hz16 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS23_hz18 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B (359238283659527617 / 1000000000000000000) (11226196364360357 / 31250000000000000) (((53 / 100) : ℝ) * (kdot ((53 / 100)))) := bmul (bpoint ((53 / 100) : ℝ)) (lowCoarseS23_hz13 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS23_hz19 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B (629164316411474481 / 1000000000000000000) (629164316411478289 / 1000000000000000000) (((√((1 : ℝ) - (((53 / 100) : ℝ)^2))) / Real.pi) + (((53 / 100) : ℝ) * (kdot ((53 / 100))))) := badd (lowCoarseS23_hz17 hx hc) (lowCoarseS23_hz18 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS23_hz20 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B (629164316411474481 / 1000000000000000000) (629164316411478289 / 1000000000000000000) (kappa ((53 / 100))) := by rw [kappa_eq]; exact (lowCoarseS23_hz19 hx hc)

theorem lowCoarseS23_hz21 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B (340787885684049643 / 500000000000000000) (340787885684051451 / 500000000000000000) (kdot ((27 / 50))) := by
    constructor
    · apply bkdot_lower (q := (68316965625002639 / 125000000000000000)) (a := (50017960869748799 / 100000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (546535725000021111 / 1000000000000000000)) (a := (500179608697482311 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS23_hz22 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B (729 / 2500) (729 / 2500) (((27 / 50) : ℝ)^2) := bsq (bpoint ((27 / 50) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS23_hz23 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B (1771 / 2500) (1771 / 2500) ((1 : ℝ) - (((27 / 50) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS23_hz22 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS23_hz24 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B (841665016500032511 / 1000000000000000000) (821938492675813 / 976562500000000) (√((1 : ℝ) - (((27 / 50) : ℝ)^2))) := bsqrt (lowCoarseS23_hz23 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS23_hz25 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B (133955147803501823 / 500000000000000000) (267910295607003647 / 1000000000000000000) ((√((1 : ℝ) - (((27 / 50) : ℝ)^2))) / Real.pi) := bdiv (lowCoarseS23_hz24 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS23_hz26 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B (184025458269386807 / 500000000000000000) (23003182283673473 / 62500000000000000) (((27 / 50) : ℝ) * (kdot ((27 / 50)))) := bmul (bpoint ((27 / 50) : ℝ)) (lowCoarseS23_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS23_hz27 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B (31798060607288863 / 50000000000000000) (127192242429155843 / 200000000000000000) (((√((1 : ℝ) - (((27 / 50) : ℝ)^2))) / Real.pi) + (((27 / 50) : ℝ) * (kdot ((27 / 50))))) := badd (lowCoarseS23_hz25 hx hc) (lowCoarseS23_hz26 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS23_hz28 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B (31798060607288863 / 50000000000000000) (127192242429155843 / 200000000000000000) (kappa ((27 / 50))) := by rw [kappa_eq]; exact (lowCoarseS23_hz27 hx hc)

theorem lowCoarseS23_hz29 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B (629164316411474481 / 1000000000000000000) (127192242429155843 / 200000000000000000) (kappa c) := bkappa (lowCoarseS23_hz1 hx hc) (by norm_num) (by norm_num) (lowCoarseS23_hz20 hx hc).1 (lowCoarseS23_hz28 hx hc).2

theorem lowCoarseS23_hz30 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B (72807757570844157 / 200000000000000000) (370835683588525519 / 1000000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (lowCoarseS23_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS23_hz31 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B (72807757570844157 / 100000000000000000) (370835683588525519 / 500000000000000000) ((2 : ℝ) * ((1 : ℝ) - (kappa c))) := bmul (bpoint (2 : ℝ)) (lowCoarseS23_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS23_hz32 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B 0 (1 / 8000000) ((8 : ℝ) * (x^2)) := bmul (bpoint (8 : ℝ)) (lowCoarseS23_hz7 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS23_hz33 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B (72807745070844157 / 100000000000000000) (370835683588525519 / 500000000000000000) (((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2))) := bsub (lowCoarseS23_hz31 hx hc) (lowCoarseS23_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS23_hz34 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B (426637272958083671 / 500000000000000000) (861203441224575599 / 1000000000000000000) (√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) := bsqrt (lowCoarseS23_hz33 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS23_hz35 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B (6782329983125268139 / 250000000000000000) (13564659966250536279 / 500000000000000000) ((2 : ℝ) * (√(184 : ℝ))) := bmul (bpoint (2 : ℝ)) (lowCoarseS23_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS23_hz36 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B 0 (678232998312527 / 200000000000000000) (((2 : ℝ) * (√(184 : ℝ))) * x) := bmul (lowCoarseS23_hz35 hx hc) (lowCoarseS23_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS23_hz37 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B (849883380924604707 / 1000000000000000000) (861203441224575599 / 1000000000000000000) ((√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) - (((2 : ℝ) * (√(184 : ℝ))) * x)) := bsub (lowCoarseS23_hz34 hx hc) (lowCoarseS23_hz36 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS23_hz38 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B (849883380924604707 / 1000000000000000000) (861203441224575599 / 1000000000000000000) (ndm x c) := by
    convert (lowCoarseS23_hz37 hx hc) using 1 <;>
      norm_num [ndm] <;> ring

theorem lowCoarseS23_hz39 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B 1 (1003394039991562637 / 1000000000000000000) ((nap x)^2) := bsq (lowCoarseS23_hz6 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS23_hz40 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B 2 (1003394039991562637 / 500000000000000000) ((2 : ℝ) * ((nap x)^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS23_hz39 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS23_hz41 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B (722301761171836747 / 1000000000000000000) (741671367177051039 / 1000000000000000000) ((ndm x c)^2) := bsq (lowCoarseS23_hz38 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS23_hz42 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B (1258328632822948961 / 1000000000000000000) (1284486318811288527 / 1000000000000000000) (((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) := bsub (lowCoarseS23_hz40 hx hc) (lowCoarseS23_hz41 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS23_hz43 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B (199322335762284863 / 200000000000000000) 1 ((nam x)^2) := bsq (lowCoarseS23_hz12 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS23_hz44 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B (199322335762284863 / 100000000000000000) 2 ((2 : ℝ) * ((nam x)^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS23_hz43 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS23_hz45 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B (7864553955143431 / 12500000000000000) (322213341996751509 / 500000000000000000) ((((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) / ((2 : ℝ) * ((nam x)^2))) := bdiv (lowCoarseS23_hz42 hx hc) (lowCoarseS23_hz44 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS23_hz46 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B (7864553955143431 / 12500000000000000) (322213341996751509 / 500000000000000000) (nc1 x c) := by
    convert (lowCoarseS23_hz45 hx hc) using 1 <;>
      norm_num [nc1] <;> ring

theorem lowCoarseS23_hz47 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B (338904041188233601 / 500000000000000000) (340787885684051451 / 500000000000000000) (kdot c) := bkdot (lowCoarseS23_hz1 hx hc) (lowCoarseS23_hz13 hx hc).1 (lowCoarseS23_hz21 hx hc).2

theorem lowCoarseS23_hz48 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B (716602745519152003 / 1000000000000000000) (71660274551915201 / 100000000000000000) (kdot ((7864553955143431 / 12500000000000000))) := by
    constructor
    · apply bkdot_lower (q := (477098788889526803 / 1000000000000000000)) (a := (44515936636227459 / 100000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (238549394444763401 / 500000000000000000)) (a := (445159366362274581 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS23_hz49 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B (28916156401119201 / 40000000000000000) (180725977506995007 / 250000000000000000) (kdot ((322213341996751509 / 500000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (465004679360037991 / 1000000000000000000)) (a := (108815380074319291 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (46500467936003799 / 100000000000000000)) (a := (10881538007431929 / 25000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS23_hz50 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B (716602745519152003 / 1000000000000000000) (180725977506995007 / 250000000000000000) (kdot (nc1 x c)) := bkdot (lowCoarseS23_hz46 hx hc) (lowCoarseS23_hz48 hx hc).1 (lowCoarseS23_hz49 hx hc).2

theorem lowCoarseS23_hz51 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B (2809 / 10000) (729 / 2500) (c^2) := bsq (lowCoarseS23_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS23_hz52 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B (1771 / 2500) (7191 / 10000) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS23_hz51 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS23_hz53 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B (841665016500032511 / 1000000000000000000) (847997641506154191 / 1000000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (lowCoarseS23_hz52 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS23_hz54 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B (570487350837244663 / 1000000000000000000) (577974646627889037 / 1000000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (lowCoarseS23_hz53 hx hc) (lowCoarseS23_hz47 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS23_hz55 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B (570487350837244663 / 1000000000000000000) (577974646627889037 / 1000000000000000000) (npa c) := by
    convert (lowCoarseS23_hz54 hx hc) using 1 <;>
      norm_num [npa] <;> ring

theorem lowCoarseS23_hz56 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B (133955147803501823 / 500000000000000000) (53985206550389373 / 200000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (lowCoarseS23_hz53 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS23_hz57 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B (359238283659527617 / 1000000000000000000) (23003182283673473 / 62500000000000000) (c * (kdot c)) := bmul (lowCoarseS23_hz1 hx hc) (lowCoarseS23_hz47 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS23_hz58 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B (-50070310465885961 / 500000000000000000) (-5582015681723797 / 62500000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (lowCoarseS23_hz56 hx hc) (lowCoarseS23_hz57 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS23_hz59 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B (-50070310465885961 / 500000000000000000) (-5582015681723797 / 62500000000000000) (npp c) := by
    convert (lowCoarseS23_hz58 hx hc) using 1 <;>
      norm_num [npp] <;> ring

theorem lowCoarseS23_hz60 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B 0 (23 / 4000) ((46 : ℝ) * x) := bmul (bpoint (46 : ℝ)) (lowCoarseS23_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS23_hz61 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B (9591663046625439083 / 1000000000000000000) (2399353261656359771 / 250000000000000000) ((√(92 : ℝ)) + ((46 : ℝ) * x)) := badd (lowCoarseS23_hz3 hx hc) (lowCoarseS23_hz60 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS23_hz62 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B (28774989139876317249 / 250000000000000000) (7198059784969079313 / 62500000000000000) ((12 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (bpoint (12 : ℝ)) (lowCoarseS23_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS23_hz63 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B 0 (14396119569938159 / 1000000000000000000) (((12 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS23_hz62 hx hc) (lowCoarseS23_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS23_hz64 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B 0 (14396119569938159 / 1000000000000000000) (nr1 x) := by
    convert (lowCoarseS23_hz63 hx hc) using 1 <;>
      norm_num [nr1] <;> ring

theorem lowCoarseS23_hz65 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B (9591663046625439083 / 125000000000000000) (2399353261656359771 / 31250000000000000) ((8 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (bpoint (8 : ℝ)) (lowCoarseS23_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS23_hz66 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B 0 (59983831541409 / 6250000000000000) (((8 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS23_hz65 hx hc) (lowCoarseS23_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS23_hz67 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B 0 (59983831541409 / 6250000000000000) (nrpp x) := by
    convert (lowCoarseS23_hz66 hx hc) using 1 <;>
      norm_num [nrpp] <;> ring

theorem lowCoarseS23_hz68 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B 0 (847791247890659 / 500000000000000000) (ne0 x) := by
    convert (lowCoarseS23_hz4 hx hc) using 1 <;>
      norm_num [ne0] <;> ring

theorem lowCoarseS23_hz69 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B (570487350837244663 / 1000000000000000000) (148092691549456799 / 250000000000000000) ((npa c) + (nr1 x)) := badd (lowCoarseS23_hz55 hx hc) (lowCoarseS23_hz64 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS23_hz70 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B (570487350837244663 / 1000000000000000000) (593376894945812443 / 1000000000000000000) (((npa c) + (nr1 x)) / (nam x)) := bdiv (lowCoarseS23_hz69 hx hc) (lowCoarseS23_hz12 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS23_hz71 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B (570487350837244663 / 1000000000000000000) (595072477441593761 / 1000000000000000000) ((((npa c) + (nr1 x)) / (nam x)) + (ne0 x)) := badd (lowCoarseS23_hz70 hx hc) (lowCoarseS23_hz68 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS23_hz72 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B (570487350837244663 / 1000000000000000000) (595072477441593761 / 1000000000000000000) (nlam x c) := by
    convert (lowCoarseS23_hz71 hx hc) using 1 <;>
      norm_num [nlam] <;> ring

theorem lowCoarseS23_hz73 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS23_hz74 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B 0 (59947894041409 / 100000000000000000) ((√(23 : ℝ)) * x) := bmul (lowCoarseS23_hz73 hx hc) (lowCoarseS23_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS23_hz75 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B (1 / 2) (50059947894041409 / 100000000000000000) (((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)) := badd (bpoint ((1 / 2) : ℝ)) (lowCoarseS23_hz74 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS23_hz76 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B (176776695296636881 / 250000000000000000) (353765274914177413 / 500000000000000000) (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) := bsqrt (lowCoarseS23_hz75 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS23_hz77 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B 0 (59947894041409 / 50000000000000000) ((√(92 : ℝ)) * x) := bmul (lowCoarseS23_hz3 hx hc) (lowCoarseS23_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS23_hz78 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B (176776695296636881 / 250000000000000000) (354364753854591503 / 500000000000000000) ((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x)) := badd (lowCoarseS23_hz76 hx hc) (lowCoarseS23_hz77 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS23_hz79 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B (499999999999999999 / 1000000000000000000) (251148757548850447 / 500000000000000000) (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2) := bsq (lowCoarseS23_hz78 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS23_hz80 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B (499999999999999999 / 125000000000000000) (251148757548850447 / 62500000000000000) ((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) := bmul (bpoint (8 : ℝ)) (lowCoarseS23_hz79 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS23_hz81 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B (7673330437300351251 / 200000000000000000) (1928302689874485209 / 50000000000000000) (((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (lowCoarseS23_hz80 hx hc) (lowCoarseS23_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS23_hz82 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B 0 (2410378362343107 / 500000000000000000) ((((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS23_hz81 hx hc) (lowCoarseS23_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS23_hz83 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B 0 (2410378362343107 / 500000000000000000) (nrs x) := by
    convert (lowCoarseS23_hz82 hx hc) using 1 <;>
      norm_num [nrs] <;> ring

theorem lowCoarseS23_hz84 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B (-50070310465885961 / 500000000000000000) (-4982177366309707 / 62500000000000000) ((npp c) + (nrpp x)) := badd (lowCoarseS23_hz59 hx hc) (lowCoarseS23_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS23_hz85 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B (-9049005803025963 / 125000000000000000) (-4982177366309707 / 125000000000000000) (if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) := bweaken (bfirst (lowCoarseS23_hz84 hx hc) (lowCoarseS23_hz50 hx hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem lowCoarseS23_hz86 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B (162727908732648739 / 500000000000000000) (88527813352119029 / 250000000000000000) ((nlam x c)^2) := bsq (lowCoarseS23_hz72 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS23_hz87 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B (15833909481820719 / 40000000000000000) (415285751042862199 / 1000000000000000000) ((nc1 x c)^2) := bsq (lowCoarseS23_hz46 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS23_hz88 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B (584714248957137801 / 1000000000000000000) (24166090518179281 / 40000000000000000) ((1 : ℝ) - ((nc1 x c)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS23_hz87 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS23_hz89 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B (764666102921489387 / 1000000000000000000) (77727232226194831 / 100000000000000000) (√((1 : ℝ) - ((nc1 x c)^2))) := bsqrt (lowCoarseS23_hz88 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS23_hz90 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B (2402269411387287791 / 1000000000000000000) (2441873017456815113 / 1000000000000000000) (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))) := bmul pi_mem (lowCoarseS23_hz89 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS23_hz91 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B (133281221070314403 / 1000000000000000000) (18425871164257771 / 125000000000000000) (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2))))) := bdiv (lowCoarseS23_hz86 hx hc) (lowCoarseS23_hz90 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS23_hz92 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B (60889174646106699 / 1000000000000000000) (420115431185877 / 3906250000000000) ((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) := badd (lowCoarseS23_hz85 hx hc) (lowCoarseS23_hz91 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS23_hz93 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B 0 (2875000000001 / 1000000000000000000) ((ne0 x)^2) := bsq (lowCoarseS23_hz68 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS23_hz94 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B (60889174646106699 / 1000000000000000000) (107552425383584513 / 1000000000000000000) (((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) + ((ne0 x)^2)) := badd (lowCoarseS23_hz92 hx hc) (lowCoarseS23_hz93 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS23_hz95 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B (60889174646106699 / 1000000000000000000) (112373182108270727 / 1000000000000000000) ((((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) + ((ne0 x)^2)) + (nrs x)) := badd (lowCoarseS23_hz94 hx hc) (lowCoarseS23_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS23_hz96 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B (60889174646106699 / 1000000000000000000) (112373182108270727 / 1000000000000000000) (nu x c) := by
    convert (lowCoarseS23_hz95 hx hc) using 1 <;>
      norm_num [nu] <;> ring

theorem lowCoarseS23_hz97 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B (-54869016989198681 / 500000000000000000) (-5582015681723797 / 62500000000000000) ((npp c) - (nrpp x)) := bsub (lowCoarseS23_hz59 hx hc) (lowCoarseS23_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS23_hz98 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B (-54869016989198681 / 500000000000000000) (-5582015681723797 / 62500000000000000) (min ((npp c) - (nrpp x)) (0 : ℝ)) := bweaken (bmin (lowCoarseS23_hz97 hx hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem lowCoarseS23_hz99 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B (-39665026920883391 / 500000000000000000) (-32000702104433871 / 500000000000000000) ((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) := bmul (lowCoarseS23_hz50 hx hc) (lowCoarseS23_hz98 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS23_hz100 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B (-79332928841766783 / 1000000000000000000) (-32000702104433871 / 500000000000000000) (((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) - ((ne0 x)^2)) := bsub (lowCoarseS23_hz99 hx hc) (lowCoarseS23_hz93 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS23_hz101 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B (-84153685566452997 / 1000000000000000000) (-32000702104433871 / 500000000000000000) ((((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) - ((ne0 x)^2)) - (nrs x)) := bsub (lowCoarseS23_hz100 hx hc) (lowCoarseS23_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS23_hz102 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B (-84153685566452997 / 1000000000000000000) (-32000702104433871 / 500000000000000000) (nl x c) := by
    convert (lowCoarseS23_hz101 hx hc) using 1 <;>
      norm_num [nl] <;> ring

theorem lowCoarseS23_hz103 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B 0 (112373182108270727 / 1000000000000000000) |(nu x c)| := bweaken (babs (lowCoarseS23_hz96 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS23_hz104 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B 0 (84153685566452997 / 1000000000000000000) |(nl x c)| := bweaken (babs (lowCoarseS23_hz102 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS23_hz105 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B 0 (112373182108270727 / 1000000000000000000) (max |(nu x c)| |(nl x c)|) := bweaken (bmax (lowCoarseS23_hz103 hx hc) (lowCoarseS23_hz104 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS23_hz106 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) : B 0 (112373182108270727 / 1000000000000000000) (ns x c) := by
    convert (lowCoarseS23_hz105 hx hc) using 1 <;>
      norm_num [ns] <;> ring

theorem lowCoarseS23 {x c : ℝ}
    (hx : B 0 (1/8000) x) (hc : B (53 / 100) (27 / 50) c) :
    0 < nam x ∧ 0 ≤ ndm x c ∧ ndm x c ^ 2 ≤ 2 * nap x ^ 2 ∧ nc1 x c < 1 ∧
    0 ≤ npa c - nr1 x ∧ ne0 x ≤ (npa c - nr1 x) / nap x ∧ ns x c ≤ (1 / 5) := by
  refine ⟨lt_of_lt_of_le (by norm_num) (lowCoarseS23_hz12 hx hc).1,
    le_trans (by norm_num) (lowCoarseS23_hz38 hx hc).1, ?_,
    lt_of_le_of_lt (lowCoarseS23_hz46 hx hc).2 (by norm_num), ?_, ?_, (lowCoarseS23_hz106 hx hc).2.trans (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (lowCoarseS23_hz38 hx hc).1) (lowCoarseS23_hz38 hx hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) (lowCoarseS23_hz6 hx hc).1 2
    nlinarith only [h1,h2]
  · linarith only [(lowCoarseS23_hz55 hx hc).1,(lowCoarseS23_hz64 hx hc).2]
  · have hap : 0 < nap x := lt_of_lt_of_le (by norm_num) (lowCoarseS23_hz6 hx hc).1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul (lowCoarseS23_hz68 hx hc).2 (lowCoarseS23_hz6 hx hc).2 (le_trans (by norm_num) (lowCoarseS23_hz6 hx hc).1) (by norm_num)
    linarith only [h,(lowCoarseS23_hz55 hx hc).1,(lowCoarseS23_hz64 hx hc).2]

end BstLean.BlueprintLow
