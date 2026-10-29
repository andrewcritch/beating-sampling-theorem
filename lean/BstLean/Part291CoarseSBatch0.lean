import BstLean.Part264bNormalize
namespace BstLean.BlueprintLow
open Real BstLean.Part130 BstLean.Part182 BstLean.Part197 BstLean.Part246 BstLean.Part255
open BstLean.Part264b
theorem lowCoarseS0_hz0 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B 0 (1 / 8000) x := hx

theorem lowCoarseS0_hz1 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B (3 / 10) (31 / 100) c := hc

theorem lowCoarseS0_hz2 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B (6782329983125268139 / 500000000000000000) (13564659966250536279 / 1000000000000000000) (√(184 : ℝ)) := bsqrt (bpoint (184 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS0_hz3 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS0_hz4 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B 0 (847791247890659 / 500000000000000000) ((√(184 : ℝ)) * x) := bmul (lowCoarseS0_hz2 hx hc) (lowCoarseS0_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS0_hz5 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B 1 (500847791247890659 / 500000000000000000) ((1 : ℝ) + ((√(184 : ℝ)) * x)) := badd (bpoint (1 : ℝ)) (lowCoarseS0_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS0_hz6 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B 1 (500847791247890659 / 500000000000000000) (nap x) := by
    convert (lowCoarseS0_hz5 hx hc) using 1 <;>
      norm_num [nap] <;> ring

theorem lowCoarseS0_hz7 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B 0 (1 / 64000000) (x^2) := bsq (lowCoarseS0_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS0_hz8 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B 0 (1 / 32000000) ((2 : ℝ) * (x^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS0_hz7 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS0_hz9 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B (31999999 / 32000000) 1 ((1 : ℝ) - ((2 : ℝ) * (x^2))) := bsub (bpoint (1 : ℝ)) (lowCoarseS0_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS0_hz10 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B (999999984374999877 / 1000000000000000000) 1 (√((1 : ℝ) - ((2 : ℝ) * (x^2)))) := bsqrt (lowCoarseS0_hz9 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS0_hz11 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B (998304401879218559 / 1000000000000000000) 1 ((√((1 : ℝ) - ((2 : ℝ) * (x^2)))) - ((√(184 : ℝ)) * x)) := bsub (lowCoarseS0_hz10 hx hc) (lowCoarseS0_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS0_hz12 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B (998304401879218559 / 1000000000000000000) 1 (nam x) := by
    convert (lowCoarseS0_hz11 hx hc) using 1 <;>
      norm_num [nam] <;> ring

theorem lowCoarseS0_hz13 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B (298493341436901877 / 500000000000000000) (298493344801815279 / 500000000000000000) (kdot ((3 / 10))) := by
    constructor
    · apply bkdot_lower (q := (91724923213167851 / 125000000000000000)) (a := (79131479773906983 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (733799385705342807 / 1000000000000000000)) (a := (316525913810034321 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS0_hz14 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B (9 / 100) (9 / 100) (((3 / 10) : ℝ)^2) := bsq (bpoint ((3 / 10) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS0_hz15 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B (91 / 100) (91 / 100) ((1 : ℝ) - (((3 / 10) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS0_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS0_hz16 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B (953939201416945649 / 1000000000000000000) (19078784028338913 / 20000000000000000) (√((1 : ℝ) - (((3 / 10) : ℝ)^2))) := bsqrt (lowCoarseS0_hz15 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS0_hz17 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B (151824139314642067 / 500000000000000000) (60729655725856827 / 200000000000000000) ((√((1 : ℝ) - (((3 / 10) : ℝ)^2))) / Real.pi) := bdiv (lowCoarseS0_hz16 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS0_hz18 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B (89548002431070563 / 500000000000000000) (11193500430068073 / 62500000000000000) (((3 / 10) : ℝ) * (kdot ((3 / 10)))) := bmul (bpoint ((3 / 10) : ℝ)) (lowCoarseS0_hz13 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS0_hz19 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B (24137214174571263 / 50000000000000000) (482744285510373303 / 1000000000000000000) (((√((1 : ℝ) - (((3 / 10) : ℝ)^2))) / Real.pi) + (((3 / 10) : ℝ) * (kdot ((3 / 10))))) := badd (lowCoarseS0_hz17 hx hc) (lowCoarseS0_hz18 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS0_hz20 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B (24137214174571263 / 50000000000000000) (482744285510373303 / 1000000000000000000) (kappa ((3 / 10))) := by rw [kappa_eq]; exact (lowCoarseS0_hz19 hx hc)

theorem lowCoarseS0_hz21 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B (600329057623642767 / 1000000000000000000) (150082265386100149 / 250000000000000000) (kdot ((31 / 100))) := by
    constructor
    · apply bkdot_lower (q := (362876548309445177 / 500000000000000000)) (a := (627801648211436731 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (725753096618890353 / 1000000000000000000)) (a := (306543770533557 / 488281250000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS0_hz22 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B (961 / 10000) (961 / 10000) (((31 / 100) : ℝ)^2) := bsq (bpoint ((31 / 100) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS0_hz23 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B (9039 / 10000) (9039 / 10000) ((1 : ℝ) - (((31 / 100) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS0_hz22 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS0_hz24 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B (950736556570746363 / 1000000000000000000) (237684139142686591 / 250000000000000000) (√((1 : ℝ) - (((31 / 100) : ℝ)^2))) := bsqrt (lowCoarseS0_hz23 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS0_hz25 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B (60525769022560667 / 200000000000000000) (302628845112803337 / 1000000000000000000) ((√((1 : ℝ) - (((31 / 100) : ℝ)^2))) / Real.pi) := bdiv (lowCoarseS0_hz24 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS0_hz26 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B (186102007863329257 / 1000000000000000000) (37220401815752837 / 200000000000000000) (((31 / 100) : ℝ) * (kdot ((31 / 100)))) := bmul (bpoint ((31 / 100) : ℝ)) (lowCoarseS0_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS0_hz27 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B (30545678311008287 / 62500000000000000) (244365427095783761 / 500000000000000000) (((√((1 : ℝ) - (((31 / 100) : ℝ)^2))) / Real.pi) + (((31 / 100) : ℝ) * (kdot ((31 / 100))))) := badd (lowCoarseS0_hz25 hx hc) (lowCoarseS0_hz26 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS0_hz28 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B (30545678311008287 / 62500000000000000) (244365427095783761 / 500000000000000000) (kappa ((31 / 100))) := by rw [kappa_eq]; exact (lowCoarseS0_hz27 hx hc)

theorem lowCoarseS0_hz29 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B (24137214174571263 / 50000000000000000) (244365427095783761 / 500000000000000000) (kappa c) := bkappa (lowCoarseS0_hz1 hx hc) (by norm_num) (by norm_num) (lowCoarseS0_hz20 hx hc).1 (lowCoarseS0_hz28 hx hc).2

theorem lowCoarseS0_hz30 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B (255634572904216239 / 500000000000000000) (25862785825428737 / 50000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (lowCoarseS0_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS0_hz31 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B (255634572904216239 / 250000000000000000) (25862785825428737 / 25000000000000000) ((2 : ℝ) * ((1 : ℝ) - (kappa c))) := bmul (bpoint (2 : ℝ)) (lowCoarseS0_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS0_hz32 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B 0 (1 / 8000000) ((8 : ℝ) * (x^2)) := bmul (bpoint (8 : ℝ)) (lowCoarseS0_hz7 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS0_hz33 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B (255634541654216239 / 250000000000000000) (25862785825428737 / 25000000000000000) (((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2))) := bsub (lowCoarseS0_hz31 hx hc) (lowCoarseS0_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS0_hz34 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B (1011206292809170049 / 1000000000000000000) (508554675776643873 / 500000000000000000) (√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) := bsqrt (lowCoarseS0_hz33 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS0_hz35 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B (6782329983125268139 / 250000000000000000) (13564659966250536279 / 500000000000000000) ((2 : ℝ) * (√(184 : ℝ))) := bmul (bpoint (2 : ℝ)) (lowCoarseS0_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS0_hz36 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B 0 (678232998312527 / 200000000000000000) (((2 : ℝ) * (√(184 : ℝ))) * x) := bmul (lowCoarseS0_hz35 hx hc) (lowCoarseS0_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS0_hz37 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B (503907563908803707 / 500000000000000000) (508554675776643873 / 500000000000000000) ((√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) - (((2 : ℝ) * (√(184 : ℝ))) * x)) := bsub (lowCoarseS0_hz34 hx hc) (lowCoarseS0_hz36 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS0_hz38 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B (503907563908803707 / 500000000000000000) (508554675776643873 / 500000000000000000) (ndm x c) := by
    convert (lowCoarseS0_hz37 hx hc) using 1 <;>
      norm_num [ndm] <;> ring

theorem lowCoarseS0_hz39 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B 1 (1003394039991562637 / 1000000000000000000) ((nap x)^2) := bsq (lowCoarseS0_hz6 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS0_hz40 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B 2 (1003394039991562637 / 500000000000000000) ((2 : ℝ) * ((nap x)^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS0_hz39 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS0_hz41 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B (1015691331858020369 / 1000000000000000000) (517255716508574741 / 500000000000000000) ((ndm x c)^2) := bsq (lowCoarseS0_hz38 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS0_hz42 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B (482744283491425259 / 500000000000000000) (198219349625020981 / 200000000000000000) (((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) := bsub (lowCoarseS0_hz40 hx hc) (lowCoarseS0_hz41 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS0_hz43 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B (199322335762284863 / 200000000000000000) 1 ((nam x)^2) := bsq (lowCoarseS0_hz12 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS0_hz44 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B (199322335762284863 / 100000000000000000) 2 ((2 : ℝ) * ((nam x)^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS0_hz43 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS0_hz45 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B (482744283491425259 / 1000000000000000000) (62154144964158921 / 125000000000000000) ((((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) / ((2 : ℝ) * ((nam x)^2))) := bdiv (lowCoarseS0_hz42 hx hc) (lowCoarseS0_hz44 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS0_hz46 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B (482744283491425259 / 1000000000000000000) (62154144964158921 / 125000000000000000) (nc1 x c) := by
    convert (lowCoarseS0_hz45 hx hc) using 1 <;>
      norm_num [nc1] <;> ring

theorem lowCoarseS0_hz47 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B (298493341436901877 / 500000000000000000) (150082265386100149 / 250000000000000000) (kdot c) := bkdot (lowCoarseS0_hz1 hx hc) (lowCoarseS0_hz13 hx hc).1 (lowCoarseS0_hz21 hx hc).2

theorem lowCoarseS0_hz48 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B (165089985297821299 / 250000000000000000) (132071988238289429 / 200000000000000000) (kdot ((482744283491425259 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (59063546431275923 / 100000000000000000)) (a := (133376339202282971 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (590635464312759229 / 1000000000000000000)) (a := (533505356808877497 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS0_hz49 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B (133130128361260449 / 200000000000000000) (665650641806365869 / 1000000000000000000) (kdot ((62154144964158921 / 125000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (579480191068955379 / 1000000000000000000)) (a := (131298685929222901 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (289740095534477689 / 500000000000000000)) (a := (105038948743358333 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS0_hz50 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B (165089985297821299 / 250000000000000000) (665650641806365869 / 1000000000000000000) (kdot (nc1 x c)) := bkdot (lowCoarseS0_hz46 hx hc) (lowCoarseS0_hz48 hx hc).1 (lowCoarseS0_hz49 hx hc).2

theorem lowCoarseS0_hz51 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B (9 / 100) (961 / 10000) (c^2) := bsq (lowCoarseS0_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS0_hz52 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B (9039 / 10000) (91 / 100) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS0_hz51 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS0_hz53 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B (950736556570746363 / 1000000000000000000) (19078784028338913 / 20000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (lowCoarseS0_hz52 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS0_hz54 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B (567577063194032341 / 1000000000000000000) (286338712778524961 / 500000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (lowCoarseS0_hz53 hx hc) (lowCoarseS0_hz47 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS0_hz55 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B (567577063194032341 / 1000000000000000000) (286338712778524961 / 500000000000000000) (npa c) := by
    convert (lowCoarseS0_hz54 hx hc) using 1 <;>
      norm_num [npa] <;> ring

theorem lowCoarseS0_hz56 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B (60525769022560667 / 200000000000000000) (60729655725856827 / 200000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (lowCoarseS0_hz53 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS0_hz57 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B (89548002431070563 / 500000000000000000) (37220401815752837 / 200000000000000000) (c * (kdot c)) := bmul (lowCoarseS0_hz1 hx hc) (lowCoarseS0_hz47 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS0_hz58 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B (2330536720680783 / 20000000000000000) (124552273767143009 / 1000000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (lowCoarseS0_hz56 hx hc) (lowCoarseS0_hz57 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS0_hz59 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B (2330536720680783 / 20000000000000000) (124552273767143009 / 1000000000000000000) (npp c) := by
    convert (lowCoarseS0_hz58 hx hc) using 1 <;>
      norm_num [npp] <;> ring

theorem lowCoarseS0_hz60 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B 0 (23 / 4000) ((46 : ℝ) * x) := bmul (bpoint (46 : ℝ)) (lowCoarseS0_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS0_hz61 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B (9591663046625439083 / 1000000000000000000) (2399353261656359771 / 250000000000000000) ((√(92 : ℝ)) + ((46 : ℝ) * x)) := badd (lowCoarseS0_hz3 hx hc) (lowCoarseS0_hz60 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS0_hz62 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B (28774989139876317249 / 250000000000000000) (7198059784969079313 / 62500000000000000) ((12 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (bpoint (12 : ℝ)) (lowCoarseS0_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS0_hz63 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B 0 (14396119569938159 / 1000000000000000000) (((12 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS0_hz62 hx hc) (lowCoarseS0_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS0_hz64 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B 0 (14396119569938159 / 1000000000000000000) (nr1 x) := by
    convert (lowCoarseS0_hz63 hx hc) using 1 <;>
      norm_num [nr1] <;> ring

theorem lowCoarseS0_hz65 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B (9591663046625439083 / 125000000000000000) (2399353261656359771 / 31250000000000000) ((8 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (bpoint (8 : ℝ)) (lowCoarseS0_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS0_hz66 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B 0 (59983831541409 / 6250000000000000) (((8 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS0_hz65 hx hc) (lowCoarseS0_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS0_hz67 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B 0 (59983831541409 / 6250000000000000) (nrpp x) := by
    convert (lowCoarseS0_hz66 hx hc) using 1 <;>
      norm_num [nrpp] <;> ring

theorem lowCoarseS0_hz68 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B 0 (847791247890659 / 500000000000000000) (ne0 x) := by
    convert (lowCoarseS0_hz4 hx hc) using 1 <;>
      norm_num [ne0] <;> ring

theorem lowCoarseS0_hz69 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B (567577063194032341 / 1000000000000000000) (587073545126988081 / 1000000000000000000) ((npa c) + (nr1 x)) := badd (lowCoarseS0_hz55 hx hc) (lowCoarseS0_hz64 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS0_hz70 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B (567577063194032341 / 1000000000000000000) (588070676661221519 / 1000000000000000000) (((npa c) + (nr1 x)) / (nam x)) := bdiv (lowCoarseS0_hz69 hx hc) (lowCoarseS0_hz12 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS0_hz71 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B (567577063194032341 / 1000000000000000000) (589766259157002837 / 1000000000000000000) ((((npa c) + (nr1 x)) / (nam x)) + (ne0 x)) := badd (lowCoarseS0_hz70 hx hc) (lowCoarseS0_hz68 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS0_hz72 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B (567577063194032341 / 1000000000000000000) (589766259157002837 / 1000000000000000000) (nlam x c) := by
    convert (lowCoarseS0_hz71 hx hc) using 1 <;>
      norm_num [nlam] <;> ring

theorem lowCoarseS0_hz73 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS0_hz74 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B 0 (59947894041409 / 100000000000000000) ((√(23 : ℝ)) * x) := bmul (lowCoarseS0_hz73 hx hc) (lowCoarseS0_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS0_hz75 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B (1 / 2) (50059947894041409 / 100000000000000000) (((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)) := badd (bpoint ((1 / 2) : ℝ)) (lowCoarseS0_hz74 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS0_hz76 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B (176776695296636881 / 250000000000000000) (353765274914177413 / 500000000000000000) (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) := bsqrt (lowCoarseS0_hz75 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS0_hz77 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B 0 (59947894041409 / 50000000000000000) ((√(92 : ℝ)) * x) := bmul (lowCoarseS0_hz3 hx hc) (lowCoarseS0_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS0_hz78 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B (176776695296636881 / 250000000000000000) (354364753854591503 / 500000000000000000) ((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x)) := badd (lowCoarseS0_hz76 hx hc) (lowCoarseS0_hz77 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS0_hz79 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B (499999999999999999 / 1000000000000000000) (251148757548850447 / 500000000000000000) (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2) := bsq (lowCoarseS0_hz78 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS0_hz80 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B (499999999999999999 / 125000000000000000) (251148757548850447 / 62500000000000000) ((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) := bmul (bpoint (8 : ℝ)) (lowCoarseS0_hz79 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS0_hz81 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B (7673330437300351251 / 200000000000000000) (1928302689874485209 / 50000000000000000) (((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (lowCoarseS0_hz80 hx hc) (lowCoarseS0_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS0_hz82 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B 0 (2410378362343107 / 500000000000000000) ((((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS0_hz81 hx hc) (lowCoarseS0_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS0_hz83 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B 0 (2410378362343107 / 500000000000000000) (nrs x) := by
    convert (lowCoarseS0_hz82 hx hc) using 1 <;>
      norm_num [nrs] <;> ring

theorem lowCoarseS0_hz84 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B (2330536720680783 / 20000000000000000) (134149686813768449 / 1000000000000000000) ((npp c) + (nrpp x)) := badd (lowCoarseS0_hz59 hx hc) (lowCoarseS0_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS0_hz85 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B (2330536720680783 / 40000000000000000) (17859365025141589 / 200000000000000000) (if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) := bweaken (bfirst (lowCoarseS0_hz84 hx hc) (lowCoarseS0_hz50 hx hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem lowCoarseS0_hz86 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B (322143722663962581 / 1000000000000000000) (347824240440045033 / 1000000000000000000) ((nlam x c)^2) := bsq (lowCoarseS0_hz72 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS0_hz87 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B (233042043243649557 / 1000000000000000000) (247240815118443633 / 1000000000000000000) ((nc1 x c)^2) := bsq (lowCoarseS0_hz46 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS0_hz88 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B (752759184881556367 / 1000000000000000000) (766957956756350443 / 1000000000000000000) ((1 : ℝ) - ((nc1 x c)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS0_hz87 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS0_hz89 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B (216904239366355569 / 250000000000000000) (437880679168523729 / 500000000000000000) (√((1 : ℝ) - ((nc1 x c)^2))) := bsqrt (lowCoarseS0_hz88 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS0_hz90 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B (1362849529851649369 / 500000000000000000) (4298883515077323 / 1562500000000000) (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))) := bmul pi_mem (lowCoarseS0_hz89 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS0_hz91 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B (117088440497878413 / 1000000000000000000) (127609186788913829 / 1000000000000000000) (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2))))) := bdiv (lowCoarseS0_hz86 hx hc) (lowCoarseS0_hz90 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS0_hz92 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B (43837964628724497 / 250000000000000000) (108453005957310887 / 500000000000000000) ((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) := badd (lowCoarseS0_hz85 hx hc) (lowCoarseS0_hz91 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS0_hz93 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B 0 (2875000000001 / 1000000000000000000) ((ne0 x)^2) := bsq (lowCoarseS0_hz68 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS0_hz94 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B (43837964628724497 / 250000000000000000) (8676355476584871 / 40000000000000000) (((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) + ((ne0 x)^2)) := badd (lowCoarseS0_hz92 hx hc) (lowCoarseS0_hz93 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS0_hz95 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B (43837964628724497 / 250000000000000000) (221729643639307989 / 1000000000000000000) ((((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) + ((ne0 x)^2)) + (nrs x)) := badd (lowCoarseS0_hz94 hx hc) (lowCoarseS0_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS0_hz96 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B (43837964628724497 / 250000000000000000) (221729643639307989 / 1000000000000000000) (nu x c) := by
    convert (lowCoarseS0_hz95 hx hc) using 1 <;>
      norm_num [nu] <;> ring

theorem lowCoarseS0_hz97 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B (10692942298741371 / 100000000000000000) (124552273767143009 / 1000000000000000000) ((npp c) - (nrpp x)) := bsub (lowCoarseS0_hz59 hx hc) (lowCoarseS0_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS0_hz98 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B 0 0 (min ((npp c) - (nrpp x)) (0 : ℝ)) := bweaken (bmin (lowCoarseS0_hz97 hx hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem lowCoarseS0_hz99 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B 0 0 ((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) := bmul (lowCoarseS0_hz50 hx hc) (lowCoarseS0_hz98 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS0_hz100 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B (-2875000000001 / 1000000000000000000) 0 (((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) - ((ne0 x)^2)) := bsub (lowCoarseS0_hz99 hx hc) (lowCoarseS0_hz93 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS0_hz101 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B (-964726344937243 / 200000000000000000) 0 ((((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) - ((ne0 x)^2)) - (nrs x)) := bsub (lowCoarseS0_hz100 hx hc) (lowCoarseS0_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS0_hz102 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B (-964726344937243 / 200000000000000000) 0 (nl x c) := by
    convert (lowCoarseS0_hz101 hx hc) using 1 <;>
      norm_num [nl] <;> ring

theorem lowCoarseS0_hz103 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B 0 (221729643639307989 / 1000000000000000000) |(nu x c)| := bweaken (babs (lowCoarseS0_hz96 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS0_hz104 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B 0 (964726344937243 / 200000000000000000) |(nl x c)| := bweaken (babs (lowCoarseS0_hz102 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS0_hz105 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B 0 (221729643639307989 / 1000000000000000000) (max |(nu x c)| |(nl x c)|) := bweaken (bmax (lowCoarseS0_hz103 hx hc) (lowCoarseS0_hz104 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS0_hz106 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) : B 0 (221729643639307989 / 1000000000000000000) (ns x c) := by
    convert (lowCoarseS0_hz105 hx hc) using 1 <;>
      norm_num [ns] <;> ring

theorem lowCoarseS0 {x c : ℝ}
    (hx : B 0 (1/8000) x) (hc : B (3 / 10) (31 / 100) c) :
    0 < nam x ∧ 0 ≤ ndm x c ∧ ndm x c ^ 2 ≤ 2 * nap x ^ 2 ∧ nc1 x c < 1 ∧
    0 ≤ npa c - nr1 x ∧ ne0 x ≤ (npa c - nr1 x) / nap x ∧ ns x c ≤ (9 / 25) := by
  refine ⟨lt_of_lt_of_le (by norm_num) (lowCoarseS0_hz12 hx hc).1,
    le_trans (by norm_num) (lowCoarseS0_hz38 hx hc).1, ?_,
    lt_of_le_of_lt (lowCoarseS0_hz46 hx hc).2 (by norm_num), ?_, ?_, (lowCoarseS0_hz106 hx hc).2.trans (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (lowCoarseS0_hz38 hx hc).1) (lowCoarseS0_hz38 hx hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) (lowCoarseS0_hz6 hx hc).1 2
    nlinarith only [h1,h2]
  · linarith only [(lowCoarseS0_hz55 hx hc).1,(lowCoarseS0_hz64 hx hc).2]
  · have hap : 0 < nap x := lt_of_lt_of_le (by norm_num) (lowCoarseS0_hz6 hx hc).1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul (lowCoarseS0_hz68 hx hc).2 (lowCoarseS0_hz6 hx hc).2 (le_trans (by norm_num) (lowCoarseS0_hz6 hx hc).1) (by norm_num)
    linarith only [h,(lowCoarseS0_hz55 hx hc).1,(lowCoarseS0_hz64 hx hc).2]

theorem lowCoarseS1_hz0 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B 0 (1 / 8000) x := hx

theorem lowCoarseS1_hz1 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B (31 / 100) (8 / 25) c := hc

theorem lowCoarseS1_hz2 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B (6782329983125268139 / 500000000000000000) (13564659966250536279 / 1000000000000000000) (√(184 : ℝ)) := bsqrt (bpoint (184 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS1_hz3 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS1_hz4 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B 0 (847791247890659 / 500000000000000000) ((√(184 : ℝ)) * x) := bmul (lowCoarseS1_hz2 hx hc) (lowCoarseS1_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS1_hz5 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B 1 (500847791247890659 / 500000000000000000) ((1 : ℝ) + ((√(184 : ℝ)) * x)) := badd (bpoint (1 : ℝ)) (lowCoarseS1_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS1_hz6 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B 1 (500847791247890659 / 500000000000000000) (nap x) := by
    convert (lowCoarseS1_hz5 hx hc) using 1 <;>
      norm_num [nap] <;> ring

theorem lowCoarseS1_hz7 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B 0 (1 / 64000000) (x^2) := bsq (lowCoarseS1_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS1_hz8 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B 0 (1 / 32000000) ((2 : ℝ) * (x^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS1_hz7 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS1_hz9 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B (31999999 / 32000000) 1 ((1 : ℝ) - ((2 : ℝ) * (x^2))) := bsub (bpoint (1 : ℝ)) (lowCoarseS1_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS1_hz10 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B (999999984374999877 / 1000000000000000000) 1 (√((1 : ℝ) - ((2 : ℝ) * (x^2)))) := bsqrt (lowCoarseS1_hz9 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS1_hz11 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B (998304401879218559 / 1000000000000000000) 1 ((√((1 : ℝ) - ((2 : ℝ) * (x^2)))) - ((√(184 : ℝ)) * x)) := bsub (lowCoarseS1_hz10 hx hc) (lowCoarseS1_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS1_hz12 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B (998304401879218559 / 1000000000000000000) 1 (nam x) := by
    convert (lowCoarseS1_hz11 hx hc) using 1 <;>
      norm_num [nam] <;> ring

theorem lowCoarseS1_hz13 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B (600329057623642767 / 1000000000000000000) (150082265386100149 / 250000000000000000) (kdot ((31 / 100))) := by
    constructor
    · apply bkdot_lower (q := (362876548309445177 / 500000000000000000)) (a := (627801648211436731 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (725753096618890353 / 1000000000000000000)) (a := (306543770533557 / 488281250000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS1_hz14 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B (961 / 10000) (961 / 10000) (((31 / 100) : ℝ)^2) := bsq (bpoint ((31 / 100) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS1_hz15 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B (9039 / 10000) (9039 / 10000) ((1 : ℝ) - (((31 / 100) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS1_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS1_hz16 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B (950736556570746363 / 1000000000000000000) (237684139142686591 / 250000000000000000) (√((1 : ℝ) - (((31 / 100) : ℝ)^2))) := bsqrt (lowCoarseS1_hz15 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS1_hz17 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B (60525769022560667 / 200000000000000000) (302628845112803337 / 1000000000000000000) ((√((1 : ℝ) - (((31 / 100) : ℝ)^2))) / Real.pi) := bdiv (lowCoarseS1_hz16 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS1_hz18 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B (186102007863329257 / 1000000000000000000) (37220401815752837 / 200000000000000000) (((31 / 100) : ℝ) * (kdot ((31 / 100)))) := bmul (bpoint ((31 / 100) : ℝ)) (lowCoarseS1_hz13 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS1_hz19 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B (30545678311008287 / 62500000000000000) (244365427095783761 / 500000000000000000) (((√((1 : ℝ) - (((31 / 100) : ℝ)^2))) / Real.pi) + (((31 / 100) : ℝ) * (kdot ((31 / 100))))) := badd (lowCoarseS1_hz17 hx hc) (lowCoarseS1_hz18 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS1_hz20 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B (30545678311008287 / 62500000000000000) (244365427095783761 / 500000000000000000) (kappa ((31 / 100))) := by rw [kappa_eq]; exact (lowCoarseS1_hz19 hx hc)

theorem lowCoarseS1_hz21 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B (301841457825431989 / 500000000000000000) (301841458963297909 / 500000000000000000) (kdot ((8 / 25))) := by
    constructor
    · apply bkdot_lower (q := (717740562565273409 / 1000000000000000000)) (a := (311266710170843037 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (11214696290082397 / 15625000000000000)) (a := (622533416766974861 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS1_hz22 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B (64 / 625) (64 / 625) (((8 / 25) : ℝ)^2) := bsq (bpoint ((8 / 25) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS1_hz23 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B (561 / 625) (561 / 625) ((1 : ℝ) - (((8 / 25) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS1_hz22 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS1_hz24 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B (473708771293080449 / 500000000000000000) (947417542586160899 / 1000000000000000000) (√((1 : ℝ) - (((8 / 25) : ℝ)^2))) := bsqrt (lowCoarseS1_hz23 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS1_hz25 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B (150786185074563763 / 500000000000000000) (37696546268640941 / 125000000000000000) ((√((1 : ℝ) - (((8 / 25) : ℝ)^2))) / Real.pi) := bdiv (lowCoarseS1_hz24 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS1_hz26 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B (24147316626034559 / 125000000000000000) (96589266868255331 / 500000000000000000) (((8 / 25) : ℝ) * (kdot ((8 / 25)))) := bmul (bpoint ((8 / 25) : ℝ)) (lowCoarseS1_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS1_hz27 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B (247375451578701999 / 500000000000000000) (49475090388563819 / 100000000000000000) (((√((1 : ℝ) - (((8 / 25) : ℝ)^2))) / Real.pi) + (((8 / 25) : ℝ) * (kdot ((8 / 25))))) := badd (lowCoarseS1_hz25 hx hc) (lowCoarseS1_hz26 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS1_hz28 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B (247375451578701999 / 500000000000000000) (49475090388563819 / 100000000000000000) (kappa ((8 / 25))) := by rw [kappa_eq]; exact (lowCoarseS1_hz27 hx hc)

theorem lowCoarseS1_hz29 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B (30545678311008287 / 62500000000000000) (49475090388563819 / 100000000000000000) (kappa c) := bkappa (lowCoarseS1_hz1 hx hc) (by norm_num) (by norm_num) (lowCoarseS1_hz20 hx hc).1 (lowCoarseS1_hz28 hx hc).2

theorem lowCoarseS1_hz30 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B (50524909611436181 / 100000000000000000) (31954321688991713 / 62500000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (lowCoarseS1_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS1_hz31 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B (50524909611436181 / 50000000000000000) (31954321688991713 / 31250000000000000) ((2 : ℝ) * ((1 : ℝ) - (kappa c))) := bmul (bpoint (2 : ℝ)) (lowCoarseS1_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS1_hz32 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B 0 (1 / 8000000) ((8 : ℝ) * (x^2)) := bmul (bpoint (8 : ℝ)) (lowCoarseS1_hz7 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS1_hz33 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B (50524903361436181 / 50000000000000000) (31954321688991713 / 31250000000000000) (((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2))) := bsub (lowCoarseS1_hz31 hx hc) (lowCoarseS1_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS1_hz34 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B (1005235329278037073 / 1000000000000000000) (252801588954625493 / 250000000000000000) (√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) := bsqrt (lowCoarseS1_hz33 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS1_hz35 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B (6782329983125268139 / 250000000000000000) (13564659966250536279 / 500000000000000000) ((2 : ℝ) * (√(184 : ℝ))) := bmul (bpoint (2 : ℝ)) (lowCoarseS1_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS1_hz36 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B 0 (678232998312527 / 200000000000000000) (((2 : ℝ) * (√(184 : ℝ))) * x) := bmul (lowCoarseS1_hz35 hx hc) (lowCoarseS1_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS1_hz37 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B (500922082143237219 / 500000000000000000) (252801588954625493 / 250000000000000000) ((√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) - (((2 : ℝ) * (√(184 : ℝ))) * x)) := bsub (lowCoarseS1_hz34 hx hc) (lowCoarseS1_hz36 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS1_hz38 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B (500922082143237219 / 500000000000000000) (252801588954625493 / 250000000000000000) (ndm x c) := by
    convert (lowCoarseS1_hz37 hx hc) using 1 <;>
      norm_num [ndm] <;> ring

theorem lowCoarseS1_hz39 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B 1 (1003394039991562637 / 1000000000000000000) ((nap x)^2) := bsq (lowCoarseS1_hz6 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS1_hz40 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B 2 (1003394039991562637 / 500000000000000000) ((2 : ℝ) * ((nap x)^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS1_hz39 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS1_hz41 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B (1003691729514864383 / 1000000000000000000) (511269147023867409 / 500000000000000000) ((ndm x c)^2) := bsq (lowCoarseS1_hz38 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS1_hz42 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B (488730852976132591 / 500000000000000000) (1003096350468260891 / 1000000000000000000) (((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) := bsub (lowCoarseS1_hz40 hx hc) (lowCoarseS1_hz41 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS1_hz43 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B (199322335762284863 / 200000000000000000) 1 ((nam x)^2) := bsq (lowCoarseS1_hz12 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS1_hz44 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B (199322335762284863 / 100000000000000000) 2 ((2 : ℝ) * ((nam x)^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS1_hz43 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS1_hz45 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B (488730852976132591 / 1000000000000000000) (62906669906814301 / 125000000000000000) ((((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) / ((2 : ℝ) * ((nam x)^2))) := bdiv (lowCoarseS1_hz42 hx hc) (lowCoarseS1_hz44 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS1_hz46 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B (488730852976132591 / 1000000000000000000) (62906669906814301 / 125000000000000000) (nc1 x c) := by
    convert (lowCoarseS1_hz45 hx hc) using 1 <;>
      norm_num [nc1] <;> ring

theorem lowCoarseS1_hz47 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B (600329057623642767 / 1000000000000000000) (301841458963297909 / 500000000000000000) (kdot c) := bkdot (lowCoarseS1_hz1 hx hc) (lowCoarseS1_hz13 hx hc).1 (lowCoarseS1_hz21 hx hc).2

theorem lowCoarseS1_hz48 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B (662539990607086937 / 1000000000000000000) (662539990607197253 / 1000000000000000000) (kdot ((488730852976132591 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (586025748647315141 / 1000000000000000000)) (a := (10601618863891183 / 20000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (29301287432365757 / 50000000000000000)) (a := (530080943194385867 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS1_hz49 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B (166965937431014373 / 250000000000000000) (667863749724100421 / 1000000000000000000) (kdot ((62906669906814301 / 125000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (574845820260829227 / 1000000000000000000)) (a := (1630370006027753 / 3125000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (287422910130414613 / 500000000000000000)) (a := (65214800241101691 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS1_hz50 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B (662539990607086937 / 1000000000000000000) (667863749724100421 / 1000000000000000000) (kdot (nc1 x c)) := bkdot (lowCoarseS1_hz46 hx hc) (lowCoarseS1_hz48 hx hc).1 (lowCoarseS1_hz49 hx hc).2

theorem lowCoarseS1_hz51 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B (961 / 10000) (64 / 625) (c^2) := bsq (lowCoarseS1_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS1_hz52 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B (561 / 625) (9039 / 10000) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS1_hz51 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS1_hz53 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B (473708771293080449 / 500000000000000000) (237684139142686591 / 250000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (lowCoarseS1_hz52 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS1_hz54 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B (56876228051685741 / 100000000000000000) (2869717093250561 / 5000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (lowCoarseS1_hz53 hx hc) (lowCoarseS1_hz47 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS1_hz55 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B (56876228051685741 / 100000000000000000) (2869717093250561 / 5000000000000000) (npa c) := by
    convert (lowCoarseS1_hz54 hx hc) using 1 <;>
      norm_num [npa] <;> ring

theorem lowCoarseS1_hz56 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B (150786185074563763 / 500000000000000000) (302628845112803337 / 1000000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (lowCoarseS1_hz53 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS1_hz57 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B (186102007863329257 / 1000000000000000000) (96589266868255331 / 500000000000000000) (c * (kdot c)) := bmul (lowCoarseS1_hz1 hx hc) (lowCoarseS1_hz47 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS1_hz58 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B (3387307387894277 / 31250000000000000) (728292732809213 / 6250000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (lowCoarseS1_hz56 hx hc) (lowCoarseS1_hz57 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS1_hz59 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B (3387307387894277 / 31250000000000000) (728292732809213 / 6250000000000000) (npp c) := by
    convert (lowCoarseS1_hz58 hx hc) using 1 <;>
      norm_num [npp] <;> ring

theorem lowCoarseS1_hz60 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B 0 (23 / 4000) ((46 : ℝ) * x) := bmul (bpoint (46 : ℝ)) (lowCoarseS1_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS1_hz61 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B (9591663046625439083 / 1000000000000000000) (2399353261656359771 / 250000000000000000) ((√(92 : ℝ)) + ((46 : ℝ) * x)) := badd (lowCoarseS1_hz3 hx hc) (lowCoarseS1_hz60 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS1_hz62 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B (28774989139876317249 / 250000000000000000) (7198059784969079313 / 62500000000000000) ((12 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (bpoint (12 : ℝ)) (lowCoarseS1_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS1_hz63 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B 0 (14396119569938159 / 1000000000000000000) (((12 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS1_hz62 hx hc) (lowCoarseS1_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS1_hz64 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B 0 (14396119569938159 / 1000000000000000000) (nr1 x) := by
    convert (lowCoarseS1_hz63 hx hc) using 1 <;>
      norm_num [nr1] <;> ring

theorem lowCoarseS1_hz65 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B (9591663046625439083 / 125000000000000000) (2399353261656359771 / 31250000000000000) ((8 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (bpoint (8 : ℝ)) (lowCoarseS1_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS1_hz66 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B 0 (59983831541409 / 6250000000000000) (((8 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS1_hz65 hx hc) (lowCoarseS1_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS1_hz67 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B 0 (59983831541409 / 6250000000000000) (nrpp x) := by
    convert (lowCoarseS1_hz66 hx hc) using 1 <;>
      norm_num [nrpp] <;> ring

theorem lowCoarseS1_hz68 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B 0 (847791247890659 / 500000000000000000) (ne0 x) := by
    convert (lowCoarseS1_hz4 hx hc) using 1 <;>
      norm_num [ne0] <;> ring

theorem lowCoarseS1_hz69 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B (56876228051685741 / 100000000000000000) (588339538220050359 / 1000000000000000000) ((npa c) + (nr1 x)) := badd (lowCoarseS1_hz55 hx hc) (lowCoarseS1_hz64 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS1_hz70 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B (56876228051685741 / 100000000000000000) (36833676250985791 / 62500000000000000) (((npa c) + (nr1 x)) / (nam x)) := bdiv (lowCoarseS1_hz69 hx hc) (lowCoarseS1_hz12 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS1_hz71 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B (56876228051685741 / 100000000000000000) (295517201255776987 / 500000000000000000) ((((npa c) + (nr1 x)) / (nam x)) + (ne0 x)) := badd (lowCoarseS1_hz70 hx hc) (lowCoarseS1_hz68 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS1_hz72 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B (56876228051685741 / 100000000000000000) (295517201255776987 / 500000000000000000) (nlam x c) := by
    convert (lowCoarseS1_hz71 hx hc) using 1 <;>
      norm_num [nlam] <;> ring

theorem lowCoarseS1_hz73 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS1_hz74 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B 0 (59947894041409 / 100000000000000000) ((√(23 : ℝ)) * x) := bmul (lowCoarseS1_hz73 hx hc) (lowCoarseS1_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS1_hz75 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B (1 / 2) (50059947894041409 / 100000000000000000) (((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)) := badd (bpoint ((1 / 2) : ℝ)) (lowCoarseS1_hz74 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS1_hz76 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B (176776695296636881 / 250000000000000000) (353765274914177413 / 500000000000000000) (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) := bsqrt (lowCoarseS1_hz75 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS1_hz77 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B 0 (59947894041409 / 50000000000000000) ((√(92 : ℝ)) * x) := bmul (lowCoarseS1_hz3 hx hc) (lowCoarseS1_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS1_hz78 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B (176776695296636881 / 250000000000000000) (354364753854591503 / 500000000000000000) ((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x)) := badd (lowCoarseS1_hz76 hx hc) (lowCoarseS1_hz77 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS1_hz79 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B (499999999999999999 / 1000000000000000000) (251148757548850447 / 500000000000000000) (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2) := bsq (lowCoarseS1_hz78 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS1_hz80 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B (499999999999999999 / 125000000000000000) (251148757548850447 / 62500000000000000) ((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) := bmul (bpoint (8 : ℝ)) (lowCoarseS1_hz79 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS1_hz81 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B (7673330437300351251 / 200000000000000000) (1928302689874485209 / 50000000000000000) (((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (lowCoarseS1_hz80 hx hc) (lowCoarseS1_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS1_hz82 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B 0 (2410378362343107 / 500000000000000000) ((((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS1_hz81 hx hc) (lowCoarseS1_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS1_hz83 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B 0 (2410378362343107 / 500000000000000000) (nrs x) := by
    convert (lowCoarseS1_hz82 hx hc) using 1 <;>
      norm_num [nrs] <;> ring

theorem lowCoarseS1_hz84 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B (3387307387894277 / 31250000000000000) (394138282175311 / 3125000000000000) ((npp c) + (nrpp x)) := badd (lowCoarseS1_hz59 hx hc) (lowCoarseS1_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS1_hz85 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B (3387307387894277 / 62500000000000000) (84233814733894009 / 1000000000000000000) (if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) := bweaken (bfirst (lowCoarseS1_hz84 hx hc) (lowCoarseS1_hz50 hx hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem lowCoarseS1_hz86 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B (161745265869368199 / 500000000000000000) (349321664952189599 / 1000000000000000000) ((nlam x c)^2) := bsq (lowCoarseS1_hz72 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS1_hz87 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B (23885784665077813 / 100000000000000000) (253263943600953343 / 1000000000000000000) ((nc1 x c)^2) := bsq (lowCoarseS1_hz46 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS1_hz88 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B (746736056399046657 / 1000000000000000000) (76114215334922187 / 100000000000000000) ((1 : ℝ) - ((nc1 x c)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS1_hz87 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS1_hz89 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B (864138910360508333 / 1000000000000000000) (872434612649694149 / 1000000000000000000) (√((1 : ℝ) - ((nc1 x c)^2))) := bsqrt (lowCoarseS1_hz88 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS1_hz90 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B (1357386226234830923 / 500000000000000000) (2740834169837736037 / 1000000000000000000) (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))) := bmul pi_mem (lowCoarseS1_hz89 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS1_hz91 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B (29506576437447127 / 250000000000000000) (64337190513777203 / 500000000000000000) (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2))))) := bdiv (lowCoarseS1_hz86 hx hc) (lowCoarseS1_hz90 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS1_hz92 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B (8611161197804847 / 50000000000000000) (42581639152289683 / 200000000000000000) ((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) := badd (lowCoarseS1_hz85 hx hc) (lowCoarseS1_hz91 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS1_hz93 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B 0 (2875000000001 / 1000000000000000000) ((ne0 x)^2) := bsq (lowCoarseS1_hz68 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS1_hz94 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B (8611161197804847 / 50000000000000000) (6653470961295263 / 31250000000000000) (((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) + ((ne0 x)^2)) := badd (lowCoarseS1_hz92 hx hc) (lowCoarseS1_hz93 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS1_hz95 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B (8611161197804847 / 50000000000000000) (21773182748613463 / 100000000000000000) ((((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) + ((ne0 x)^2)) + (nrs x)) := badd (lowCoarseS1_hz94 hx hc) (lowCoarseS1_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS1_hz96 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B (8611161197804847 / 50000000000000000) (21773182748613463 / 100000000000000000) (nu x c) := by
    convert (lowCoarseS1_hz95 hx hc) using 1 <;>
      norm_num [nu] <;> ring

theorem lowCoarseS1_hz97 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B (96480882193351 / 976562500000000) (728292732809213 / 6250000000000000) ((npp c) - (nrpp x)) := bsub (lowCoarseS1_hz59 hx hc) (lowCoarseS1_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS1_hz98 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B 0 0 (min ((npp c) - (nrpp x)) (0 : ℝ)) := bweaken (bmin (lowCoarseS1_hz97 hx hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem lowCoarseS1_hz99 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B 0 0 ((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) := bmul (lowCoarseS1_hz50 hx hc) (lowCoarseS1_hz98 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS1_hz100 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B (-2875000000001 / 1000000000000000000) 0 (((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) - ((ne0 x)^2)) := bsub (lowCoarseS1_hz99 hx hc) (lowCoarseS1_hz93 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS1_hz101 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B (-964726344937243 / 200000000000000000) 0 ((((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) - ((ne0 x)^2)) - (nrs x)) := bsub (lowCoarseS1_hz100 hx hc) (lowCoarseS1_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS1_hz102 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B (-964726344937243 / 200000000000000000) 0 (nl x c) := by
    convert (lowCoarseS1_hz101 hx hc) using 1 <;>
      norm_num [nl] <;> ring

theorem lowCoarseS1_hz103 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B 0 (21773182748613463 / 100000000000000000) |(nu x c)| := bweaken (babs (lowCoarseS1_hz96 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS1_hz104 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B 0 (964726344937243 / 200000000000000000) |(nl x c)| := bweaken (babs (lowCoarseS1_hz102 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS1_hz105 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B 0 (21773182748613463 / 100000000000000000) (max |(nu x c)| |(nl x c)|) := bweaken (bmax (lowCoarseS1_hz103 hx hc) (lowCoarseS1_hz104 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS1_hz106 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) : B 0 (21773182748613463 / 100000000000000000) (ns x c) := by
    convert (lowCoarseS1_hz105 hx hc) using 1 <;>
      norm_num [ns] <;> ring

theorem lowCoarseS1 {x c : ℝ}
    (hx : B 0 (1/8000) x) (hc : B (31 / 100) (8 / 25) c) :
    0 < nam x ∧ 0 ≤ ndm x c ∧ ndm x c ^ 2 ≤ 2 * nap x ^ 2 ∧ nc1 x c < 1 ∧
    0 ≤ npa c - nr1 x ∧ ne0 x ≤ (npa c - nr1 x) / nap x ∧ ns x c ≤ (9 / 25) := by
  refine ⟨lt_of_lt_of_le (by norm_num) (lowCoarseS1_hz12 hx hc).1,
    le_trans (by norm_num) (lowCoarseS1_hz38 hx hc).1, ?_,
    lt_of_le_of_lt (lowCoarseS1_hz46 hx hc).2 (by norm_num), ?_, ?_, (lowCoarseS1_hz106 hx hc).2.trans (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (lowCoarseS1_hz38 hx hc).1) (lowCoarseS1_hz38 hx hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) (lowCoarseS1_hz6 hx hc).1 2
    nlinarith only [h1,h2]
  · linarith only [(lowCoarseS1_hz55 hx hc).1,(lowCoarseS1_hz64 hx hc).2]
  · have hap : 0 < nap x := lt_of_lt_of_le (by norm_num) (lowCoarseS1_hz6 hx hc).1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul (lowCoarseS1_hz68 hx hc).2 (lowCoarseS1_hz6 hx hc).2 (le_trans (by norm_num) (lowCoarseS1_hz6 hx hc).1) (by norm_num)
    linarith only [h,(lowCoarseS1_hz55 hx hc).1,(lowCoarseS1_hz64 hx hc).2]

theorem lowCoarseS2_hz0 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B 0 (1 / 8000) x := hx

theorem lowCoarseS2_hz1 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B (8 / 25) (33 / 100) c := hc

theorem lowCoarseS2_hz2 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B (6782329983125268139 / 500000000000000000) (13564659966250536279 / 1000000000000000000) (√(184 : ℝ)) := bsqrt (bpoint (184 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS2_hz3 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS2_hz4 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B 0 (847791247890659 / 500000000000000000) ((√(184 : ℝ)) * x) := bmul (lowCoarseS2_hz2 hx hc) (lowCoarseS2_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS2_hz5 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B 1 (500847791247890659 / 500000000000000000) ((1 : ℝ) + ((√(184 : ℝ)) * x)) := badd (bpoint (1 : ℝ)) (lowCoarseS2_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS2_hz6 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B 1 (500847791247890659 / 500000000000000000) (nap x) := by
    convert (lowCoarseS2_hz5 hx hc) using 1 <;>
      norm_num [nap] <;> ring

theorem lowCoarseS2_hz7 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B 0 (1 / 64000000) (x^2) := bsq (lowCoarseS2_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS2_hz8 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B 0 (1 / 32000000) ((2 : ℝ) * (x^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS2_hz7 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS2_hz9 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B (31999999 / 32000000) 1 ((1 : ℝ) - ((2 : ℝ) * (x^2))) := bsub (bpoint (1 : ℝ)) (lowCoarseS2_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS2_hz10 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B (999999984374999877 / 1000000000000000000) 1 (√((1 : ℝ) - ((2 : ℝ) * (x^2)))) := bsqrt (lowCoarseS2_hz9 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS2_hz11 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B (998304401879218559 / 1000000000000000000) 1 ((√((1 : ℝ) - ((2 : ℝ) * (x^2)))) - ((√(184 : ℝ)) * x)) := bsub (lowCoarseS2_hz10 hx hc) (lowCoarseS2_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS2_hz12 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B (998304401879218559 / 1000000000000000000) 1 (nam x) := by
    convert (lowCoarseS2_hz11 hx hc) using 1 <;>
      norm_num [nam] <;> ring

theorem lowCoarseS2_hz13 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B (301841457825431989 / 500000000000000000) (301841458963297909 / 500000000000000000) (kdot ((8 / 25))) := by
    constructor
    · apply bkdot_lower (q := (717740562565273409 / 1000000000000000000)) (a := (311266710170843037 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (11214696290082397 / 15625000000000000)) (a := (622533416766974861 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS2_hz14 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B (64 / 625) (64 / 625) (((8 / 25) : ℝ)^2) := bsq (bpoint ((8 / 25) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS2_hz15 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B (561 / 625) (561 / 625) ((1 : ℝ) - (((8 / 25) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS2_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS2_hz16 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B (473708771293080449 / 500000000000000000) (947417542586160899 / 1000000000000000000) (√((1 : ℝ) - (((8 / 25) : ℝ)^2))) := bsqrt (lowCoarseS2_hz15 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS2_hz17 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B (150786185074563763 / 500000000000000000) (37696546268640941 / 125000000000000000) ((√((1 : ℝ) - (((8 / 25) : ℝ)^2))) / Real.pi) := bdiv (lowCoarseS2_hz16 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS2_hz18 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B (24147316626034559 / 125000000000000000) (96589266868255331 / 500000000000000000) (((8 / 25) : ℝ) * (kdot ((8 / 25)))) := bmul (bpoint ((8 / 25) : ℝ)) (lowCoarseS2_hz13 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS2_hz19 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B (247375451578701999 / 500000000000000000) (49475090388563819 / 100000000000000000) (((√((1 : ℝ) - (((8 / 25) : ℝ)^2))) / Real.pi) + (((8 / 25) : ℝ) * (kdot ((8 / 25))))) := badd (lowCoarseS2_hz17 hx hc) (lowCoarseS2_hz18 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS2_hz20 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B (247375451578701999 / 500000000000000000) (49475090388563819 / 100000000000000000) (kappa ((8 / 25))) := by rw [kappa_eq]; exact (lowCoarseS2_hz19 hx hc)

theorem lowCoarseS2_hz21 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B (607048752515971501 / 1000000000000000000) (60704875383174611 / 100000000000000000) (kdot ((33 / 100))) := by
    constructor
    · apply bkdot_lower (q := (4436000620351557 / 6250000000000000)) (a := (77155797019673041 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (709760099256249119 / 1000000000000000000)) (a := (308623187045285203 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS2_hz22 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B (1089 / 10000) (1089 / 10000) (((33 / 100) : ℝ)^2) := bsq (bpoint ((33 / 100) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS2_hz23 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B (8911 / 10000) (8911 / 10000) ((1 : ℝ) - (((33 / 100) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS2_hz22 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS2_hz24 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B (14749702062668927 / 15625000000000000) (943980932010811329 / 1000000000000000000) (√((1 : ℝ) - (((33 / 100) : ℝ)^2))) := bsqrt (lowCoarseS2_hz23 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS2_hz25 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B (300478463028029993 / 1000000000000000000) (60095692605605999 / 200000000000000000) ((√((1 : ℝ) - (((33 / 100) : ℝ)^2))) / Real.pi) := bdiv (lowCoarseS2_hz24 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS2_hz26 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B (40065217666054119 / 200000000000000000) (200326088764476217 / 1000000000000000000) (((33 / 100) : ℝ) * (kdot ((33 / 100)))) := bmul (bpoint ((33 / 100) : ℝ)) (lowCoarseS2_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS2_hz27 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B (125201137839575147 / 250000000000000000) (125201137948126553 / 250000000000000000) (((√((1 : ℝ) - (((33 / 100) : ℝ)^2))) / Real.pi) + (((33 / 100) : ℝ) * (kdot ((33 / 100))))) := badd (lowCoarseS2_hz25 hx hc) (lowCoarseS2_hz26 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS2_hz28 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B (125201137839575147 / 250000000000000000) (125201137948126553 / 250000000000000000) (kappa ((33 / 100))) := by rw [kappa_eq]; exact (lowCoarseS2_hz27 hx hc)

theorem lowCoarseS2_hz29 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B (247375451578701999 / 500000000000000000) (125201137948126553 / 250000000000000000) (kappa c) := bkappa (lowCoarseS2_hz1 hx hc) (by norm_num) (by norm_num) (lowCoarseS2_hz20 hx hc).1 (lowCoarseS2_hz28 hx hc).2

theorem lowCoarseS2_hz30 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B (124798862051873447 / 250000000000000000) (252624548421298001 / 500000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (lowCoarseS2_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS2_hz31 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B (124798862051873447 / 125000000000000000) (252624548421298001 / 250000000000000000) ((2 : ℝ) * ((1 : ℝ) - (kappa c))) := bmul (bpoint (2 : ℝ)) (lowCoarseS2_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS2_hz32 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B 0 (1 / 8000000) ((8 : ℝ) * (x^2)) := bmul (bpoint (8 : ℝ)) (lowCoarseS2_hz7 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS2_hz33 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B (124798846426873447 / 125000000000000000) (252624548421298001 / 250000000000000000) (((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2))) := bsub (lowCoarseS2_hz31 hx hc) (lowCoarseS2_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS2_hz34 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B (499597530872348181 / 500000000000000000) (1005235392176972649 / 1000000000000000000) (√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) := bsqrt (lowCoarseS2_hz33 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS2_hz35 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B (6782329983125268139 / 250000000000000000) (13564659966250536279 / 500000000000000000) ((2 : ℝ) * (√(184 : ℝ))) := bmul (bpoint (2 : ℝ)) (lowCoarseS2_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS2_hz36 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B 0 (678232998312527 / 200000000000000000) (((2 : ℝ) * (√(184 : ℝ))) * x) := bmul (lowCoarseS2_hz35 hx hc) (lowCoarseS2_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS2_hz37 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B (995803896753133727 / 1000000000000000000) (1005235392176972649 / 1000000000000000000) ((√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) - (((2 : ℝ) * (√(184 : ℝ))) * x)) := bsub (lowCoarseS2_hz34 hx hc) (lowCoarseS2_hz36 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS2_hz38 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B (995803896753133727 / 1000000000000000000) (1005235392176972649 / 1000000000000000000) (ndm x c) := by
    convert (lowCoarseS2_hz37 hx hc) using 1 <;>
      norm_num [ndm] <;> ring

theorem lowCoarseS2_hz39 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B 1 (1003394039991562637 / 1000000000000000000) ((nap x)^2) := bsq (lowCoarseS2_hz6 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS2_hz40 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B 2 (1003394039991562637 / 500000000000000000) ((2 : ℝ) * ((nap x)^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS2_hz39 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS2_hz41 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B (198325080157745163 / 200000000000000000) (202099638737038401 / 200000000000000000) ((ndm x c)^2) := bsq (lowCoarseS2_hz38 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS2_hz42 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B (197900361262961599 / 200000000000000000) (1015162679194399459 / 1000000000000000000) (((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) := bsub (lowCoarseS2_hz40 hx hc) (lowCoarseS2_hz41 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS2_hz43 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B (199322335762284863 / 200000000000000000) 1 ((nam x)^2) := bsq (lowCoarseS2_hz12 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS2_hz44 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B (199322335762284863 / 100000000000000000) 2 ((2 : ℝ) * ((nam x)^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS2_hz43 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS2_hz45 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B (494750903157403997 / 1000000000000000000) (509307035416793117 / 1000000000000000000) ((((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) / ((2 : ℝ) * ((nam x)^2))) := bdiv (lowCoarseS2_hz42 hx hc) (lowCoarseS2_hz44 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS2_hz46 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B (494750903157403997 / 1000000000000000000) (509307035416793117 / 1000000000000000000) (nc1 x c) := by
    convert (lowCoarseS2_hz45 hx hc) using 1 <;>
      norm_num [nc1] <;> ring

theorem lowCoarseS2_hz47 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B (301841457825431989 / 500000000000000000) (60704875383174611 / 100000000000000000) (kdot c) := bkdot (lowCoarseS2_hz1 hx hc) (lowCoarseS2_hz13 hx hc).1 (lowCoarseS2_hz21 hx hc).2

theorem lowCoarseS2_hz48 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B (664740699735827063 / 1000000000000000000) (5193286716686733 / 7812500000000000) (kdot ((494750903157403997 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (116278215026789217 / 200000000000000000)) (a := (263312038689395081 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (145347768783486521 / 250000000000000000)) (a := (526624077378672729 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS2_hz49 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B (670098237428975063 / 1000000000000000000) (670098237429003873 / 1000000000000000000) (kdot ((509307035416793117 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (570185432419150983 / 1000000000000000000)) (a := (6477605960621601 / 12500000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (285092716209575491 / 500000000000000000)) (a := (518208476849682827 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS2_hz50 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B (664740699735827063 / 1000000000000000000) (670098237429003873 / 1000000000000000000) (kdot (nc1 x c)) := bkdot (lowCoarseS2_hz46 hx hc) (lowCoarseS2_hz48 hx hc).1 (lowCoarseS2_hz49 hx hc).2

theorem lowCoarseS2_hz51 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B (64 / 625) (1089 / 10000) (c^2) := bsq (lowCoarseS2_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS2_hz52 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B (8911 / 10000) (561 / 625) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS2_hz51 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS2_hz53 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B (14749702062668927 / 15625000000000000) (947417542586160899 / 1000000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (lowCoarseS2_hz52 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS2_hz54 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B (284932580677553289 / 500000000000000000) (23005145543410569 / 40000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (lowCoarseS2_hz53 hx hc) (lowCoarseS2_hz47 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS2_hz55 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B (284932580677553289 / 500000000000000000) (23005145543410569 / 40000000000000000) (npa c) := by
    convert (lowCoarseS2_hz54 hx hc) using 1 <;>
      norm_num [npa] <;> ring

theorem lowCoarseS2_hz56 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B (300478463028029993 / 1000000000000000000) (37696546268640941 / 125000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (lowCoarseS2_hz53 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS2_hz57 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B (24147316626034559 / 125000000000000000) (200326088764476217 / 1000000000000000000) (c * (kdot c)) := bmul (lowCoarseS2_hz1 hx hc) (lowCoarseS2_hz47 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS2_hz58 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B (6259523391472111 / 62500000000000000) (6774614821303191 / 62500000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (lowCoarseS2_hz56 hx hc) (lowCoarseS2_hz57 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS2_hz59 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B (6259523391472111 / 62500000000000000) (6774614821303191 / 62500000000000000) (npp c) := by
    convert (lowCoarseS2_hz58 hx hc) using 1 <;>
      norm_num [npp] <;> ring

theorem lowCoarseS2_hz60 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B 0 (23 / 4000) ((46 : ℝ) * x) := bmul (bpoint (46 : ℝ)) (lowCoarseS2_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS2_hz61 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B (9591663046625439083 / 1000000000000000000) (2399353261656359771 / 250000000000000000) ((√(92 : ℝ)) + ((46 : ℝ) * x)) := badd (lowCoarseS2_hz3 hx hc) (lowCoarseS2_hz60 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS2_hz62 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B (28774989139876317249 / 250000000000000000) (7198059784969079313 / 62500000000000000) ((12 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (bpoint (12 : ℝ)) (lowCoarseS2_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS2_hz63 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B 0 (14396119569938159 / 1000000000000000000) (((12 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS2_hz62 hx hc) (lowCoarseS2_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS2_hz64 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B 0 (14396119569938159 / 1000000000000000000) (nr1 x) := by
    convert (lowCoarseS2_hz63 hx hc) using 1 <;>
      norm_num [nr1] <;> ring

theorem lowCoarseS2_hz65 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B (9591663046625439083 / 125000000000000000) (2399353261656359771 / 31250000000000000) ((8 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (bpoint (8 : ℝ)) (lowCoarseS2_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS2_hz66 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B 0 (59983831541409 / 6250000000000000) (((8 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS2_hz65 hx hc) (lowCoarseS2_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS2_hz67 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B 0 (59983831541409 / 6250000000000000) (nrpp x) := by
    convert (lowCoarseS2_hz66 hx hc) using 1 <;>
      norm_num [nrpp] <;> ring

theorem lowCoarseS2_hz68 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B 0 (847791247890659 / 500000000000000000) (ne0 x) := by
    convert (lowCoarseS2_hz4 hx hc) using 1 <;>
      norm_num [ne0] <;> ring

theorem lowCoarseS2_hz69 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B (284932580677553289 / 500000000000000000) (36845297384700149 / 62500000000000000) ((npa c) + (nr1 x)) := badd (lowCoarseS2_hz55 hx hc) (lowCoarseS2_hz64 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS2_hz70 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B (284932580677553289 / 500000000000000000) (118105210604195447 / 200000000000000000) (((npa c) + (nr1 x)) / (nam x)) := bdiv (lowCoarseS2_hz69 hx hc) (lowCoarseS2_hz12 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS2_hz71 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B (284932580677553289 / 500000000000000000) (592221635516758553 / 1000000000000000000) ((((npa c) + (nr1 x)) / (nam x)) + (ne0 x)) := badd (lowCoarseS2_hz70 hx hc) (lowCoarseS2_hz68 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS2_hz72 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B (284932580677553289 / 500000000000000000) (592221635516758553 / 1000000000000000000) (nlam x c) := by
    convert (lowCoarseS2_hz71 hx hc) using 1 <;>
      norm_num [nlam] <;> ring

theorem lowCoarseS2_hz73 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS2_hz74 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B 0 (59947894041409 / 100000000000000000) ((√(23 : ℝ)) * x) := bmul (lowCoarseS2_hz73 hx hc) (lowCoarseS2_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS2_hz75 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B (1 / 2) (50059947894041409 / 100000000000000000) (((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)) := badd (bpoint ((1 / 2) : ℝ)) (lowCoarseS2_hz74 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS2_hz76 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B (176776695296636881 / 250000000000000000) (353765274914177413 / 500000000000000000) (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) := bsqrt (lowCoarseS2_hz75 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS2_hz77 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B 0 (59947894041409 / 50000000000000000) ((√(92 : ℝ)) * x) := bmul (lowCoarseS2_hz3 hx hc) (lowCoarseS2_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS2_hz78 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B (176776695296636881 / 250000000000000000) (354364753854591503 / 500000000000000000) ((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x)) := badd (lowCoarseS2_hz76 hx hc) (lowCoarseS2_hz77 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS2_hz79 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B (499999999999999999 / 1000000000000000000) (251148757548850447 / 500000000000000000) (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2) := bsq (lowCoarseS2_hz78 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS2_hz80 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B (499999999999999999 / 125000000000000000) (251148757548850447 / 62500000000000000) ((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) := bmul (bpoint (8 : ℝ)) (lowCoarseS2_hz79 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS2_hz81 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B (7673330437300351251 / 200000000000000000) (1928302689874485209 / 50000000000000000) (((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (lowCoarseS2_hz80 hx hc) (lowCoarseS2_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS2_hz82 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B 0 (2410378362343107 / 500000000000000000) ((((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS2_hz81 hx hc) (lowCoarseS2_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS2_hz83 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B 0 (2410378362343107 / 500000000000000000) (nrs x) := by
    convert (lowCoarseS2_hz82 hx hc) using 1 <;>
      norm_num [nrs] <;> ring

theorem lowCoarseS2_hz84 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B (6259523391472111 / 62500000000000000) (7374453136717281 / 62500000000000000) ((npp c) + (nrpp x)) := badd (lowCoarseS2_hz59 hx hc) (lowCoarseS2_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS2_hz85 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B (6259523391472111 / 125000000000000000) (79065728782672623 / 1000000000000000000) (if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) := bweaken (bfirst (lowCoarseS2_hz84 hx hc) (lowCoarseS2_hz50 hx hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem lowCoarseS2_hz86 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B (64949260425256331 / 200000000000000000) (10960202049192013 / 31250000000000000) ((nlam x c)^2) := bsq (lowCoarseS2_hz72 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS2_hz87 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B (61194614043766737 / 250000000000000000) (259393656325042559 / 1000000000000000000) ((nc1 x c)^2) := bsq (lowCoarseS2_hz46 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS2_hz88 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B (740606343674957441 / 1000000000000000000) (188805385956233263 / 250000000000000000) ((1 : ℝ) - ((nc1 x c)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS2_hz87 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS2_hz89 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B (860584884642391009 / 1000000000000000000) (217258708661030009 / 250000000000000000) (√((1 : ℝ) - ((nc1 x c)^2))) := bsqrt (lowCoarseS2_hz88 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS2_hz90 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B (337950893922869409 / 125000000000000000) (546030690446317649 / 200000000000000000) (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))) := bmul pi_mem (lowCoarseS2_hz89 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS2_hz91 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B (23789600680565313 / 200000000000000000) (32431345045335083 / 250000000000000000) (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2))))) := bdiv (lowCoarseS2_hz86 hx hc) (lowCoarseS2_hz90 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS2_hz92 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B (169024190534603453 / 1000000000000000000) (41758221792802591 / 200000000000000000) ((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) := badd (lowCoarseS2_hz85 hx hc) (lowCoarseS2_hz91 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS2_hz93 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B 0 (2875000000001 / 1000000000000000000) ((ne0 x)^2) := bsq (lowCoarseS2_hz68 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS2_hz94 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B (169024190534603453 / 1000000000000000000) (52198495991003239 / 250000000000000000) (((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) + ((ne0 x)^2)) := badd (lowCoarseS2_hz92 hx hc) (lowCoarseS2_hz93 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS2_hz95 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B (169024190534603453 / 1000000000000000000) (21361474068869917 / 100000000000000000) ((((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) + ((ne0 x)^2)) + (nrs x)) := badd (lowCoarseS2_hz94 hx hc) (lowCoarseS2_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS2_hz96 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B (169024190534603453 / 1000000000000000000) (21361474068869917 / 100000000000000000) (nu x c) := by
    convert (lowCoarseS2_hz95 hx hc) using 1 <;>
      norm_num [nu] <;> ring

theorem lowCoarseS2_hz97 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B (5659685076058021 / 62500000000000000) (6774614821303191 / 62500000000000000) ((npp c) - (nrpp x)) := bsub (lowCoarseS2_hz59 hx hc) (lowCoarseS2_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS2_hz98 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B 0 0 (min ((npp c) - (nrpp x)) (0 : ℝ)) := bweaken (bmin (lowCoarseS2_hz97 hx hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem lowCoarseS2_hz99 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B 0 0 ((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) := bmul (lowCoarseS2_hz50 hx hc) (lowCoarseS2_hz98 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS2_hz100 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B (-2875000000001 / 1000000000000000000) 0 (((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) - ((ne0 x)^2)) := bsub (lowCoarseS2_hz99 hx hc) (lowCoarseS2_hz93 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS2_hz101 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B (-964726344937243 / 200000000000000000) 0 ((((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) - ((ne0 x)^2)) - (nrs x)) := bsub (lowCoarseS2_hz100 hx hc) (lowCoarseS2_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS2_hz102 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B (-964726344937243 / 200000000000000000) 0 (nl x c) := by
    convert (lowCoarseS2_hz101 hx hc) using 1 <;>
      norm_num [nl] <;> ring

theorem lowCoarseS2_hz103 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B 0 (21361474068869917 / 100000000000000000) |(nu x c)| := bweaken (babs (lowCoarseS2_hz96 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS2_hz104 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B 0 (964726344937243 / 200000000000000000) |(nl x c)| := bweaken (babs (lowCoarseS2_hz102 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS2_hz105 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B 0 (21361474068869917 / 100000000000000000) (max |(nu x c)| |(nl x c)|) := bweaken (bmax (lowCoarseS2_hz103 hx hc) (lowCoarseS2_hz104 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS2_hz106 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) : B 0 (21361474068869917 / 100000000000000000) (ns x c) := by
    convert (lowCoarseS2_hz105 hx hc) using 1 <;>
      norm_num [ns] <;> ring

theorem lowCoarseS2 {x c : ℝ}
    (hx : B 0 (1/8000) x) (hc : B (8 / 25) (33 / 100) c) :
    0 < nam x ∧ 0 ≤ ndm x c ∧ ndm x c ^ 2 ≤ 2 * nap x ^ 2 ∧ nc1 x c < 1 ∧
    0 ≤ npa c - nr1 x ∧ ne0 x ≤ (npa c - nr1 x) / nap x ∧ ns x c ≤ (9 / 25) := by
  refine ⟨lt_of_lt_of_le (by norm_num) (lowCoarseS2_hz12 hx hc).1,
    le_trans (by norm_num) (lowCoarseS2_hz38 hx hc).1, ?_,
    lt_of_le_of_lt (lowCoarseS2_hz46 hx hc).2 (by norm_num), ?_, ?_, (lowCoarseS2_hz106 hx hc).2.trans (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (lowCoarseS2_hz38 hx hc).1) (lowCoarseS2_hz38 hx hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) (lowCoarseS2_hz6 hx hc).1 2
    nlinarith only [h1,h2]
  · linarith only [(lowCoarseS2_hz55 hx hc).1,(lowCoarseS2_hz64 hx hc).2]
  · have hap : 0 < nap x := lt_of_lt_of_le (by norm_num) (lowCoarseS2_hz6 hx hc).1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul (lowCoarseS2_hz68 hx hc).2 (lowCoarseS2_hz6 hx hc).2 (le_trans (by norm_num) (lowCoarseS2_hz6 hx hc).1) (by norm_num)
    linarith only [h,(lowCoarseS2_hz55 hx hc).1,(lowCoarseS2_hz64 hx hc).2]

theorem lowCoarseS3_hz0 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B 0 (1 / 8000) x := hx

theorem lowCoarseS3_hz1 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B (33 / 100) (17 / 50) c := hc

theorem lowCoarseS3_hz2 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B (6782329983125268139 / 500000000000000000) (13564659966250536279 / 1000000000000000000) (√(184 : ℝ)) := bsqrt (bpoint (184 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS3_hz3 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS3_hz4 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B 0 (847791247890659 / 500000000000000000) ((√(184 : ℝ)) * x) := bmul (lowCoarseS3_hz2 hx hc) (lowCoarseS3_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS3_hz5 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B 1 (500847791247890659 / 500000000000000000) ((1 : ℝ) + ((√(184 : ℝ)) * x)) := badd (bpoint (1 : ℝ)) (lowCoarseS3_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS3_hz6 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B 1 (500847791247890659 / 500000000000000000) (nap x) := by
    convert (lowCoarseS3_hz5 hx hc) using 1 <;>
      norm_num [nap] <;> ring

theorem lowCoarseS3_hz7 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B 0 (1 / 64000000) (x^2) := bsq (lowCoarseS3_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS3_hz8 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B 0 (1 / 32000000) ((2 : ℝ) * (x^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS3_hz7 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS3_hz9 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B (31999999 / 32000000) 1 ((1 : ℝ) - ((2 : ℝ) * (x^2))) := bsub (bpoint (1 : ℝ)) (lowCoarseS3_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS3_hz10 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B (999999984374999877 / 1000000000000000000) 1 (√((1 : ℝ) - ((2 : ℝ) * (x^2)))) := bsqrt (lowCoarseS3_hz9 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS3_hz11 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B (998304401879218559 / 1000000000000000000) 1 ((√((1 : ℝ) - ((2 : ℝ) * (x^2)))) - ((√(184 : ℝ)) * x)) := bsub (lowCoarseS3_hz10 hx hc) (lowCoarseS3_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS3_hz12 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B (998304401879218559 / 1000000000000000000) 1 (nam x) := by
    convert (lowCoarseS3_hz11 hx hc) using 1 <;>
      norm_num [nam] <;> ring

theorem lowCoarseS3_hz13 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B (607048752515971501 / 1000000000000000000) (60704875383174611 / 100000000000000000) (kdot ((33 / 100))) := by
    constructor
    · apply bkdot_lower (q := (4436000620351557 / 6250000000000000)) (a := (77155797019673041 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (709760099256249119 / 1000000000000000000)) (a := (308623187045285203 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS3_hz14 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B (1089 / 10000) (1089 / 10000) (((33 / 100) : ℝ)^2) := bsq (bpoint ((33 / 100) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS3_hz15 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B (8911 / 10000) (8911 / 10000) ((1 : ℝ) - (((33 / 100) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS3_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS3_hz16 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B (14749702062668927 / 15625000000000000) (943980932010811329 / 1000000000000000000) (√((1 : ℝ) - (((33 / 100) : ℝ)^2))) := bsqrt (lowCoarseS3_hz15 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS3_hz17 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B (300478463028029993 / 1000000000000000000) (60095692605605999 / 200000000000000000) ((√((1 : ℝ) - (((33 / 100) : ℝ)^2))) / Real.pi) := bdiv (lowCoarseS3_hz16 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS3_hz18 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B (40065217666054119 / 200000000000000000) (200326088764476217 / 1000000000000000000) (((33 / 100) : ℝ) * (kdot ((33 / 100)))) := bmul (bpoint ((33 / 100) : ℝ)) (lowCoarseS3_hz13 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS3_hz19 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B (125201137839575147 / 250000000000000000) (125201137948126553 / 250000000000000000) (((√((1 : ℝ) - (((33 / 100) : ℝ)^2))) / Real.pi) + (((33 / 100) : ℝ) * (kdot ((33 / 100))))) := badd (lowCoarseS3_hz17 hx hc) (lowCoarseS3_hz18 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS3_hz20 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B (125201137839575147 / 250000000000000000) (125201137948126553 / 250000000000000000) (kappa ((33 / 100))) := by rw [kappa_eq]; exact (lowCoarseS3_hz19 hx hc)

theorem lowCoarseS3_hz21 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B (610427078045460699 / 1000000000000000000) (610427078803118153 / 1000000000000000000) (kdot ((17 / 50))) := by
    constructor
    · apply bkdot_lower (q := (175452506649384291 / 250000000000000000)) (a := (611939714824945271 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (701810026597537163 / 1000000000000000000)) (a := (305969856817409863 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS3_hz22 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B (289 / 2500) (289 / 2500) (((17 / 50) : ℝ)^2) := bsq (bpoint ((17 / 50) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS3_hz23 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B (2211 / 2500) (2211 / 2500) ((1 : ℝ) - (((17 / 50) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS3_hz22 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS3_hz24 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B (940425435640699799 / 1000000000000000000) (4702127178203499 / 5000000000000000) (√((1 : ℝ) - (((17 / 50) : ℝ)^2))) := bsqrt (lowCoarseS3_hz23 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS3_hz25 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B (18709169586445807 / 62500000000000000) (299346713383132913 / 1000000000000000000) ((√((1 : ℝ) - (((17 / 50) : ℝ)^2))) / Real.pi) := bdiv (lowCoarseS3_hz24 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS3_hz26 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B (207545206535456637 / 1000000000000000000) (207545206793060173 / 1000000000000000000) (((17 / 50) : ℝ) * (kdot ((17 / 50)))) := bmul (bpoint ((17 / 50) : ℝ)) (lowCoarseS3_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS3_hz27 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B (506891919918589549 / 1000000000000000000) (253445960088096543 / 500000000000000000) (((√((1 : ℝ) - (((17 / 50) : ℝ)^2))) / Real.pi) + (((17 / 50) : ℝ) * (kdot ((17 / 50))))) := badd (lowCoarseS3_hz25 hx hc) (lowCoarseS3_hz26 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS3_hz28 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B (506891919918589549 / 1000000000000000000) (253445960088096543 / 500000000000000000) (kappa ((17 / 50))) := by rw [kappa_eq]; exact (lowCoarseS3_hz27 hx hc)

theorem lowCoarseS3_hz29 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B (125201137839575147 / 250000000000000000) (253445960088096543 / 500000000000000000) (kappa c) := bkappa (lowCoarseS3_hz1 hx hc) (by norm_num) (by norm_num) (lowCoarseS3_hz20 hx hc).1 (lowCoarseS3_hz28 hx hc).2

theorem lowCoarseS3_hz30 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B (246554039911903457 / 500000000000000000) (124798862160424853 / 250000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (lowCoarseS3_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS3_hz31 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B (246554039911903457 / 250000000000000000) (124798862160424853 / 125000000000000000) ((2 : ℝ) * ((1 : ℝ) - (kappa c))) := bmul (bpoint (2 : ℝ)) (lowCoarseS3_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS3_hz32 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B 0 (1 / 8000000) ((8 : ℝ) * (x^2)) := bmul (bpoint (8 : ℝ)) (lowCoarseS3_hz7 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS3_hz33 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B (246554008661903457 / 250000000000000000) (124798862160424853 / 125000000000000000) (((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2))) := bsub (lowCoarseS3_hz31 hx hc) (lowCoarseS3_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS3_hz34 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B (993084102504724333 / 1000000000000000000) (999195124729598961 / 1000000000000000000) (√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) := bsqrt (lowCoarseS3_hz33 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS3_hz35 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B (6782329983125268139 / 250000000000000000) (13564659966250536279 / 500000000000000000) ((2 : ℝ) * (√(184 : ℝ))) := bmul (bpoint (2 : ℝ)) (lowCoarseS3_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS3_hz36 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B 0 (678232998312527 / 200000000000000000) (((2 : ℝ) * (√(184 : ℝ))) * x) := bmul (lowCoarseS3_hz35 hx hc) (lowCoarseS3_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS3_hz37 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B (494846468756580849 / 500000000000000000) (999195124729598961 / 1000000000000000000) ((√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) - (((2 : ℝ) * (√(184 : ℝ))) * x)) := bsub (lowCoarseS3_hz34 hx hc) (lowCoarseS3_hz36 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS3_hz38 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B (494846468756580849 / 500000000000000000) (999195124729598961 / 1000000000000000000) (ndm x c) := by
    convert (lowCoarseS3_hz37 hx hc) using 1 <;>
      norm_num [ndm] <;> ring

theorem lowCoarseS3_hz39 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B 1 (1003394039991562637 / 1000000000000000000) ((nap x)^2) := bsq (lowCoarseS3_hz6 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS3_hz40 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B 2 (1003394039991562637 / 500000000000000000) ((2 : ℝ) * ((nap x)^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS3_hz39 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS3_hz41 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B (195898422112686197 / 200000000000000000) (499195448641699413 / 500000000000000000) ((ndm x c)^2) := bsq (lowCoarseS3_hz38 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS3_hz42 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B (500804551358300587 / 500000000000000000) (1027295969419694289 / 1000000000000000000) (((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) := bsub (lowCoarseS3_hz40 hx hc) (lowCoarseS3_hz41 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS3_hz43 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B (199322335762284863 / 200000000000000000) 1 ((nam x)^2) := bsq (lowCoarseS3_hz12 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS3_hz44 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B (199322335762284863 / 100000000000000000) 2 ((2 : ℝ) * ((nam x)^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS3_hz43 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS3_hz45 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B (500804551358300587 / 1000000000000000000) (51539430615787313 / 100000000000000000) ((((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) / ((2 : ℝ) * ((nam x)^2))) := bdiv (lowCoarseS3_hz42 hx hc) (lowCoarseS3_hz44 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS3_hz46 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B (500804551358300587 / 1000000000000000000) (51539430615787313 / 100000000000000000) (nc1 x c) := by
    convert (lowCoarseS3_hz45 hx hc) using 1 <;>
      norm_num [nc1] <;> ring

theorem lowCoarseS3_hz47 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B (607048752515971501 / 1000000000000000000) (610427078803118153 / 1000000000000000000) (kdot c) := bkdot (lowCoarseS3_hz1 hx hc) (lowCoarseS3_hz13 hx hc).1 (lowCoarseS3_hz21 hx hc).2

theorem lowCoarseS3_hz48 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B (666962460998888621 / 1000000000000000000) (33348123049946951 / 50000000000000000) (kdot ((500804551358300587 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (576730925086961917 / 1000000000000000000)) (a := (523134142947757877 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (144182731271740479 / 250000000000000000)) (a := (65391767868459839 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS3_hz49 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B (67235452555710533 / 100000000000000000) (672354525557124557 / 1000000000000000000) (kdot ((51539430615787313 / 100000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (113099693079009859 / 200000000000000000)) (a := (128666076936467531 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (282749232697524647 / 500000000000000000)) (a := (128666076936459981 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS3_hz50 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B (666962460998888621 / 1000000000000000000) (672354525557124557 / 1000000000000000000) (kdot (nc1 x c)) := bkdot (lowCoarseS3_hz46 hx hc) (lowCoarseS3_hz48 hx hc).1 (lowCoarseS3_hz49 hx hc).2

theorem lowCoarseS3_hz51 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B (1089 / 10000) (289 / 2500) (c^2) := bsq (lowCoarseS3_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS3_hz52 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B (2211 / 2500) (8911 / 10000) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS3_hz51 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS3_hz53 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B (940425435640699799 / 1000000000000000000) (943980932010811329 / 1000000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (lowCoarseS3_hz52 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS3_hz54 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B (35680255471248491 / 62500000000000000) (576231522773204447 / 1000000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (lowCoarseS3_hz53 hx hc) (lowCoarseS3_hz47 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS3_hz55 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B (35680255471248491 / 62500000000000000) (576231522773204447 / 1000000000000000000) (npa c) := by
    convert (lowCoarseS3_hz54 hx hc) using 1 <;>
      norm_num [npa] <;> ring

theorem lowCoarseS3_hz56 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B (18709169586445807 / 62500000000000000) (60095692605605999 / 200000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (lowCoarseS3_hz53 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS3_hz57 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B (40065217666054119 / 200000000000000000) (207545206793060173 / 1000000000000000000) (c * (kdot c)) := bmul (lowCoarseS3_hz1 hx hc) (lowCoarseS3_hz47 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS3_hz58 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B (91801506590072739 / 1000000000000000000) (500761873488797 / 5000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (lowCoarseS3_hz56 hx hc) (lowCoarseS3_hz57 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS3_hz59 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B (91801506590072739 / 1000000000000000000) (500761873488797 / 5000000000000000) (npp c) := by
    convert (lowCoarseS3_hz58 hx hc) using 1 <;>
      norm_num [npp] <;> ring

theorem lowCoarseS3_hz60 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B 0 (23 / 4000) ((46 : ℝ) * x) := bmul (bpoint (46 : ℝ)) (lowCoarseS3_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS3_hz61 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B (9591663046625439083 / 1000000000000000000) (2399353261656359771 / 250000000000000000) ((√(92 : ℝ)) + ((46 : ℝ) * x)) := badd (lowCoarseS3_hz3 hx hc) (lowCoarseS3_hz60 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS3_hz62 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B (28774989139876317249 / 250000000000000000) (7198059784969079313 / 62500000000000000) ((12 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (bpoint (12 : ℝ)) (lowCoarseS3_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS3_hz63 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B 0 (14396119569938159 / 1000000000000000000) (((12 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS3_hz62 hx hc) (lowCoarseS3_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS3_hz64 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B 0 (14396119569938159 / 1000000000000000000) (nr1 x) := by
    convert (lowCoarseS3_hz63 hx hc) using 1 <;>
      norm_num [nr1] <;> ring

theorem lowCoarseS3_hz65 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B (9591663046625439083 / 125000000000000000) (2399353261656359771 / 31250000000000000) ((8 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (bpoint (8 : ℝ)) (lowCoarseS3_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS3_hz66 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B 0 (59983831541409 / 6250000000000000) (((8 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS3_hz65 hx hc) (lowCoarseS3_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS3_hz67 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B 0 (59983831541409 / 6250000000000000) (nrpp x) := by
    convert (lowCoarseS3_hz66 hx hc) using 1 <;>
      norm_num [nrpp] <;> ring

theorem lowCoarseS3_hz68 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B 0 (847791247890659 / 500000000000000000) (ne0 x) := by
    convert (lowCoarseS3_hz4 hx hc) using 1 <;>
      norm_num [ne0] <;> ring

theorem lowCoarseS3_hz69 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B (35680255471248491 / 62500000000000000) (295313821171571303 / 500000000000000000) ((npa c) + (nr1 x)) := badd (lowCoarseS3_hz55 hx hc) (lowCoarseS3_hz64 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS3_hz70 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B (35680255471248491 / 62500000000000000) (591630810433510067 / 1000000000000000000) (((npa c) + (nr1 x)) / (nam x)) := bdiv (lowCoarseS3_hz69 hx hc) (lowCoarseS3_hz12 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS3_hz71 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B (35680255471248491 / 62500000000000000) (118665278585858277 / 200000000000000000) ((((npa c) + (nr1 x)) / (nam x)) + (ne0 x)) := badd (lowCoarseS3_hz70 hx hc) (lowCoarseS3_hz68 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS3_hz72 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B (35680255471248491 / 62500000000000000) (118665278585858277 / 200000000000000000) (nlam x c) := by
    convert (lowCoarseS3_hz71 hx hc) using 1 <;>
      norm_num [nlam] <;> ring

theorem lowCoarseS3_hz73 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS3_hz74 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B 0 (59947894041409 / 100000000000000000) ((√(23 : ℝ)) * x) := bmul (lowCoarseS3_hz73 hx hc) (lowCoarseS3_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS3_hz75 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B (1 / 2) (50059947894041409 / 100000000000000000) (((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)) := badd (bpoint ((1 / 2) : ℝ)) (lowCoarseS3_hz74 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS3_hz76 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B (176776695296636881 / 250000000000000000) (353765274914177413 / 500000000000000000) (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) := bsqrt (lowCoarseS3_hz75 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS3_hz77 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B 0 (59947894041409 / 50000000000000000) ((√(92 : ℝ)) * x) := bmul (lowCoarseS3_hz3 hx hc) (lowCoarseS3_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS3_hz78 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B (176776695296636881 / 250000000000000000) (354364753854591503 / 500000000000000000) ((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x)) := badd (lowCoarseS3_hz76 hx hc) (lowCoarseS3_hz77 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS3_hz79 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B (499999999999999999 / 1000000000000000000) (251148757548850447 / 500000000000000000) (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2) := bsq (lowCoarseS3_hz78 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS3_hz80 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B (499999999999999999 / 125000000000000000) (251148757548850447 / 62500000000000000) ((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) := bmul (bpoint (8 : ℝ)) (lowCoarseS3_hz79 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS3_hz81 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B (7673330437300351251 / 200000000000000000) (1928302689874485209 / 50000000000000000) (((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (lowCoarseS3_hz80 hx hc) (lowCoarseS3_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS3_hz82 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B 0 (2410378362343107 / 500000000000000000) ((((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS3_hz81 hx hc) (lowCoarseS3_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS3_hz83 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B 0 (2410378362343107 / 500000000000000000) (nrs x) := by
    convert (lowCoarseS3_hz82 hx hc) using 1 <;>
      norm_num [nrs] <;> ring

theorem lowCoarseS3_hz84 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B (91801506590072739 / 1000000000000000000) (2743744693609621 / 25000000000000000) ((npp c) + (nrpp x)) := badd (lowCoarseS3_hz59 hx hc) (lowCoarseS3_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS3_hz85 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B (45900753295036369 / 1000000000000000000) (73790766468870993 / 1000000000000000000) (if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) := bweaken (bfirst (lowCoarseS3_hz84 hx hc) (lowCoarseS3_hz50 hx hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem lowCoarseS3_hz86 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B (10184645043948463 / 31250000000000000) (2816289668371871 / 8000000000000000) ((nlam x c)^2) := bsq (lowCoarseS3_hz72 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS3_hz87 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B (25080519866118873 / 100000000000000000) (265631290819955461 / 1000000000000000000) ((nc1 x c)^2) := bsq (lowCoarseS3_hz46 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS3_hz88 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B (734368709180044539 / 1000000000000000000) (74919480133881127 / 100000000000000000) ((1 : ℝ) - ((nc1 x c)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS3_hz87 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS3_hz89 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B (428476577300336377 / 500000000000000000) (173112079455919109 / 200000000000000000) (√((1 : ℝ) - ((nc1 x c)^2))) := bsqrt (lowCoarseS3_hz88 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS3_hz90 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B (2692197734964071849 / 1000000000000000000) (2719238185331840221 / 1000000000000000000) (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))) := bmul pi_mem (lowCoarseS3_hz89 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS3_hz91 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B (119852921735349489 / 1000000000000000000) (163452058133827 / 1250000000000000) (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2))))) := bdiv (lowCoarseS3_hz86 hx hc) (lowCoarseS3_hz90 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS3_hz92 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B (82876837515192929 / 500000000000000000) (204552412975932593 / 1000000000000000000) ((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) := badd (lowCoarseS3_hz85 hx hc) (lowCoarseS3_hz91 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS3_hz93 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B 0 (2875000000001 / 1000000000000000000) ((ne0 x)^2) := bsq (lowCoarseS3_hz68 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS3_hz94 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B (82876837515192929 / 500000000000000000) (102277643987966297 / 500000000000000000) (((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) + ((ne0 x)^2)) := badd (lowCoarseS3_hz92 hx hc) (lowCoarseS3_hz93 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS3_hz95 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B (82876837515192929 / 500000000000000000) (26172005587577351 / 125000000000000000) ((((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) + ((ne0 x)^2)) + (nrs x)) := badd (lowCoarseS3_hz94 hx hc) (lowCoarseS3_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS3_hz96 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B (82876837515192929 / 500000000000000000) (26172005587577351 / 125000000000000000) (nu x c) := by
    convert (lowCoarseS3_hz95 hx hc) using 1 <;>
      norm_num [nu] <;> ring

theorem lowCoarseS3_hz97 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B (82204093543447299 / 1000000000000000000) (500761873488797 / 5000000000000000) ((npp c) - (nrpp x)) := bsub (lowCoarseS3_hz59 hx hc) (lowCoarseS3_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS3_hz98 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B 0 0 (min ((npp c) - (nrpp x)) (0 : ℝ)) := bweaken (bmin (lowCoarseS3_hz97 hx hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem lowCoarseS3_hz99 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B 0 0 ((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) := bmul (lowCoarseS3_hz50 hx hc) (lowCoarseS3_hz98 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS3_hz100 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B (-2875000000001 / 1000000000000000000) 0 (((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) - ((ne0 x)^2)) := bsub (lowCoarseS3_hz99 hx hc) (lowCoarseS3_hz93 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS3_hz101 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B (-964726344937243 / 200000000000000000) 0 ((((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) - ((ne0 x)^2)) - (nrs x)) := bsub (lowCoarseS3_hz100 hx hc) (lowCoarseS3_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS3_hz102 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B (-964726344937243 / 200000000000000000) 0 (nl x c) := by
    convert (lowCoarseS3_hz101 hx hc) using 1 <;>
      norm_num [nl] <;> ring

theorem lowCoarseS3_hz103 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B 0 (26172005587577351 / 125000000000000000) |(nu x c)| := bweaken (babs (lowCoarseS3_hz96 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS3_hz104 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B 0 (964726344937243 / 200000000000000000) |(nl x c)| := bweaken (babs (lowCoarseS3_hz102 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS3_hz105 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B 0 (26172005587577351 / 125000000000000000) (max |(nu x c)| |(nl x c)|) := bweaken (bmax (lowCoarseS3_hz103 hx hc) (lowCoarseS3_hz104 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS3_hz106 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) : B 0 (26172005587577351 / 125000000000000000) (ns x c) := by
    convert (lowCoarseS3_hz105 hx hc) using 1 <;>
      norm_num [ns] <;> ring

theorem lowCoarseS3 {x c : ℝ}
    (hx : B 0 (1/8000) x) (hc : B (33 / 100) (17 / 50) c) :
    0 < nam x ∧ 0 ≤ ndm x c ∧ ndm x c ^ 2 ≤ 2 * nap x ^ 2 ∧ nc1 x c < 1 ∧
    0 ≤ npa c - nr1 x ∧ ne0 x ≤ (npa c - nr1 x) / nap x ∧ ns x c ≤ (9 / 25) := by
  refine ⟨lt_of_lt_of_le (by norm_num) (lowCoarseS3_hz12 hx hc).1,
    le_trans (by norm_num) (lowCoarseS3_hz38 hx hc).1, ?_,
    lt_of_le_of_lt (lowCoarseS3_hz46 hx hc).2 (by norm_num), ?_, ?_, (lowCoarseS3_hz106 hx hc).2.trans (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (lowCoarseS3_hz38 hx hc).1) (lowCoarseS3_hz38 hx hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) (lowCoarseS3_hz6 hx hc).1 2
    nlinarith only [h1,h2]
  · linarith only [(lowCoarseS3_hz55 hx hc).1,(lowCoarseS3_hz64 hx hc).2]
  · have hap : 0 < nap x := lt_of_lt_of_le (by norm_num) (lowCoarseS3_hz6 hx hc).1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul (lowCoarseS3_hz68 hx hc).2 (lowCoarseS3_hz6 hx hc).2 (le_trans (by norm_num) (lowCoarseS3_hz6 hx hc).1) (by norm_num)
    linarith only [h,(lowCoarseS3_hz55 hx hc).1,(lowCoarseS3_hz64 hx hc).2]

theorem lowCoarseS4_hz0 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B 0 (1 / 8000) x := hx

theorem lowCoarseS4_hz1 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B (17 / 50) (7 / 20) c := hc

theorem lowCoarseS4_hz2 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B (6782329983125268139 / 500000000000000000) (13564659966250536279 / 1000000000000000000) (√(184 : ℝ)) := bsqrt (bpoint (184 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS4_hz3 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS4_hz4 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B 0 (847791247890659 / 500000000000000000) ((√(184 : ℝ)) * x) := bmul (lowCoarseS4_hz2 hx hc) (lowCoarseS4_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS4_hz5 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B 1 (500847791247890659 / 500000000000000000) ((1 : ℝ) + ((√(184 : ℝ)) * x)) := badd (bpoint (1 : ℝ)) (lowCoarseS4_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS4_hz6 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B 1 (500847791247890659 / 500000000000000000) (nap x) := by
    convert (lowCoarseS4_hz5 hx hc) using 1 <;>
      norm_num [nap] <;> ring

theorem lowCoarseS4_hz7 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B 0 (1 / 64000000) (x^2) := bsq (lowCoarseS4_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS4_hz8 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B 0 (1 / 32000000) ((2 : ℝ) * (x^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS4_hz7 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS4_hz9 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B (31999999 / 32000000) 1 ((1 : ℝ) - ((2 : ℝ) * (x^2))) := bsub (bpoint (1 : ℝ)) (lowCoarseS4_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS4_hz10 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B (999999984374999877 / 1000000000000000000) 1 (√((1 : ℝ) - ((2 : ℝ) * (x^2)))) := bsqrt (lowCoarseS4_hz9 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS4_hz11 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B (998304401879218559 / 1000000000000000000) 1 ((√((1 : ℝ) - ((2 : ℝ) * (x^2)))) - ((√(184 : ℝ)) * x)) := bsub (lowCoarseS4_hz10 hx hc) (lowCoarseS4_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS4_hz12 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B (998304401879218559 / 1000000000000000000) 1 (nam x) := by
    convert (lowCoarseS4_hz11 hx hc) using 1 <;>
      norm_num [nam] <;> ring

theorem lowCoarseS4_hz13 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B (610427078045460699 / 1000000000000000000) (610427078803118153 / 1000000000000000000) (kdot ((17 / 50))) := by
    constructor
    · apply bkdot_lower (q := (175452506649384291 / 250000000000000000)) (a := (611939714824945271 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (701810026597537163 / 1000000000000000000)) (a := (305969856817409863 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS4_hz14 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B (289 / 2500) (289 / 2500) (((17 / 50) : ℝ)^2) := bsq (bpoint ((17 / 50) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS4_hz15 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B (2211 / 2500) (2211 / 2500) ((1 : ℝ) - (((17 / 50) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS4_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS4_hz16 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B (940425435640699799 / 1000000000000000000) (4702127178203499 / 5000000000000000) (√((1 : ℝ) - (((17 / 50) : ℝ)^2))) := bsqrt (lowCoarseS4_hz15 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS4_hz17 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B (18709169586445807 / 62500000000000000) (299346713383132913 / 1000000000000000000) ((√((1 : ℝ) - (((17 / 50) : ℝ)^2))) / Real.pi) := bdiv (lowCoarseS4_hz16 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS4_hz18 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B (207545206535456637 / 1000000000000000000) (207545206793060173 / 1000000000000000000) (((17 / 50) : ℝ) * (kdot ((17 / 50)))) := bmul (bpoint ((17 / 50) : ℝ)) (lowCoarseS4_hz13 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS4_hz19 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B (506891919918589549 / 1000000000000000000) (253445960088096543 / 500000000000000000) (((√((1 : ℝ) - (((17 / 50) : ℝ)^2))) / Real.pi) + (((17 / 50) : ℝ) * (kdot ((17 / 50))))) := badd (lowCoarseS4_hz17 hx hc) (lowCoarseS4_hz18 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS4_hz20 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B (506891919918589549 / 1000000000000000000) (253445960088096543 / 500000000000000000) (kappa ((17 / 50))) := by rw [kappa_eq]; exact (lowCoarseS4_hz19 hx hc)

theorem lowCoarseS4_hz21 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B (24552736689413483 / 40000000000000000) (122763683533952243 / 200000000000000000) (kdot ((7 / 20))) := by
    constructor
    · apply bkdot_lower (q := (2710502603471527 / 3906250000000000)) (a := (606612611682571879 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (693888666488710911 / 1000000000000000000)) (a := (606612611000180037 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS4_hz22 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B (49 / 400) (49 / 400) (((7 / 20) : ℝ)^2) := bsq (bpoint ((7 / 20) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS4_hz23 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B (351 / 400) (351 / 400) ((1 : ℝ) - (((7 / 20) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS4_hz22 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS4_hz24 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B (93674969975975973 / 100000000000000000) (936749699759759731 / 1000000000000000000) (√((1 : ℝ) - (((7 / 20) : ℝ)^2))) := bsqrt (lowCoarseS4_hz23 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS4_hz25 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B (298176690313229203 / 1000000000000000000) (74544172578307301 / 250000000000000000) ((√((1 : ℝ) - (((7 / 20) : ℝ)^2))) / Real.pi) := bdiv (lowCoarseS4_hz24 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS4_hz26 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B (26854555754045997 / 125000000000000000) (107418223092208213 / 500000000000000000) (((7 / 20) : ℝ) * (kdot ((7 / 20)))) := bmul (bpoint ((7 / 20) : ℝ)) (lowCoarseS4_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS4_hz27 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B (513013136345597179 / 1000000000000000000) (51301313649764563 / 100000000000000000) (((√((1 : ℝ) - (((7 / 20) : ℝ)^2))) / Real.pi) + (((7 / 20) : ℝ) * (kdot ((7 / 20))))) := badd (lowCoarseS4_hz25 hx hc) (lowCoarseS4_hz26 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS4_hz28 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B (513013136345597179 / 1000000000000000000) (51301313649764563 / 100000000000000000) (kappa ((7 / 20))) := by rw [kappa_eq]; exact (lowCoarseS4_hz27 hx hc)

theorem lowCoarseS4_hz29 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B (506891919918589549 / 1000000000000000000) (51301313649764563 / 100000000000000000) (kappa c) := bkappa (lowCoarseS4_hz1 hx hc) (by norm_num) (by norm_num) (lowCoarseS4_hz20 hx hc).1 (lowCoarseS4_hz28 hx hc).2

theorem lowCoarseS4_hz30 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B (48698686350235437 / 100000000000000000) (493108080081410451 / 1000000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (lowCoarseS4_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS4_hz31 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B (48698686350235437 / 50000000000000000) (493108080081410451 / 500000000000000000) ((2 : ℝ) * ((1 : ℝ) - (kappa c))) := bmul (bpoint (2 : ℝ)) (lowCoarseS4_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS4_hz32 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B 0 (1 / 8000000) ((8 : ℝ) * (x^2)) := bmul (bpoint (8 : ℝ)) (lowCoarseS4_hz7 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS4_hz33 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B (48698680100235437 / 50000000000000000) (493108080081410451 / 500000000000000000) (((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2))) := bsub (lowCoarseS4_hz31 hx hc) (lowCoarseS4_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS4_hz34 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B (123362626152832747 / 125000000000000000) (993084165699373591 / 1000000000000000000) (√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) := bsqrt (lowCoarseS4_hz33 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS4_hz35 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B (6782329983125268139 / 250000000000000000) (13564659966250536279 / 500000000000000000) ((2 : ℝ) * (√(184 : ℝ))) := bmul (bpoint (2 : ℝ)) (lowCoarseS4_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS4_hz36 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B 0 (678232998312527 / 200000000000000000) (((2 : ℝ) * (√(184 : ℝ))) * x) := bmul (lowCoarseS4_hz35 hx hc) (lowCoarseS4_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS4_hz37 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B (983509844231099341 / 1000000000000000000) (993084165699373591 / 1000000000000000000) ((√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) - (((2 : ℝ) * (√(184 : ℝ))) * x)) := bsub (lowCoarseS4_hz34 hx hc) (lowCoarseS4_hz36 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS4_hz38 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B (983509844231099341 / 1000000000000000000) (993084165699373591 / 1000000000000000000) (ndm x c) := by
    convert (lowCoarseS4_hz37 hx hc) using 1 <;>
      norm_num [ndm] <;> ring

theorem lowCoarseS4_hz39 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B 1 (1003394039991562637 / 1000000000000000000) ((nap x)^2) := bsq (lowCoarseS4_hz6 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS4_hz40 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B 2 (1003394039991562637 / 500000000000000000) ((2 : ℝ) * ((nap x)^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS4_hz39 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS4_hz41 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B (967291613699481289 / 1000000000000000000) (986216160162820903 / 1000000000000000000) ((ndm x c)^2) := bsq (lowCoarseS4_hz38 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS4_hz42 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B (1013783839837179097 / 1000000000000000000) (207899293256728797 / 200000000000000000) (((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) := bsub (lowCoarseS4_hz40 hx hc) (lowCoarseS4_hz41 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS4_hz43 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B (199322335762284863 / 200000000000000000) 1 ((nam x)^2) := bsq (lowCoarseS4_hz12 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS4_hz44 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B (199322335762284863 / 100000000000000000) 2 ((2 : ℝ) * ((nam x)^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS4_hz43 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS4_hz45 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B (126722979979647387 / 250000000000000000) (260757647232110701 / 500000000000000000) ((((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) / ((2 : ℝ) * ((nam x)^2))) := bdiv (lowCoarseS4_hz42 hx hc) (lowCoarseS4_hz44 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS4_hz46 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B (126722979979647387 / 250000000000000000) (260757647232110701 / 500000000000000000) (nc1 x c) := by
    convert (lowCoarseS4_hz45 hx hc) using 1 <;>
      norm_num [nc1] <;> ring

theorem lowCoarseS4_hz47 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B (610427078045460699 / 1000000000000000000) (122763683533952243 / 200000000000000000) (kdot c) := bkdot (lowCoarseS4_hz1 hx hc) (lowCoarseS4_hz13 hx hc).1 (lowCoarseS4_hz21 hx hc).2

theorem lowCoarseS4_hz48 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B (669205683047231283 / 1000000000000000000) (26768227321890603 / 40000000000000000) (kdot ((126722979979647387 / 250000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (286022377120676197 / 500000000000000000)) (a := (5196104979940359 / 10000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (572044754241352393 / 1000000000000000000)) (a := (519610497993982821 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS4_hz49 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B (134926610494924897 / 200000000000000000) (674633052474637243 / 1000000000000000000) (kdot ((260757647232110701 / 500000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (112156865846939003 / 200000000000000000)) (a := (511085206033327737 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (280392164617347507 / 500000000000000000)) (a := (255542603016653849 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS4_hz50 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B (669205683047231283 / 1000000000000000000) (674633052474637243 / 1000000000000000000) (kdot (nc1 x c)) := bkdot (lowCoarseS4_hz46 hx hc) (lowCoarseS4_hz48 hx hc).1 (lowCoarseS4_hz49 hx hc).2

theorem lowCoarseS4_hz51 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B (289 / 2500) (49 / 400) (c^2) := bsq (lowCoarseS4_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS4_hz52 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B (351 / 400) (2211 / 2500) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS4_hz51 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS4_hz53 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B (93674969975975973 / 100000000000000000) (4702127178203499 / 5000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (lowCoarseS4_hz52 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS4_hz54 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B (57181738208431273 / 100000000000000000) (115450090568274043 / 200000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (lowCoarseS4_hz53 hx hc) (lowCoarseS4_hz47 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS4_hz55 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B (57181738208431273 / 100000000000000000) (115450090568274043 / 200000000000000000) (npa c) := by
    convert (lowCoarseS4_hz54 hx hc) using 1 <;>
      norm_num [npa] <;> ring

theorem lowCoarseS4_hz56 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B (298176690313229203 / 1000000000000000000) (299346713383132913 / 1000000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (lowCoarseS4_hz53 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS4_hz57 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B (207545206535456637 / 1000000000000000000) (107418223092208213 / 500000000000000000) (c * (kdot c)) := bmul (lowCoarseS4_hz1 hx hc) (lowCoarseS4_hz47 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS4_hz58 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B (83340244128812777 / 1000000000000000000) (22950376711919069 / 250000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (lowCoarseS4_hz56 hx hc) (lowCoarseS4_hz57 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS4_hz59 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B (83340244128812777 / 1000000000000000000) (22950376711919069 / 250000000000000000) (npp c) := by
    convert (lowCoarseS4_hz58 hx hc) using 1 <;>
      norm_num [npp] <;> ring

theorem lowCoarseS4_hz60 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B 0 (23 / 4000) ((46 : ℝ) * x) := bmul (bpoint (46 : ℝ)) (lowCoarseS4_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS4_hz61 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B (9591663046625439083 / 1000000000000000000) (2399353261656359771 / 250000000000000000) ((√(92 : ℝ)) + ((46 : ℝ) * x)) := badd (lowCoarseS4_hz3 hx hc) (lowCoarseS4_hz60 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS4_hz62 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B (28774989139876317249 / 250000000000000000) (7198059784969079313 / 62500000000000000) ((12 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (bpoint (12 : ℝ)) (lowCoarseS4_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS4_hz63 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B 0 (14396119569938159 / 1000000000000000000) (((12 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS4_hz62 hx hc) (lowCoarseS4_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS4_hz64 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B 0 (14396119569938159 / 1000000000000000000) (nr1 x) := by
    convert (lowCoarseS4_hz63 hx hc) using 1 <;>
      norm_num [nr1] <;> ring

theorem lowCoarseS4_hz65 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B (9591663046625439083 / 125000000000000000) (2399353261656359771 / 31250000000000000) ((8 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (bpoint (8 : ℝ)) (lowCoarseS4_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS4_hz66 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B 0 (59983831541409 / 6250000000000000) (((8 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS4_hz65 hx hc) (lowCoarseS4_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS4_hz67 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B 0 (59983831541409 / 6250000000000000) (nrpp x) := by
    convert (lowCoarseS4_hz66 hx hc) using 1 <;>
      norm_num [nrpp] <;> ring

theorem lowCoarseS4_hz68 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B 0 (847791247890659 / 500000000000000000) (ne0 x) := by
    convert (lowCoarseS4_hz4 hx hc) using 1 <;>
      norm_num [ne0] <;> ring

theorem lowCoarseS4_hz69 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B (57181738208431273 / 100000000000000000) (295823286205654187 / 500000000000000000) ((npa c) + (nr1 x)) := badd (lowCoarseS4_hz55 hx hc) (lowCoarseS4_hz64 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS4_hz70 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B (57181738208431273 / 100000000000000000) (118530294226407643 / 200000000000000000) (((npa c) + (nr1 x)) / (nam x)) := bdiv (lowCoarseS4_hz69 hx hc) (lowCoarseS4_hz12 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS4_hz71 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B (57181738208431273 / 100000000000000000) (594347053627819533 / 1000000000000000000) ((((npa c) + (nr1 x)) / (nam x)) + (ne0 x)) := badd (lowCoarseS4_hz70 hx hc) (lowCoarseS4_hz68 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS4_hz72 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B (57181738208431273 / 100000000000000000) (594347053627819533 / 1000000000000000000) (nlam x c) := by
    convert (lowCoarseS4_hz71 hx hc) using 1 <;>
      norm_num [nlam] <;> ring

theorem lowCoarseS4_hz73 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS4_hz74 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B 0 (59947894041409 / 100000000000000000) ((√(23 : ℝ)) * x) := bmul (lowCoarseS4_hz73 hx hc) (lowCoarseS4_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS4_hz75 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B (1 / 2) (50059947894041409 / 100000000000000000) (((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)) := badd (bpoint ((1 / 2) : ℝ)) (lowCoarseS4_hz74 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS4_hz76 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B (176776695296636881 / 250000000000000000) (353765274914177413 / 500000000000000000) (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) := bsqrt (lowCoarseS4_hz75 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS4_hz77 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B 0 (59947894041409 / 50000000000000000) ((√(92 : ℝ)) * x) := bmul (lowCoarseS4_hz3 hx hc) (lowCoarseS4_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS4_hz78 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B (176776695296636881 / 250000000000000000) (354364753854591503 / 500000000000000000) ((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x)) := badd (lowCoarseS4_hz76 hx hc) (lowCoarseS4_hz77 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS4_hz79 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B (499999999999999999 / 1000000000000000000) (251148757548850447 / 500000000000000000) (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2) := bsq (lowCoarseS4_hz78 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS4_hz80 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B (499999999999999999 / 125000000000000000) (251148757548850447 / 62500000000000000) ((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) := bmul (bpoint (8 : ℝ)) (lowCoarseS4_hz79 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS4_hz81 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B (7673330437300351251 / 200000000000000000) (1928302689874485209 / 50000000000000000) (((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (lowCoarseS4_hz80 hx hc) (lowCoarseS4_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS4_hz82 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B 0 (2410378362343107 / 500000000000000000) ((((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS4_hz81 hx hc) (lowCoarseS4_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS4_hz83 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B 0 (2410378362343107 / 500000000000000000) (nrs x) := by
    convert (lowCoarseS4_hz82 hx hc) using 1 <;>
      norm_num [nrs] <;> ring

theorem lowCoarseS4_hz84 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B (83340244128812777 / 1000000000000000000) (25349729973575429 / 250000000000000000) ((npp c) + (nrpp x)) := badd (lowCoarseS4_hz59 hx hc) (lowCoarseS4_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS4_hz85 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B (10417530516101597 / 250000000000000000) (17101765711480997 / 250000000000000000) (if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) := bweaken (bfirst (lowCoarseS4_hz84 hx hc) (lowCoarseS4_hz50 hx hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem lowCoarseS4_hz86 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B (326975118453756893 / 1000000000000000000) (88312105039017547 / 250000000000000000) ((nlam x c)^2) := bsq (lowCoarseS4_hz72 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS4_hz87 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B (256939418478753799 / 1000000000000000000) (271978202360103559 / 1000000000000000000) ((nc1 x c)^2) := bsq (lowCoarseS4_hz46 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS4_hz88 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B (728021797639896441 / 1000000000000000000) (743060581521246201 / 1000000000000000000) ((1 : ℝ) - ((nc1 x c)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS4_hz87 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS4_hz89 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B (853241933826447867 / 1000000000000000000) (862009617998109231 / 1000000000000000000) (√((1 : ℝ) - ((nc1 x c)^2))) := bsqrt (lowCoarseS4_hz88 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS4_hz90 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B (2680538591043917119 / 1000000000000000000) (2708083083226603973 / 1000000000000000000) (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))) := bmul pi_mem (lowCoarseS4_hz89 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS4_hz91 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B (120740430926578271 / 1000000000000000000) (32945657016124141 / 250000000000000000) (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2))))) := bdiv (lowCoarseS4_hz86 hx hc) (lowCoarseS4_hz90 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS4_hz92 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B (162410552990984659 / 1000000000000000000) (25023711363802569 / 125000000000000000) ((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) := badd (lowCoarseS4_hz85 hx hc) (lowCoarseS4_hz91 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS4_hz93 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B 0 (2875000000001 / 1000000000000000000) ((ne0 x)^2) := bsq (lowCoarseS4_hz68 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS4_hz94 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B (162410552990984659 / 1000000000000000000) (200192565910420553 / 1000000000000000000) (((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) + ((ne0 x)^2)) := badd (lowCoarseS4_hz92 hx hc) (lowCoarseS4_hz93 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS4_hz95 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B (162410552990984659 / 1000000000000000000) (205013322635106767 / 1000000000000000000) ((((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) + ((ne0 x)^2)) + (nrs x)) := badd (lowCoarseS4_hz94 hx hc) (lowCoarseS4_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS4_hz96 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B (162410552990984659 / 1000000000000000000) (205013322635106767 / 1000000000000000000) (nu x c) := by
    convert (lowCoarseS4_hz95 hx hc) using 1 <;>
      norm_num [nu] <;> ring

theorem lowCoarseS4_hz97 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B (73742831082187337 / 1000000000000000000) (22950376711919069 / 250000000000000000) ((npp c) - (nrpp x)) := bsub (lowCoarseS4_hz59 hx hc) (lowCoarseS4_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS4_hz98 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B 0 0 (min ((npp c) - (nrpp x)) (0 : ℝ)) := bweaken (bmin (lowCoarseS4_hz97 hx hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem lowCoarseS4_hz99 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B 0 0 ((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) := bmul (lowCoarseS4_hz50 hx hc) (lowCoarseS4_hz98 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS4_hz100 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B (-2875000000001 / 1000000000000000000) 0 (((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) - ((ne0 x)^2)) := bsub (lowCoarseS4_hz99 hx hc) (lowCoarseS4_hz93 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS4_hz101 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B (-964726344937243 / 200000000000000000) 0 ((((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) - ((ne0 x)^2)) - (nrs x)) := bsub (lowCoarseS4_hz100 hx hc) (lowCoarseS4_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS4_hz102 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B (-964726344937243 / 200000000000000000) 0 (nl x c) := by
    convert (lowCoarseS4_hz101 hx hc) using 1 <;>
      norm_num [nl] <;> ring

theorem lowCoarseS4_hz103 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B 0 (205013322635106767 / 1000000000000000000) |(nu x c)| := bweaken (babs (lowCoarseS4_hz96 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS4_hz104 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B 0 (964726344937243 / 200000000000000000) |(nl x c)| := bweaken (babs (lowCoarseS4_hz102 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS4_hz105 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B 0 (205013322635106767 / 1000000000000000000) (max |(nu x c)| |(nl x c)|) := bweaken (bmax (lowCoarseS4_hz103 hx hc) (lowCoarseS4_hz104 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS4_hz106 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) : B 0 (205013322635106767 / 1000000000000000000) (ns x c) := by
    convert (lowCoarseS4_hz105 hx hc) using 1 <;>
      norm_num [ns] <;> ring

theorem lowCoarseS4 {x c : ℝ}
    (hx : B 0 (1/8000) x) (hc : B (17 / 50) (7 / 20) c) :
    0 < nam x ∧ 0 ≤ ndm x c ∧ ndm x c ^ 2 ≤ 2 * nap x ^ 2 ∧ nc1 x c < 1 ∧
    0 ≤ npa c - nr1 x ∧ ne0 x ≤ (npa c - nr1 x) / nap x ∧ ns x c ≤ (9 / 25) := by
  refine ⟨lt_of_lt_of_le (by norm_num) (lowCoarseS4_hz12 hx hc).1,
    le_trans (by norm_num) (lowCoarseS4_hz38 hx hc).1, ?_,
    lt_of_le_of_lt (lowCoarseS4_hz46 hx hc).2 (by norm_num), ?_, ?_, (lowCoarseS4_hz106 hx hc).2.trans (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (lowCoarseS4_hz38 hx hc).1) (lowCoarseS4_hz38 hx hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) (lowCoarseS4_hz6 hx hc).1 2
    nlinarith only [h1,h2]
  · linarith only [(lowCoarseS4_hz55 hx hc).1,(lowCoarseS4_hz64 hx hc).2]
  · have hap : 0 < nap x := lt_of_lt_of_le (by norm_num) (lowCoarseS4_hz6 hx hc).1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul (lowCoarseS4_hz68 hx hc).2 (lowCoarseS4_hz6 hx hc).2 (le_trans (by norm_num) (lowCoarseS4_hz6 hx hc).1) (by norm_num)
    linarith only [h,(lowCoarseS4_hz55 hx hc).1,(lowCoarseS4_hz64 hx hc).2]

theorem lowCoarseS5_hz0 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B 0 (1 / 8000) x := hx

theorem lowCoarseS5_hz1 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B (7 / 20) (9 / 25) c := hc

theorem lowCoarseS5_hz2 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B (6782329983125268139 / 500000000000000000) (13564659966250536279 / 1000000000000000000) (√(184 : ℝ)) := bsqrt (bpoint (184 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS5_hz3 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS5_hz4 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B 0 (847791247890659 / 500000000000000000) ((√(184 : ℝ)) * x) := bmul (lowCoarseS5_hz2 hx hc) (lowCoarseS5_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS5_hz5 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B 1 (500847791247890659 / 500000000000000000) ((1 : ℝ) + ((√(184 : ℝ)) * x)) := badd (bpoint (1 : ℝ)) (lowCoarseS5_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS5_hz6 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B 1 (500847791247890659 / 500000000000000000) (nap x) := by
    convert (lowCoarseS5_hz5 hx hc) using 1 <;>
      norm_num [nap] <;> ring

theorem lowCoarseS5_hz7 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B 0 (1 / 64000000) (x^2) := bsq (lowCoarseS5_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS5_hz8 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B 0 (1 / 32000000) ((2 : ℝ) * (x^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS5_hz7 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS5_hz9 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B (31999999 / 32000000) 1 ((1 : ℝ) - ((2 : ℝ) * (x^2))) := bsub (bpoint (1 : ℝ)) (lowCoarseS5_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS5_hz10 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B (999999984374999877 / 1000000000000000000) 1 (√((1 : ℝ) - ((2 : ℝ) * (x^2)))) := bsqrt (lowCoarseS5_hz9 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS5_hz11 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B (998304401879218559 / 1000000000000000000) 1 ((√((1 : ℝ) - ((2 : ℝ) * (x^2)))) - ((√(184 : ℝ)) * x)) := bsub (lowCoarseS5_hz10 hx hc) (lowCoarseS5_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS5_hz12 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B (998304401879218559 / 1000000000000000000) 1 (nam x) := by
    convert (lowCoarseS5_hz11 hx hc) using 1 <;>
      norm_num [nam] <;> ring

theorem lowCoarseS5_hz13 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B (24552736689413483 / 40000000000000000) (122763683533952243 / 200000000000000000) (kdot ((7 / 20))) := by
    constructor
    · apply bkdot_lower (q := (2710502603471527 / 3906250000000000)) (a := (606612611682571879 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (693888666488710911 / 1000000000000000000)) (a := (606612611000180037 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS5_hz14 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B (49 / 400) (49 / 400) (((7 / 20) : ℝ)^2) := bsq (bpoint ((7 / 20) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS5_hz15 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B (351 / 400) (351 / 400) ((1 : ℝ) - (((7 / 20) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS5_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS5_hz16 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B (93674969975975973 / 100000000000000000) (936749699759759731 / 1000000000000000000) (√((1 : ℝ) - (((7 / 20) : ℝ)^2))) := bsqrt (lowCoarseS5_hz15 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS5_hz17 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B (298176690313229203 / 1000000000000000000) (74544172578307301 / 250000000000000000) ((√((1 : ℝ) - (((7 / 20) : ℝ)^2))) / Real.pi) := bdiv (lowCoarseS5_hz16 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS5_hz18 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B (26854555754045997 / 125000000000000000) (107418223092208213 / 500000000000000000) (((7 / 20) : ℝ) * (kdot ((7 / 20)))) := bmul (bpoint ((7 / 20) : ℝ)) (lowCoarseS5_hz13 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS5_hz19 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B (513013136345597179 / 1000000000000000000) (51301313649764563 / 100000000000000000) (((√((1 : ℝ) - (((7 / 20) : ℝ)^2))) / Real.pi) + (((7 / 20) : ℝ) * (kdot ((7 / 20))))) := badd (lowCoarseS5_hz17 hx hc) (lowCoarseS5_hz18 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS5_hz20 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B (513013136345597179 / 1000000000000000000) (51301313649764563 / 100000000000000000) (kappa ((7 / 20))) := by rw [kappa_eq]; exact (lowCoarseS5_hz19 hx hc)

theorem lowCoarseS5_hz21 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B (77152913900796081 / 125000000000000000) (617223311454350643 / 1000000000000000000) (kdot ((9 / 25))) := by
    constructor
    · apply bkdot_lower (q := (13719886811400707 / 20000000000000000)) (a := (120252843347949879 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (685994340570035349 / 1000000000000000000)) (a := (601264216350220189 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS5_hz22 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B (81 / 625) (81 / 625) (((9 / 25) : ℝ)^2) := bsq (bpoint ((9 / 25) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS5_hz23 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B (544 / 625) (544 / 625) ((1 : ℝ) - (((9 / 25) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS5_hz22 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS5_hz24 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B (37318092127009923 / 40000000000000000) (233238075793812019 / 250000000000000000) (√((1 : ℝ) - (((9 / 25) : ℝ)^2))) := bsqrt (lowCoarseS5_hz23 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS5_hz25 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B (296967941438618583 / 1000000000000000000) (37120992679827323 / 125000000000000000) ((√((1 : ℝ) - (((9 / 25) : ℝ)^2))) / Real.pi) := bdiv (lowCoarseS5_hz24 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS5_hz26 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B (222200392034292713 / 1000000000000000000) (27775049015445779 / 125000000000000000) (((9 / 25) : ℝ) * (kdot ((9 / 25)))) := bmul (bpoint ((9 / 25) : ℝ)) (lowCoarseS5_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS5_hz27 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B (8112005210514239 / 15625000000000000) (32448020847636551 / 62500000000000000) (((√((1 : ℝ) - (((9 / 25) : ℝ)^2))) / Real.pi) + (((9 / 25) : ℝ) * (kdot ((9 / 25))))) := badd (lowCoarseS5_hz25 hx hc) (lowCoarseS5_hz26 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS5_hz28 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B (8112005210514239 / 15625000000000000) (32448020847636551 / 62500000000000000) (kappa ((9 / 25))) := by rw [kappa_eq]; exact (lowCoarseS5_hz27 hx hc)

theorem lowCoarseS5_hz29 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B (513013136345597179 / 1000000000000000000) (32448020847636551 / 62500000000000000) (kappa c) := bkappa (lowCoarseS5_hz1 hx hc) (by norm_num) (by norm_num) (lowCoarseS5_hz20 hx hc).1 (lowCoarseS5_hz28 hx hc).2

theorem lowCoarseS5_hz30 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B (30051979152363449 / 62500000000000000) (486986863654402821 / 1000000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (lowCoarseS5_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS5_hz31 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B (30051979152363449 / 31250000000000000) (486986863654402821 / 500000000000000000) ((2 : ℝ) * ((1 : ℝ) - (kappa c))) := bmul (bpoint (2 : ℝ)) (lowCoarseS5_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS5_hz32 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B 0 (1 / 8000000) ((8 : ℝ) * (x^2)) := bmul (bpoint (8 : ℝ)) (lowCoarseS5_hz7 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS5_hz33 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B (30051975246113449 / 31250000000000000) (486986863654402821 / 500000000000000000) (((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2))) := bsub (lowCoarseS5_hz31 hx hc) (lowCoarseS5_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS5_hz34 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B (980644282028723383 / 1000000000000000000) (986901072706279737 / 1000000000000000000) (√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) := bsqrt (lowCoarseS5_hz33 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS5_hz35 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B (6782329983125268139 / 250000000000000000) (13564659966250536279 / 500000000000000000) ((2 : ℝ) * (√(184 : ℝ))) := bmul (bpoint (2 : ℝ)) (lowCoarseS5_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS5_hz36 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B 0 (678232998312527 / 200000000000000000) (((2 : ℝ) * (√(184 : ℝ))) * x) := bmul (lowCoarseS5_hz35 hx hc) (lowCoarseS5_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS5_hz37 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B (244313279259290187 / 250000000000000000) (986901072706279737 / 1000000000000000000) ((√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) - (((2 : ℝ) * (√(184 : ℝ))) * x)) := bsub (lowCoarseS5_hz34 hx hc) (lowCoarseS5_hz36 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS5_hz38 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B (244313279259290187 / 250000000000000000) (986901072706279737 / 1000000000000000000) (ndm x c) := by
    convert (lowCoarseS5_hz37 hx hc) using 1 <;>
      norm_num [ndm] <;> ring

theorem lowCoarseS5_hz39 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B 1 (1003394039991562637 / 1000000000000000000) ((nap x)^2) := bsq (lowCoarseS5_hz6 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS5_hz40 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B 2 (1003394039991562637 / 500000000000000000) ((2 : ℝ) * ((nap x)^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS5_hz39 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS5_hz41 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B (477511827379423301 / 500000000000000000) (243493431827201411 / 250000000000000000) ((ndm x c)^2) := bsq (lowCoarseS5_hz38 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS5_hz42 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B (256506568172798589 / 250000000000000000) (65735276576517417 / 62500000000000000) (((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) := bsub (lowCoarseS5_hz40 hx hc) (lowCoarseS5_hz41 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS5_hz43 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B (199322335762284863 / 200000000000000000) 1 ((nam x)^2) := bsq (lowCoarseS5_hz12 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS5_hz44 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B (199322335762284863 / 100000000000000000) 2 ((2 : ℝ) * ((nam x)^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS5_hz43 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS5_hz45 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B (256506568172798589 / 500000000000000000) (527670128489077331 / 1000000000000000000) ((((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) / ((2 : ℝ) * ((nam x)^2))) := bdiv (lowCoarseS5_hz42 hx hc) (lowCoarseS5_hz44 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS5_hz46 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B (256506568172798589 / 500000000000000000) (527670128489077331 / 1000000000000000000) (nc1 x c) := by
    convert (lowCoarseS5_hz45 hx hc) using 1 <;>
      norm_num [nc1] <;> ring

theorem lowCoarseS5_hz47 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B (24552736689413483 / 40000000000000000) (617223311454350643 / 1000000000000000000) (kdot c) := bkdot (lowCoarseS5_hz1 hx hc) (lowCoarseS5_hz13 hx hc).1 (lowCoarseS5_hz21 hx hc).2

theorem lowCoarseS5_hz48 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B (8393384895103881 / 12500000000000000) (67147079160833301 / 100000000000000000) (kdot ((256506568172798589 / 500000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (567331991497803811 / 1000000000000000000)) (a := (16126639805828157 / 31250000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (56733199149780381 / 100000000000000000)) (a := (258026236893232817 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS5_hz49 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B (135386855045013779 / 200000000000000000) (676934275225077311 / 1000000000000000000) (kdot ((527670128489077331 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (556042404774024919 / 1000000000000000000)) (a := (507470453789792809 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (278021202387012459 / 500000000000000000)) (a := (50747045378977959 / 100000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS5_hz50 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B (8393384895103881 / 12500000000000000) (676934275225077311 / 1000000000000000000) (kdot (nc1 x c)) := bkdot (lowCoarseS5_hz46 hx hc) (lowCoarseS5_hz48 hx hc).1 (lowCoarseS5_hz49 hx hc).2

theorem lowCoarseS5_hz51 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B (49 / 400) (81 / 625) (c^2) := bsq (lowCoarseS5_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS5_hz52 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B (544 / 625) (351 / 400) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS5_hz51 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS5_hz53 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B (37318092127009923 / 40000000000000000) (936749699759759731 / 1000000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (lowCoarseS5_hz52 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS5_hz54 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B (572663306091093113 / 1000000000000000000) (115636750337917527 / 200000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (lowCoarseS5_hz53 hx hc) (lowCoarseS5_hz47 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS5_hz55 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B (572663306091093113 / 1000000000000000000) (115636750337917527 / 200000000000000000) (npa c) := by
    convert (lowCoarseS5_hz54 hx hc) using 1 <;>
      norm_num [npa] <;> ring

theorem lowCoarseS5_hz56 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B (296967941438618583 / 1000000000000000000) (74544172578307301 / 250000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (lowCoarseS5_hz53 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS5_hz57 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B (26854555754045997 / 125000000000000000) (27775049015445779 / 125000000000000000) (c * (kdot c)) := bmul (lowCoarseS5_hz1 hx hc) (lowCoarseS5_hz47 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS5_hz58 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B (74767549315052351 / 1000000000000000000) (20835061070215307 / 250000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (lowCoarseS5_hz56 hx hc) (lowCoarseS5_hz57 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS5_hz59 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B (74767549315052351 / 1000000000000000000) (20835061070215307 / 250000000000000000) (npp c) := by
    convert (lowCoarseS5_hz58 hx hc) using 1 <;>
      norm_num [npp] <;> ring

theorem lowCoarseS5_hz60 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B 0 (23 / 4000) ((46 : ℝ) * x) := bmul (bpoint (46 : ℝ)) (lowCoarseS5_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS5_hz61 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B (9591663046625439083 / 1000000000000000000) (2399353261656359771 / 250000000000000000) ((√(92 : ℝ)) + ((46 : ℝ) * x)) := badd (lowCoarseS5_hz3 hx hc) (lowCoarseS5_hz60 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS5_hz62 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B (28774989139876317249 / 250000000000000000) (7198059784969079313 / 62500000000000000) ((12 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (bpoint (12 : ℝ)) (lowCoarseS5_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS5_hz63 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B 0 (14396119569938159 / 1000000000000000000) (((12 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS5_hz62 hx hc) (lowCoarseS5_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS5_hz64 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B 0 (14396119569938159 / 1000000000000000000) (nr1 x) := by
    convert (lowCoarseS5_hz63 hx hc) using 1 <;>
      norm_num [nr1] <;> ring

theorem lowCoarseS5_hz65 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B (9591663046625439083 / 125000000000000000) (2399353261656359771 / 31250000000000000) ((8 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (bpoint (8 : ℝ)) (lowCoarseS5_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS5_hz66 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B 0 (59983831541409 / 6250000000000000) (((8 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS5_hz65 hx hc) (lowCoarseS5_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS5_hz67 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B 0 (59983831541409 / 6250000000000000) (nrpp x) := by
    convert (lowCoarseS5_hz66 hx hc) using 1 <;>
      norm_num [nrpp] <;> ring

theorem lowCoarseS5_hz68 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B 0 (847791247890659 / 500000000000000000) (ne0 x) := by
    convert (lowCoarseS5_hz4 hx hc) using 1 <;>
      norm_num [ne0] <;> ring

theorem lowCoarseS5_hz69 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B (572663306091093113 / 1000000000000000000) (296289935629762897 / 500000000000000000) ((npa c) + (nr1 x)) := badd (lowCoarseS5_hz55 hx hc) (lowCoarseS5_hz64 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS5_hz70 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B (572663306091093113 / 1000000000000000000) (29679317758393497 / 50000000000000000) (((npa c) + (nr1 x)) / (nam x)) := bdiv (lowCoarseS5_hz69 hx hc) (lowCoarseS5_hz12 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS5_hz71 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B (572663306091093113 / 1000000000000000000) (297640968831825629 / 500000000000000000) ((((npa c) + (nr1 x)) / (nam x)) + (ne0 x)) := badd (lowCoarseS5_hz70 hx hc) (lowCoarseS5_hz68 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS5_hz72 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B (572663306091093113 / 1000000000000000000) (297640968831825629 / 500000000000000000) (nlam x c) := by
    convert (lowCoarseS5_hz71 hx hc) using 1 <;>
      norm_num [nlam] <;> ring

theorem lowCoarseS5_hz73 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS5_hz74 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B 0 (59947894041409 / 100000000000000000) ((√(23 : ℝ)) * x) := bmul (lowCoarseS5_hz73 hx hc) (lowCoarseS5_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS5_hz75 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B (1 / 2) (50059947894041409 / 100000000000000000) (((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)) := badd (bpoint ((1 / 2) : ℝ)) (lowCoarseS5_hz74 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS5_hz76 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B (176776695296636881 / 250000000000000000) (353765274914177413 / 500000000000000000) (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) := bsqrt (lowCoarseS5_hz75 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS5_hz77 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B 0 (59947894041409 / 50000000000000000) ((√(92 : ℝ)) * x) := bmul (lowCoarseS5_hz3 hx hc) (lowCoarseS5_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS5_hz78 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B (176776695296636881 / 250000000000000000) (354364753854591503 / 500000000000000000) ((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x)) := badd (lowCoarseS5_hz76 hx hc) (lowCoarseS5_hz77 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS5_hz79 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B (499999999999999999 / 1000000000000000000) (251148757548850447 / 500000000000000000) (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2) := bsq (lowCoarseS5_hz78 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS5_hz80 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B (499999999999999999 / 125000000000000000) (251148757548850447 / 62500000000000000) ((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) := bmul (bpoint (8 : ℝ)) (lowCoarseS5_hz79 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS5_hz81 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B (7673330437300351251 / 200000000000000000) (1928302689874485209 / 50000000000000000) (((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (lowCoarseS5_hz80 hx hc) (lowCoarseS5_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS5_hz82 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B 0 (2410378362343107 / 500000000000000000) ((((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS5_hz81 hx hc) (lowCoarseS5_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS5_hz83 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B 0 (2410378362343107 / 500000000000000000) (nrs x) := by
    convert (lowCoarseS5_hz82 hx hc) using 1 <;>
      norm_num [nrs] <;> ring

theorem lowCoarseS5_hz84 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B (74767549315052351 / 1000000000000000000) (23234414331871667 / 250000000000000000) ((npp c) + (nrpp x)) := badd (lowCoarseS5_hz59 hx hc) (lowCoarseS5_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS5_hz85 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B (1495350986301047 / 40000000000000000) (1966021428253087 / 31250000000000000) (if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) := bweaken (bfirst (lowCoarseS5_hz84 hx hc) (lowCoarseS5_hz50 hx hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem lowCoarseS5_hz86 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B (163971631071590501 / 500000000000000000) (354360585308591183 / 1000000000000000000) ((nlam x c)^2) := bsq (lowCoarseS5_hz72 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS5_hz87 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B (6579561951578657 / 25000000000000000) (13921788224983969 / 50000000000000000) ((nc1 x c)^2) := bsq (lowCoarseS5_hz46 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS5_hz88 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B (36078211775016031 / 50000000000000000) (18420438048421343 / 25000000000000000) ((1 : ℝ) - ((nc1 x c)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS5_hz87 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS5_hz89 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B (424724685973255097 / 500000000000000000) (858380755805285817 / 1000000000000000000) (√((1 : ℝ) - ((nc1 x c)^2))) := bsqrt (lowCoarseS5_hz88 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS5_hz90 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B (266862390650362023 / 100000000000000000) (674170669105185047 / 250000000000000000) (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))) := bmul pi_mem (lowCoarseS5_hz89 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS5_hz91 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B (3800308813336799 / 31250000000000000) (8299234870755627 / 62500000000000000) (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2))))) := bdiv (lowCoarseS5_hz86 hx hc) (lowCoarseS5_hz90 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS5_hz92 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B (158993656684303743 / 1000000000000000000) (12231277727261801 / 62500000000000000) ((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) := badd (lowCoarseS5_hz85 hx hc) (lowCoarseS5_hz91 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS5_hz93 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B 0 (2875000000001 / 1000000000000000000) ((ne0 x)^2) := bsq (lowCoarseS5_hz68 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS5_hz94 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B (158993656684303743 / 1000000000000000000) (195703318636188817 / 1000000000000000000) (((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) + ((ne0 x)^2)) := badd (lowCoarseS5_hz92 hx hc) (lowCoarseS5_hz93 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS5_hz95 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B (158993656684303743 / 1000000000000000000) (200524075360875031 / 1000000000000000000) ((((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) + ((ne0 x)^2)) + (nrs x)) := badd (lowCoarseS5_hz94 hx hc) (lowCoarseS5_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS5_hz96 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B (158993656684303743 / 1000000000000000000) (200524075360875031 / 1000000000000000000) (nu x c) := by
    convert (lowCoarseS5_hz95 hx hc) using 1 <;>
      norm_num [nu] <;> ring

theorem lowCoarseS5_hz97 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B (65170136268426911 / 1000000000000000000) (20835061070215307 / 250000000000000000) ((npp c) - (nrpp x)) := bsub (lowCoarseS5_hz59 hx hc) (lowCoarseS5_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS5_hz98 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B 0 0 (min ((npp c) - (nrpp x)) (0 : ℝ)) := bweaken (bmin (lowCoarseS5_hz97 hx hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem lowCoarseS5_hz99 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B 0 0 ((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) := bmul (lowCoarseS5_hz50 hx hc) (lowCoarseS5_hz98 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS5_hz100 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B (-2875000000001 / 1000000000000000000) 0 (((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) - ((ne0 x)^2)) := bsub (lowCoarseS5_hz99 hx hc) (lowCoarseS5_hz93 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS5_hz101 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B (-964726344937243 / 200000000000000000) 0 ((((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) - ((ne0 x)^2)) - (nrs x)) := bsub (lowCoarseS5_hz100 hx hc) (lowCoarseS5_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS5_hz102 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B (-964726344937243 / 200000000000000000) 0 (nl x c) := by
    convert (lowCoarseS5_hz101 hx hc) using 1 <;>
      norm_num [nl] <;> ring

theorem lowCoarseS5_hz103 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B 0 (200524075360875031 / 1000000000000000000) |(nu x c)| := bweaken (babs (lowCoarseS5_hz96 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS5_hz104 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B 0 (964726344937243 / 200000000000000000) |(nl x c)| := bweaken (babs (lowCoarseS5_hz102 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS5_hz105 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B 0 (200524075360875031 / 1000000000000000000) (max |(nu x c)| |(nl x c)|) := bweaken (bmax (lowCoarseS5_hz103 hx hc) (lowCoarseS5_hz104 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS5_hz106 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) : B 0 (200524075360875031 / 1000000000000000000) (ns x c) := by
    convert (lowCoarseS5_hz105 hx hc) using 1 <;>
      norm_num [ns] <;> ring

theorem lowCoarseS5 {x c : ℝ}
    (hx : B 0 (1/8000) x) (hc : B (7 / 20) (9 / 25) c) :
    0 < nam x ∧ 0 ≤ ndm x c ∧ ndm x c ^ 2 ≤ 2 * nap x ^ 2 ∧ nc1 x c < 1 ∧
    0 ≤ npa c - nr1 x ∧ ne0 x ≤ (npa c - nr1 x) / nap x ∧ ns x c ≤ (9 / 25) := by
  refine ⟨lt_of_lt_of_le (by norm_num) (lowCoarseS5_hz12 hx hc).1,
    le_trans (by norm_num) (lowCoarseS5_hz38 hx hc).1, ?_,
    lt_of_le_of_lt (lowCoarseS5_hz46 hx hc).2 (by norm_num), ?_, ?_, (lowCoarseS5_hz106 hx hc).2.trans (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (lowCoarseS5_hz38 hx hc).1) (lowCoarseS5_hz38 hx hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) (lowCoarseS5_hz6 hx hc).1 2
    nlinarith only [h1,h2]
  · linarith only [(lowCoarseS5_hz55 hx hc).1,(lowCoarseS5_hz64 hx hc).2]
  · have hap : 0 < nap x := lt_of_lt_of_le (by norm_num) (lowCoarseS5_hz6 hx hc).1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul (lowCoarseS5_hz68 hx hc).2 (lowCoarseS5_hz6 hx hc).2 (le_trans (by norm_num) (lowCoarseS5_hz6 hx hc).1) (by norm_num)
    linarith only [h,(lowCoarseS5_hz55 hx hc).1,(lowCoarseS5_hz64 hx hc).2]

theorem lowCoarseS6_hz0 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B 0 (1 / 8000) x := hx

theorem lowCoarseS6_hz1 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B (9 / 25) (37 / 100) c := hc

theorem lowCoarseS6_hz2 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B (6782329983125268139 / 500000000000000000) (13564659966250536279 / 1000000000000000000) (√(184 : ℝ)) := bsqrt (bpoint (184 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS6_hz3 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS6_hz4 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B 0 (847791247890659 / 500000000000000000) ((√(184 : ℝ)) * x) := bmul (lowCoarseS6_hz2 hx hc) (lowCoarseS6_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS6_hz5 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B 1 (500847791247890659 / 500000000000000000) ((1 : ℝ) + ((√(184 : ℝ)) * x)) := badd (bpoint (1 : ℝ)) (lowCoarseS6_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS6_hz6 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B 1 (500847791247890659 / 500000000000000000) (nap x) := by
    convert (lowCoarseS6_hz5 hx hc) using 1 <;>
      norm_num [nap] <;> ring

theorem lowCoarseS6_hz7 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B 0 (1 / 64000000) (x^2) := bsq (lowCoarseS6_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS6_hz8 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B 0 (1 / 32000000) ((2 : ℝ) * (x^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS6_hz7 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS6_hz9 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B (31999999 / 32000000) 1 ((1 : ℝ) - ((2 : ℝ) * (x^2))) := bsub (bpoint (1 : ℝ)) (lowCoarseS6_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS6_hz10 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B (999999984374999877 / 1000000000000000000) 1 (√((1 : ℝ) - ((2 : ℝ) * (x^2)))) := bsqrt (lowCoarseS6_hz9 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS6_hz11 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B (998304401879218559 / 1000000000000000000) 1 ((√((1 : ℝ) - ((2 : ℝ) * (x^2)))) - ((√(184 : ℝ)) * x)) := bsub (lowCoarseS6_hz10 hx hc) (lowCoarseS6_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS6_hz12 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B (998304401879218559 / 1000000000000000000) 1 (nam x) := by
    convert (lowCoarseS6_hz11 hx hc) using 1 <;>
      norm_num [nam] <;> ring

theorem lowCoarseS6_hz13 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B (77152913900796081 / 125000000000000000) (617223311454350643 / 1000000000000000000) (kdot ((9 / 25))) := by
    constructor
    · apply bkdot_lower (q := (13719886811400707 / 20000000000000000)) (a := (120252843347949879 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (685994340570035349 / 1000000000000000000)) (a := (601264216350220189 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS6_hz14 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B (81 / 625) (81 / 625) (((9 / 25) : ℝ)^2) := bsq (bpoint ((9 / 25) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS6_hz15 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B (544 / 625) (544 / 625) ((1 : ℝ) - (((9 / 25) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS6_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS6_hz16 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B (37318092127009923 / 40000000000000000) (233238075793812019 / 250000000000000000) (√((1 : ℝ) - (((9 / 25) : ℝ)^2))) := bsqrt (lowCoarseS6_hz15 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS6_hz17 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B (296967941438618583 / 1000000000000000000) (37120992679827323 / 125000000000000000) ((√((1 : ℝ) - (((9 / 25) : ℝ)^2))) / Real.pi) := bdiv (lowCoarseS6_hz16 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS6_hz18 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B (222200392034292713 / 1000000000000000000) (27775049015445779 / 125000000000000000) (((9 / 25) : ℝ) * (kdot ((9 / 25)))) := bmul (bpoint ((9 / 25) : ℝ)) (lowCoarseS6_hz13 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS6_hz19 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B (8112005210514239 / 15625000000000000) (32448020847636551 / 62500000000000000) (((√((1 : ℝ) - (((9 / 25) : ℝ)^2))) / Real.pi) + (((9 / 25) : ℝ) * (kdot ((9 / 25))))) := badd (lowCoarseS6_hz17 hx hc) (lowCoarseS6_hz18 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS6_hz20 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B (8112005210514239 / 15625000000000000) (32448020847636551 / 62500000000000000) (kappa ((9 / 25))) := by rw [kappa_eq]; exact (lowCoarseS6_hz19 hx hc)

theorem lowCoarseS6_hz21 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B (77580289777347187 / 125000000000000000) (620642318359675101 / 1000000000000000000) (kdot ((37 / 100))) := by
    constructor
    · apply bkdot_lower (q := (678125367906657911 / 1000000000000000000)) (a := (595893653083371583 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (67812536790665791 / 100000000000000000)) (a := (18621676651939067 / 31250000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS6_hz22 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B (1369 / 10000) (1369 / 10000) (((37 / 100) : ℝ)^2) := bsq (bpoint ((37 / 100) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS6_hz23 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B (8631 / 10000) (8631 / 10000) ((1 : ℝ) - (((37 / 100) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS6_hz22 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS6_hz24 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B (116128969254015167 / 125000000000000000) (929031754032121337 / 1000000000000000000) (√((1 : ℝ) - (((37 / 100) : ℝ)^2))) := bsqrt (lowCoarseS6_hz23 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS6_hz25 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B (18482499492943247 / 62500000000000000) (147859995943545977 / 500000000000000000) ((√((1 : ℝ) - (((37 / 100) : ℝ)^2))) / Real.pi) := bdiv (lowCoarseS6_hz24 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS6_hz26 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B (229637657740947673 / 1000000000000000000) (57409414448269947 / 250000000000000000) (((37 / 100) : ℝ) * (kdot ((37 / 100)))) := bmul (bpoint ((37 / 100) : ℝ)) (lowCoarseS6_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS6_hz27 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B (4202861197024317 / 8000000000000000) (262678824840085871 / 500000000000000000) (((√((1 : ℝ) - (((37 / 100) : ℝ)^2))) / Real.pi) + (((37 / 100) : ℝ) * (kdot ((37 / 100))))) := badd (lowCoarseS6_hz25 hx hc) (lowCoarseS6_hz26 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS6_hz28 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B (4202861197024317 / 8000000000000000) (262678824840085871 / 500000000000000000) (kappa ((37 / 100))) := by rw [kappa_eq]; exact (lowCoarseS6_hz27 hx hc)

theorem lowCoarseS6_hz29 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B (8112005210514239 / 15625000000000000) (262678824840085871 / 500000000000000000) (kappa c) := bkappa (lowCoarseS6_hz1 hx hc) (by norm_num) (by norm_num) (lowCoarseS6_hz20 hx hc).1 (lowCoarseS6_hz28 hx hc).2

theorem lowCoarseS6_hz30 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B (237321175159914129 / 500000000000000000) (7512994789485761 / 15625000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (lowCoarseS6_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS6_hz31 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B (237321175159914129 / 250000000000000000) (7512994789485761 / 7812500000000000) ((2 : ℝ) * ((1 : ℝ) - (kappa c))) := bmul (bpoint (2 : ℝ)) (lowCoarseS6_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS6_hz32 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B 0 (1 / 8000000) ((8 : ℝ) * (x^2)) := bmul (bpoint (8 : ℝ)) (lowCoarseS6_hz7 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS6_hz33 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B (237321143909914129 / 250000000000000000) (7512994789485761 / 7812500000000000) (((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2))) := bsub (lowCoarseS6_hz31 hx hc) (lowCoarseS6_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS6_hz34 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B (974312360405869281 / 1000000000000000000) (490322172926683331 / 500000000000000000) (√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) := bsqrt (lowCoarseS6_hz33 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS6_hz35 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B (6782329983125268139 / 250000000000000000) (13564659966250536279 / 500000000000000000) ((2 : ℝ) * (√(184 : ℝ))) := bmul (bpoint (2 : ℝ)) (lowCoarseS6_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS6_hz36 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B 0 (678232998312527 / 200000000000000000) (((2 : ℝ) * (√(184 : ℝ))) * x) := bmul (lowCoarseS6_hz35 hx hc) (lowCoarseS6_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS6_hz37 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B (485460597707153323 / 500000000000000000) (490322172926683331 / 500000000000000000) ((√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) - (((2 : ℝ) * (√(184 : ℝ))) * x)) := bsub (lowCoarseS6_hz34 hx hc) (lowCoarseS6_hz36 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS6_hz38 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B (485460597707153323 / 500000000000000000) (490322172926683331 / 500000000000000000) (ndm x c) := by
    convert (lowCoarseS6_hz37 hx hc) using 1 <;>
      norm_num [ndm] <;> ring

theorem lowCoarseS6_hz39 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B 1 (1003394039991562637 / 1000000000000000000) ((nap x)^2) := bsq (lowCoarseS6_hz6 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS6_hz40 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B 2 (1003394039991562637 / 500000000000000000) ((2 : ℝ) * ((nap x)^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS6_hz39 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS6_hz41 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B (117835995963093279 / 125000000000000000) (961663333054177409 / 1000000000000000000) ((ndm x c)^2) := bsq (lowCoarseS6_hz38 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS6_hz42 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B (1038336666945822591 / 1000000000000000000) (532050056139189521 / 500000000000000000) (((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) := bsub (lowCoarseS6_hz40 hx hc) (lowCoarseS6_hz41 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS6_hz43 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B (199322335762284863 / 200000000000000000) 1 ((nam x)^2) := bsq (lowCoarseS6_hz12 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS6_hz44 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B (199322335762284863 / 100000000000000000) 2 ((2 : ℝ) * ((nam x)^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS6_hz43 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS6_hz45 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B (103833666694582259 / 200000000000000000) (266929470851536317 / 500000000000000000) ((((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) / ((2 : ℝ) * ((nam x)^2))) := bdiv (lowCoarseS6_hz42 hx hc) (lowCoarseS6_hz44 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS6_hz46 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B (103833666694582259 / 200000000000000000) (266929470851536317 / 500000000000000000) (nc1 x c) := by
    convert (lowCoarseS6_hz45 hx hc) using 1 <;>
      norm_num [nc1] <;> ring

theorem lowCoarseS6_hz47 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B (77152913900796081 / 125000000000000000) (620642318359675101 / 1000000000000000000) (kdot c) := bkdot (lowCoarseS6_hz1 hx hc) (lowCoarseS6_hz13 hx hc).1 (lowCoarseS6_hz21 hx hc).2

theorem lowCoarseS6_hz48 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B (168439557598013071 / 250000000000000000) (673758230392067221 / 1000000000000000000) (kdot ((103833666694582259 / 200000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (562592037577820309 / 1000000000000000000)) (a := (512459373347231211 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (140648009394455077 / 250000000000000000)) (a := (2049837493388831 / 4000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS6_hz49 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B (679258670546394807 / 1000000000000000000) (27170346821856013 / 40000000000000000) (kdot ((266929470851536317 / 500000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (551272042126018281 / 1000000000000000000)) (a := (503819302157034823 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (13781801053150457 / 25000000000000000)) (a := (125954825539256539 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS6_hz50 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B (168439557598013071 / 250000000000000000) (27170346821856013 / 40000000000000000) (kdot (nc1 x c)) := bkdot (lowCoarseS6_hz46 hx hc) (lowCoarseS6_hz48 hx hc).1 (lowCoarseS6_hz49 hx hc).2

theorem lowCoarseS6_hz51 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B (81 / 625) (1369 / 10000) (c^2) := bsq (lowCoarseS6_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS6_hz52 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B (8631 / 10000) (544 / 625) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS6_hz51 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS6_hz53 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B (116128969254015167 / 125000000000000000) (233238075793812019 / 250000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (lowCoarseS6_hz52 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS6_hz54 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B (286710027719783279 / 500000000000000000) (14475742009042111 / 25000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (lowCoarseS6_hz53 hx hc) (lowCoarseS6_hz47 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS6_hz55 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B (286710027719783279 / 500000000000000000) (14475742009042111 / 25000000000000000) (npa c) := by
    convert (lowCoarseS6_hz54 hx hc) using 1 <;>
      norm_num [npa] <;> ring

theorem lowCoarseS6_hz56 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B (18482499492943247 / 62500000000000000) (37120992679827323 / 125000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (lowCoarseS6_hz53 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS6_hz57 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B (222200392034292713 / 1000000000000000000) (57409414448269947 / 250000000000000000) (c * (kdot c)) := bmul (lowCoarseS6_hz1 hx hc) (lowCoarseS6_hz47 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS6_hz58 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B (16520583523503041 / 250000000000000000) (74767549404325871 / 1000000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (lowCoarseS6_hz56 hx hc) (lowCoarseS6_hz57 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS6_hz59 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B (16520583523503041 / 250000000000000000) (74767549404325871 / 1000000000000000000) (npp c) := by
    convert (lowCoarseS6_hz58 hx hc) using 1 <;>
      norm_num [npp] <;> ring

theorem lowCoarseS6_hz60 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B 0 (23 / 4000) ((46 : ℝ) * x) := bmul (bpoint (46 : ℝ)) (lowCoarseS6_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS6_hz61 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B (9591663046625439083 / 1000000000000000000) (2399353261656359771 / 250000000000000000) ((√(92 : ℝ)) + ((46 : ℝ) * x)) := badd (lowCoarseS6_hz3 hx hc) (lowCoarseS6_hz60 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS6_hz62 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B (28774989139876317249 / 250000000000000000) (7198059784969079313 / 62500000000000000) ((12 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (bpoint (12 : ℝ)) (lowCoarseS6_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS6_hz63 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B 0 (14396119569938159 / 1000000000000000000) (((12 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS6_hz62 hx hc) (lowCoarseS6_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS6_hz64 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B 0 (14396119569938159 / 1000000000000000000) (nr1 x) := by
    convert (lowCoarseS6_hz63 hx hc) using 1 <;>
      norm_num [nr1] <;> ring

theorem lowCoarseS6_hz65 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B (9591663046625439083 / 125000000000000000) (2399353261656359771 / 31250000000000000) ((8 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (bpoint (8 : ℝ)) (lowCoarseS6_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS6_hz66 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B 0 (59983831541409 / 6250000000000000) (((8 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS6_hz65 hx hc) (lowCoarseS6_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS6_hz67 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B 0 (59983831541409 / 6250000000000000) (nrpp x) := by
    convert (lowCoarseS6_hz66 hx hc) using 1 <;>
      norm_num [nrpp] <;> ring

theorem lowCoarseS6_hz68 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B 0 (847791247890659 / 500000000000000000) (ne0 x) := by
    convert (lowCoarseS6_hz4 hx hc) using 1 <;>
      norm_num [ne0] <;> ring

theorem lowCoarseS6_hz69 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B (286710027719783279 / 500000000000000000) (593425799931622599 / 1000000000000000000) ((npa c) + (nr1 x)) := badd (lowCoarseS6_hz55 hx hc) (lowCoarseS6_hz64 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS6_hz70 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B (286710027719783279 / 500000000000000000) (297216860315627037 / 500000000000000000) (((npa c) + (nr1 x)) / (nam x)) := bdiv (lowCoarseS6_hz69 hx hc) (lowCoarseS6_hz12 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS6_hz71 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B (286710027719783279 / 500000000000000000) (1164315045169991 / 1953125000000000) ((((npa c) + (nr1 x)) / (nam x)) + (ne0 x)) := badd (lowCoarseS6_hz70 hx hc) (lowCoarseS6_hz68 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS6_hz72 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B (286710027719783279 / 500000000000000000) (1164315045169991 / 1953125000000000) (nlam x c) := by
    convert (lowCoarseS6_hz71 hx hc) using 1 <;>
      norm_num [nlam] <;> ring

theorem lowCoarseS6_hz73 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS6_hz74 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B 0 (59947894041409 / 100000000000000000) ((√(23 : ℝ)) * x) := bmul (lowCoarseS6_hz73 hx hc) (lowCoarseS6_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS6_hz75 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B (1 / 2) (50059947894041409 / 100000000000000000) (((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)) := badd (bpoint ((1 / 2) : ℝ)) (lowCoarseS6_hz74 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS6_hz76 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B (176776695296636881 / 250000000000000000) (353765274914177413 / 500000000000000000) (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) := bsqrt (lowCoarseS6_hz75 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS6_hz77 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B 0 (59947894041409 / 50000000000000000) ((√(92 : ℝ)) * x) := bmul (lowCoarseS6_hz3 hx hc) (lowCoarseS6_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS6_hz78 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B (176776695296636881 / 250000000000000000) (354364753854591503 / 500000000000000000) ((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x)) := badd (lowCoarseS6_hz76 hx hc) (lowCoarseS6_hz77 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS6_hz79 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B (499999999999999999 / 1000000000000000000) (251148757548850447 / 500000000000000000) (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2) := bsq (lowCoarseS6_hz78 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS6_hz80 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B (499999999999999999 / 125000000000000000) (251148757548850447 / 62500000000000000) ((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) := bmul (bpoint (8 : ℝ)) (lowCoarseS6_hz79 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS6_hz81 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B (7673330437300351251 / 200000000000000000) (1928302689874485209 / 50000000000000000) (((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (lowCoarseS6_hz80 hx hc) (lowCoarseS6_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS6_hz82 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B 0 (2410378362343107 / 500000000000000000) ((((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS6_hz81 hx hc) (lowCoarseS6_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS6_hz83 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B 0 (2410378362343107 / 500000000000000000) (nrs x) := by
    convert (lowCoarseS6_hz82 hx hc) using 1 <;>
      norm_num [nrs] <;> ring

theorem lowCoarseS6_hz84 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B (16520583523503041 / 250000000000000000) (84364962450951311 / 1000000000000000000) ((npp c) + (nrpp x)) := badd (lowCoarseS6_hz59 hx hc) (lowCoarseS6_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS6_hz85 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B (16520583523503041 / 500000000000000000) (57305632235130171 / 1000000000000000000) (if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) := bweaken (bfirst (lowCoarseS6_hz84 hx hc) (lowCoarseS6_hz50 hx hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem lowCoarseS6_hz86 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B (5137664999692431 / 15625000000000000) (355370146046724849 / 1000000000000000000) ((nlam x c)^2) := bsq (lowCoarseS6_hz72 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS6_hz87 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B (134767879240520013 / 500000000000000000) (142502684818162353 / 500000000000000000) ((nc1 x c)^2) := bsq (lowCoarseS6_hz46 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS6_hz88 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B (357497315181837647 / 500000000000000000) (365232120759479987 / 500000000000000000) ((1 : ℝ) - ((nc1 x c)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS6_hz87 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS6_hz89 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B (422786775562953037 / 500000000000000000) (427336004076113383 / 500000000000000000) (√((1 : ℝ) - ((nc1 x c)^2))) := bsqrt (lowCoarseS6_hz88 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS6_hz90 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B (2656447656286979963 / 1000000000000000000) (1342515651019935743 / 500000000000000000) (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))) := bmul pi_mem (lowCoarseS6_hz89 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS6_hz91 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B (30615151463086453 / 250000000000000000) (66888226689819197 / 500000000000000000) (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2))))) := bdiv (lowCoarseS6_hz86 hx hc) (lowCoarseS6_hz90 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS6_hz92 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B (77750886449675947 / 500000000000000000) (38216417122953713 / 200000000000000000) ((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) := badd (lowCoarseS6_hz85 hx hc) (lowCoarseS6_hz91 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS6_hz93 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B 0 (2875000000001 / 1000000000000000000) ((ne0 x)^2) := bsq (lowCoarseS6_hz68 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS6_hz94 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B (77750886449675947 / 500000000000000000) (95542480307384283 / 500000000000000000) (((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) + ((ne0 x)^2)) := badd (lowCoarseS6_hz92 hx hc) (lowCoarseS6_hz93 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS6_hz95 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B (77750886449675947 / 500000000000000000) (9795285866972739 / 50000000000000000) ((((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) + ((ne0 x)^2)) + (nrs x)) := badd (lowCoarseS6_hz94 hx hc) (lowCoarseS6_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS6_hz96 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B (77750886449675947 / 500000000000000000) (9795285866972739 / 50000000000000000) (nu x c) := by
    convert (lowCoarseS6_hz95 hx hc) using 1 <;>
      norm_num [nu] <;> ring

theorem lowCoarseS6_hz97 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B (14121230261846681 / 250000000000000000) (74767549404325871 / 1000000000000000000) ((npp c) - (nrpp x)) := bsub (lowCoarseS6_hz59 hx hc) (lowCoarseS6_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS6_hz98 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B 0 0 (min ((npp c) - (nrpp x)) (0 : ℝ)) := bweaken (bmin (lowCoarseS6_hz97 hx hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem lowCoarseS6_hz99 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B 0 0 ((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) := bmul (lowCoarseS6_hz50 hx hc) (lowCoarseS6_hz98 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS6_hz100 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B (-2875000000001 / 1000000000000000000) 0 (((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) - ((ne0 x)^2)) := bsub (lowCoarseS6_hz99 hx hc) (lowCoarseS6_hz93 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS6_hz101 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B (-964726344937243 / 200000000000000000) 0 ((((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) - ((ne0 x)^2)) - (nrs x)) := bsub (lowCoarseS6_hz100 hx hc) (lowCoarseS6_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS6_hz102 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B (-964726344937243 / 200000000000000000) 0 (nl x c) := by
    convert (lowCoarseS6_hz101 hx hc) using 1 <;>
      norm_num [nl] <;> ring

theorem lowCoarseS6_hz103 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B 0 (9795285866972739 / 50000000000000000) |(nu x c)| := bweaken (babs (lowCoarseS6_hz96 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS6_hz104 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B 0 (964726344937243 / 200000000000000000) |(nl x c)| := bweaken (babs (lowCoarseS6_hz102 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS6_hz105 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B 0 (9795285866972739 / 50000000000000000) (max |(nu x c)| |(nl x c)|) := bweaken (bmax (lowCoarseS6_hz103 hx hc) (lowCoarseS6_hz104 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS6_hz106 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) : B 0 (9795285866972739 / 50000000000000000) (ns x c) := by
    convert (lowCoarseS6_hz105 hx hc) using 1 <;>
      norm_num [ns] <;> ring

theorem lowCoarseS6 {x c : ℝ}
    (hx : B 0 (1/8000) x) (hc : B (9 / 25) (37 / 100) c) :
    0 < nam x ∧ 0 ≤ ndm x c ∧ ndm x c ^ 2 ≤ 2 * nap x ^ 2 ∧ nc1 x c < 1 ∧
    0 ≤ npa c - nr1 x ∧ ne0 x ≤ (npa c - nr1 x) / nap x ∧ ns x c ≤ (9 / 25) := by
  refine ⟨lt_of_lt_of_le (by norm_num) (lowCoarseS6_hz12 hx hc).1,
    le_trans (by norm_num) (lowCoarseS6_hz38 hx hc).1, ?_,
    lt_of_le_of_lt (lowCoarseS6_hz46 hx hc).2 (by norm_num), ?_, ?_, (lowCoarseS6_hz106 hx hc).2.trans (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (lowCoarseS6_hz38 hx hc).1) (lowCoarseS6_hz38 hx hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) (lowCoarseS6_hz6 hx hc).1 2
    nlinarith only [h1,h2]
  · linarith only [(lowCoarseS6_hz55 hx hc).1,(lowCoarseS6_hz64 hx hc).2]
  · have hap : 0 < nap x := lt_of_lt_of_le (by norm_num) (lowCoarseS6_hz6 hx hc).1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul (lowCoarseS6_hz68 hx hc).2 (lowCoarseS6_hz6 hx hc).2 (le_trans (by norm_num) (lowCoarseS6_hz6 hx hc).1) (by norm_num)
    linarith only [h,(lowCoarseS6_hz55 hx hc).1,(lowCoarseS6_hz64 hx hc).2]

theorem lowCoarseS7_hz0 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B 0 (1 / 8000) x := hx

theorem lowCoarseS7_hz1 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B (37 / 100) (19 / 50) c := hc

theorem lowCoarseS7_hz2 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B (6782329983125268139 / 500000000000000000) (13564659966250536279 / 1000000000000000000) (√(184 : ℝ)) := bsqrt (bpoint (184 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS7_hz3 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS7_hz4 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B 0 (847791247890659 / 500000000000000000) ((√(184 : ℝ)) * x) := bmul (lowCoarseS7_hz2 hx hc) (lowCoarseS7_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS7_hz5 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B 1 (500847791247890659 / 500000000000000000) ((1 : ℝ) + ((√(184 : ℝ)) * x)) := badd (bpoint (1 : ℝ)) (lowCoarseS7_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS7_hz6 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B 1 (500847791247890659 / 500000000000000000) (nap x) := by
    convert (lowCoarseS7_hz5 hx hc) using 1 <;>
      norm_num [nap] <;> ring

theorem lowCoarseS7_hz7 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B 0 (1 / 64000000) (x^2) := bsq (lowCoarseS7_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS7_hz8 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B 0 (1 / 32000000) ((2 : ℝ) * (x^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS7_hz7 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS7_hz9 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B (31999999 / 32000000) 1 ((1 : ℝ) - ((2 : ℝ) * (x^2))) := bsub (bpoint (1 : ℝ)) (lowCoarseS7_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS7_hz10 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B (999999984374999877 / 1000000000000000000) 1 (√((1 : ℝ) - ((2 : ℝ) * (x^2)))) := bsqrt (lowCoarseS7_hz9 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS7_hz11 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B (998304401879218559 / 1000000000000000000) 1 ((√((1 : ℝ) - ((2 : ℝ) * (x^2)))) - ((√(184 : ℝ)) * x)) := bsub (lowCoarseS7_hz10 hx hc) (lowCoarseS7_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS7_hz12 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B (998304401879218559 / 1000000000000000000) 1 (nam x) := by
    convert (lowCoarseS7_hz11 hx hc) using 1 <;>
      norm_num [nam] <;> ring

theorem lowCoarseS7_hz13 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B (77580289777347187 / 125000000000000000) (620642318359675101 / 1000000000000000000) (kdot ((37 / 100))) := by
    constructor
    · apply bkdot_lower (q := (678125367906657911 / 1000000000000000000)) (a := (595893653083371583 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (67812536790665791 / 100000000000000000)) (a := (18621676651939067 / 31250000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS7_hz14 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B (1369 / 10000) (1369 / 10000) (((37 / 100) : ℝ)^2) := bsq (bpoint ((37 / 100) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS7_hz15 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B (8631 / 10000) (8631 / 10000) ((1 : ℝ) - (((37 / 100) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS7_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS7_hz16 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B (116128969254015167 / 125000000000000000) (929031754032121337 / 1000000000000000000) (√((1 : ℝ) - (((37 / 100) : ℝ)^2))) := bsqrt (lowCoarseS7_hz15 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS7_hz17 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B (18482499492943247 / 62500000000000000) (147859995943545977 / 500000000000000000) ((√((1 : ℝ) - (((37 / 100) : ℝ)^2))) / Real.pi) := bdiv (lowCoarseS7_hz16 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS7_hz18 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B (229637657740947673 / 1000000000000000000) (57409414448269947 / 250000000000000000) (((37 / 100) : ℝ) * (kdot ((37 / 100)))) := bmul (bpoint ((37 / 100) : ℝ)) (lowCoarseS7_hz13 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS7_hz19 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B (4202861197024317 / 8000000000000000) (262678824840085871 / 500000000000000000) (((√((1 : ℝ) - (((37 / 100) : ℝ)^2))) / Real.pi) + (((37 / 100) : ℝ) * (kdot ((37 / 100))))) := badd (lowCoarseS7_hz17 hx hc) (lowCoarseS7_hz18 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS7_hz20 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B (4202861197024317 / 8000000000000000) (262678824840085871 / 500000000000000000) (kappa ((37 / 100))) := by rw [kappa_eq]; exact (lowCoarseS7_hz19 hx hc)

theorem lowCoarseS7_hz21 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B (312038007376789501 / 500000000000000000) (78009501854155621 / 125000000000000000) (kdot ((19 / 50))) := by
    constructor
    · apply bkdot_lower (q := (670280062599836383 / 1000000000000000000)) (a := (590500015179177013 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (335140031299918191 / 500000000000000000)) (a := (73812501881754751 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS7_hz22 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B (361 / 2500) (361 / 2500) (((19 / 50) : ℝ)^2) := bsq (bpoint ((19 / 50) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS7_hz23 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B (2139 / 2500) (2139 / 2500) ((1 : ℝ) - (((19 / 50) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS7_hz22 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS7_hz24 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B (924986486387774207 / 1000000000000000000) (3613228462452243 / 3906250000000000) (√((1 : ℝ) - (((19 / 50) : ℝ)^2))) := bsqrt (lowCoarseS7_hz23 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS7_hz25 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B (294432343203636847 / 1000000000000000000) (18402021450227303 / 62500000000000000) ((√((1 : ℝ) - (((19 / 50) : ℝ)^2))) / Real.pi) := bdiv (lowCoarseS7_hz24 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS7_hz26 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B (11857444280318001 / 50000000000000000) (463181417259049 / 1953125000000000) (((19 / 50) : ℝ) * (kdot ((19 / 50)))) := bmul (bpoint ((19 / 50) : ℝ)) (lowCoarseS7_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS7_hz27 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B (531581228809996867 / 1000000000000000000) (33223826802516871 / 62500000000000000) (((√((1 : ℝ) - (((19 / 50) : ℝ)^2))) / Real.pi) + (((19 / 50) : ℝ) * (kdot ((19 / 50))))) := badd (lowCoarseS7_hz25 hx hc) (lowCoarseS7_hz26 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS7_hz28 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B (531581228809996867 / 1000000000000000000) (33223826802516871 / 62500000000000000) (kappa ((19 / 50))) := by rw [kappa_eq]; exact (lowCoarseS7_hz27 hx hc)

theorem lowCoarseS7_hz29 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B (4202861197024317 / 8000000000000000) (33223826802516871 / 62500000000000000) (kappa c) := bkappa (lowCoarseS7_hz1 hx hc) (by norm_num) (by norm_num) (lowCoarseS7_hz20 hx hc).1 (lowCoarseS7_hz28 hx hc).2

theorem lowCoarseS7_hz30 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B (29276173197483129 / 62500000000000000) (3797138802975683 / 8000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (lowCoarseS7_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS7_hz31 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B (29276173197483129 / 31250000000000000) (3797138802975683 / 4000000000000000) ((2 : ℝ) * ((1 : ℝ) - (kappa c))) := bmul (bpoint (2 : ℝ)) (lowCoarseS7_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS7_hz32 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B 0 (1 / 8000000) ((8 : ℝ) * (x^2)) := bmul (bpoint (8 : ℝ)) (lowCoarseS7_hz7 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS7_hz33 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B (29276169291233129 / 31250000000000000) (3797138802975683 / 4000000000000000) (((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2))) := bsub (lowCoarseS7_hz31 hx hc) (lowCoarseS7_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS7_hz34 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B (967903619850375457 / 1000000000000000000) (15223631634487179 / 15625000000000000) (√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) := bsqrt (lowCoarseS7_hz33 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS7_hz35 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B (6782329983125268139 / 250000000000000000) (13564659966250536279 / 500000000000000000) ((2 : ℝ) * (√(184 : ℝ))) := bmul (bpoint (2 : ℝ)) (lowCoarseS7_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS7_hz36 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B 0 (678232998312527 / 200000000000000000) (((2 : ℝ) * (√(184 : ℝ))) * x) := bmul (lowCoarseS7_hz35 hx hc) (lowCoarseS7_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS7_hz37 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B (482256227429406411 / 500000000000000000) (15223631634487179 / 15625000000000000) ((√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) - (((2 : ℝ) * (√(184 : ℝ))) * x)) := bsub (lowCoarseS7_hz34 hx hc) (lowCoarseS7_hz36 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS7_hz38 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B (482256227429406411 / 500000000000000000) (15223631634487179 / 15625000000000000) (ndm x c) := by
    convert (lowCoarseS7_hz37 hx hc) using 1 <;>
      norm_num [ndm] <;> ring

theorem lowCoarseS7_hz39 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B 1 (1003394039991562637 / 1000000000000000000) ((nap x)^2) := bsq (lowCoarseS7_hz6 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS7_hz40 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B 2 (1003394039991562637 / 500000000000000000) ((2 : ℝ) * ((nap x)^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS7_hz39 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS7_hz41 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B (930284275577773441 / 1000000000000000000) (59330293796495047 / 62500000000000000) ((ndm x c)^2) := bsq (lowCoarseS7_hz38 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS7_hz42 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B (65669706203504953 / 62500000000000000) (1076503804405351833 / 1000000000000000000) (((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) := bsub (lowCoarseS7_hz40 hx hc) (lowCoarseS7_hz41 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS7_hz43 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B (199322335762284863 / 200000000000000000) 1 ((nam x)^2) := bsq (lowCoarseS7_hz12 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS7_hz44 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B (199322335762284863 / 100000000000000000) 2 ((2 : ℝ) * ((nam x)^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS7_hz43 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS7_hz45 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B (65669706203504953 / 125000000000000000) (135020468264179911 / 250000000000000000) ((((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) / ((2 : ℝ) * ((nam x)^2))) := bdiv (lowCoarseS7_hz42 hx hc) (lowCoarseS7_hz44 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS7_hz46 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B (65669706203504953 / 125000000000000000) (135020468264179911 / 250000000000000000) (nc1 x c) := by
    convert (lowCoarseS7_hz45 hx hc) using 1 <;>
      norm_num [nc1] <;> ring

theorem lowCoarseS7_hz47 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B (77580289777347187 / 125000000000000000) (78009501854155621 / 125000000000000000) (kdot c) := bkdot (lowCoarseS7_hz1 hx hc) (lowCoarseS7_hz13 hx hc).1 (lowCoarseS7_hz21 hx hc).2

theorem lowCoarseS7_hz48 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B (338034231030596887 / 500000000000000000) (676068462061203619 / 1000000000000000000) (kdot ((65669706203504953 / 125000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (557824263580714941 / 1000000000000000000)) (a := (127207617481824629 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (27891213179035747 / 50000000000000000)) (a := (254415234963641527 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS7_hz49 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B (170401683990873921 / 250000000000000000) (8520084199543741 / 12500000000000000) (kdot ((135020468264179911 / 250000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (34154534940763491 / 62500000000000000)) (a := (250065484812389319 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (109294511810443171 / 200000000000000000)) (a := (500130969624772991 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS7_hz50 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B (338034231030596887 / 500000000000000000) (8520084199543741 / 12500000000000000) (kdot (nc1 x c)) := bkdot (lowCoarseS7_hz46 hx hc) (lowCoarseS7_hz48 hx hc).1 (lowCoarseS7_hz49 hx hc).2

theorem lowCoarseS7_hz51 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B (1369 / 10000) (361 / 2500) (c^2) := bsq (lowCoarseS7_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS7_hz52 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B (2139 / 2500) (8631 / 10000) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS7_hz51 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS7_hz53 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B (924986486387774207 / 1000000000000000000) (929031754032121337 / 1000000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (lowCoarseS7_hz52 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS7_hz54 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B (287042878616374929 / 500000000000000000) (579786434709905747 / 1000000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (lowCoarseS7_hz53 hx hc) (lowCoarseS7_hz47 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS7_hz55 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B (287042878616374929 / 500000000000000000) (579786434709905747 / 1000000000000000000) (npa c) := by
    convert (lowCoarseS7_hz54 hx hc) using 1 <;>
      norm_num [npa] <;> ring

theorem lowCoarseS7_hz56 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B (294432343203636847 / 1000000000000000000) (147859995943545977 / 500000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (lowCoarseS7_hz53 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS7_hz57 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B (229637657740947673 / 1000000000000000000) (463181417259049 / 1953125000000000) (c * (kdot c)) := bmul (lowCoarseS7_hz1 hx hc) (lowCoarseS7_hz47 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS7_hz58 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B (57283457567003759 / 1000000000000000000) (66082334146144281 / 1000000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (lowCoarseS7_hz56 hx hc) (lowCoarseS7_hz57 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS7_hz59 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B (57283457567003759 / 1000000000000000000) (66082334146144281 / 1000000000000000000) (npp c) := by
    convert (lowCoarseS7_hz58 hx hc) using 1 <;>
      norm_num [npp] <;> ring

theorem lowCoarseS7_hz60 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B 0 (23 / 4000) ((46 : ℝ) * x) := bmul (bpoint (46 : ℝ)) (lowCoarseS7_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS7_hz61 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B (9591663046625439083 / 1000000000000000000) (2399353261656359771 / 250000000000000000) ((√(92 : ℝ)) + ((46 : ℝ) * x)) := badd (lowCoarseS7_hz3 hx hc) (lowCoarseS7_hz60 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS7_hz62 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B (28774989139876317249 / 250000000000000000) (7198059784969079313 / 62500000000000000) ((12 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (bpoint (12 : ℝ)) (lowCoarseS7_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS7_hz63 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B 0 (14396119569938159 / 1000000000000000000) (((12 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS7_hz62 hx hc) (lowCoarseS7_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS7_hz64 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B 0 (14396119569938159 / 1000000000000000000) (nr1 x) := by
    convert (lowCoarseS7_hz63 hx hc) using 1 <;>
      norm_num [nr1] <;> ring

theorem lowCoarseS7_hz65 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B (9591663046625439083 / 125000000000000000) (2399353261656359771 / 31250000000000000) ((8 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (bpoint (8 : ℝ)) (lowCoarseS7_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS7_hz66 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B 0 (59983831541409 / 6250000000000000) (((8 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS7_hz65 hx hc) (lowCoarseS7_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS7_hz67 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B 0 (59983831541409 / 6250000000000000) (nrpp x) := by
    convert (lowCoarseS7_hz66 hx hc) using 1 <;>
      norm_num [nrpp] <;> ring

theorem lowCoarseS7_hz68 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B 0 (847791247890659 / 500000000000000000) (ne0 x) := by
    convert (lowCoarseS7_hz4 hx hc) using 1 <;>
      norm_num [ne0] <;> ring

theorem lowCoarseS7_hz69 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B (287042878616374929 / 500000000000000000) (297091277139921953 / 500000000000000000) ((npa c) + (nr1 x)) := badd (lowCoarseS7_hz55 hx hc) (lowCoarseS7_hz64 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS7_hz70 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B (287042878616374929 / 500000000000000000) (595191760310130361 / 1000000000000000000) (((npa c) + (nr1 x)) / (nam x)) := bdiv (lowCoarseS7_hz69 hx hc) (lowCoarseS7_hz12 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS7_hz71 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B (287042878616374929 / 500000000000000000) (596887342805911679 / 1000000000000000000) ((((npa c) + (nr1 x)) / (nam x)) + (ne0 x)) := badd (lowCoarseS7_hz70 hx hc) (lowCoarseS7_hz68 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS7_hz72 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B (287042878616374929 / 500000000000000000) (596887342805911679 / 1000000000000000000) (nlam x c) := by
    convert (lowCoarseS7_hz71 hx hc) using 1 <;>
      norm_num [nlam] <;> ring

theorem lowCoarseS7_hz73 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS7_hz74 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B 0 (59947894041409 / 100000000000000000) ((√(23 : ℝ)) * x) := bmul (lowCoarseS7_hz73 hx hc) (lowCoarseS7_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS7_hz75 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B (1 / 2) (50059947894041409 / 100000000000000000) (((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)) := badd (bpoint ((1 / 2) : ℝ)) (lowCoarseS7_hz74 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS7_hz76 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B (176776695296636881 / 250000000000000000) (353765274914177413 / 500000000000000000) (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) := bsqrt (lowCoarseS7_hz75 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS7_hz77 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B 0 (59947894041409 / 50000000000000000) ((√(92 : ℝ)) * x) := bmul (lowCoarseS7_hz3 hx hc) (lowCoarseS7_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS7_hz78 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B (176776695296636881 / 250000000000000000) (354364753854591503 / 500000000000000000) ((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x)) := badd (lowCoarseS7_hz76 hx hc) (lowCoarseS7_hz77 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS7_hz79 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B (499999999999999999 / 1000000000000000000) (251148757548850447 / 500000000000000000) (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2) := bsq (lowCoarseS7_hz78 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS7_hz80 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B (499999999999999999 / 125000000000000000) (251148757548850447 / 62500000000000000) ((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) := bmul (bpoint (8 : ℝ)) (lowCoarseS7_hz79 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS7_hz81 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B (7673330437300351251 / 200000000000000000) (1928302689874485209 / 50000000000000000) (((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (lowCoarseS7_hz80 hx hc) (lowCoarseS7_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS7_hz82 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B 0 (2410378362343107 / 500000000000000000) ((((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS7_hz81 hx hc) (lowCoarseS7_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS7_hz83 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B 0 (2410378362343107 / 500000000000000000) (nrs x) := by
    convert (lowCoarseS7_hz82 hx hc) using 1 <;>
      norm_num [nrs] <;> ring

theorem lowCoarseS7_hz84 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B (57283457567003759 / 1000000000000000000) (75679747192769721 / 1000000000000000000) ((npp c) + (nrpp x)) := badd (lowCoarseS7_hz59 hx hc) (lowCoarseS7_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS7_hz85 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B (28641728783501879 / 1000000000000000000) (6447978182825821 / 125000000000000000) (if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) := bweaken (bfirst (lowCoarseS7_hz84 hx hc) (lowCoarseS7_hz50 hx hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem lowCoarseS7_hz86 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B (65914891331499961 / 200000000000000000) (14250980000076077 / 40000000000000000) ((nlam x c)^2) := bsq (lowCoarseS7_hz72 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS7_hz87 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B (138000330011349021 / 500000000000000000) (291688429604454633 / 1000000000000000000) ((nc1 x c)^2) := bsq (lowCoarseS7_hz46 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS7_hz88 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B (708311570395545367 / 1000000000000000000) (361999669988650979 / 500000000000000000) ((1 : ℝ) - ((nc1 x c)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS7_hz87 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS7_hz89 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B (210403120579808857 / 250000000000000000) (170176301520194281 / 200000000000000000) (√((1 : ℝ) - ((nc1 x c)^2))) := bsqrt (lowCoarseS7_hz88 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS7_hz90 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B (661000897905894943 / 250000000000000000) (1336561546677309791 / 500000000000000000) (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))) := bmul pi_mem (lowCoarseS7_hz89 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS7_hz91 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B (123291911800403603 / 1000000000000000000) (16843514373931297 / 125000000000000000) (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2))))) := bdiv (lowCoarseS7_hz86 hx hc) (lowCoarseS7_hz90 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS7_hz92 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B (75966820291952741 / 500000000000000000) (11645746278378559 / 62500000000000000) ((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) := badd (lowCoarseS7_hz85 hx hc) (lowCoarseS7_hz91 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS7_hz93 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B 0 (2875000000001 / 1000000000000000000) ((ne0 x)^2) := bsq (lowCoarseS7_hz68 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS7_hz94 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B (75966820291952741 / 500000000000000000) (37266963090811389 / 200000000000000000) (((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) + ((ne0 x)^2)) := badd (lowCoarseS7_hz92 hx hc) (lowCoarseS7_hz93 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS7_hz95 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B (75966820291952741 / 500000000000000000) (191155572178743159 / 1000000000000000000) ((((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) + ((ne0 x)^2)) + (nrs x)) := badd (lowCoarseS7_hz94 hx hc) (lowCoarseS7_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS7_hz96 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B (75966820291952741 / 500000000000000000) (191155572178743159 / 1000000000000000000) (nu x c) := by
    convert (lowCoarseS7_hz95 hx hc) using 1 <;>
      norm_num [nu] <;> ring

theorem lowCoarseS7_hz97 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B (47686044520378319 / 1000000000000000000) (66082334146144281 / 1000000000000000000) ((npp c) - (nrpp x)) := bsub (lowCoarseS7_hz59 hx hc) (lowCoarseS7_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS7_hz98 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B 0 0 (min ((npp c) - (nrpp x)) (0 : ℝ)) := bweaken (bmin (lowCoarseS7_hz97 hx hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem lowCoarseS7_hz99 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B 0 0 ((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) := bmul (lowCoarseS7_hz50 hx hc) (lowCoarseS7_hz98 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS7_hz100 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B (-2875000000001 / 1000000000000000000) 0 (((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) - ((ne0 x)^2)) := bsub (lowCoarseS7_hz99 hx hc) (lowCoarseS7_hz93 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS7_hz101 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B (-964726344937243 / 200000000000000000) 0 ((((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) - ((ne0 x)^2)) - (nrs x)) := bsub (lowCoarseS7_hz100 hx hc) (lowCoarseS7_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS7_hz102 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B (-964726344937243 / 200000000000000000) 0 (nl x c) := by
    convert (lowCoarseS7_hz101 hx hc) using 1 <;>
      norm_num [nl] <;> ring

theorem lowCoarseS7_hz103 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B 0 (191155572178743159 / 1000000000000000000) |(nu x c)| := bweaken (babs (lowCoarseS7_hz96 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS7_hz104 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B 0 (964726344937243 / 200000000000000000) |(nl x c)| := bweaken (babs (lowCoarseS7_hz102 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS7_hz105 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B 0 (191155572178743159 / 1000000000000000000) (max |(nu x c)| |(nl x c)|) := bweaken (bmax (lowCoarseS7_hz103 hx hc) (lowCoarseS7_hz104 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS7_hz106 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) : B 0 (191155572178743159 / 1000000000000000000) (ns x c) := by
    convert (lowCoarseS7_hz105 hx hc) using 1 <;>
      norm_num [ns] <;> ring

theorem lowCoarseS7 {x c : ℝ}
    (hx : B 0 (1/8000) x) (hc : B (37 / 100) (19 / 50) c) :
    0 < nam x ∧ 0 ≤ ndm x c ∧ ndm x c ^ 2 ≤ 2 * nap x ^ 2 ∧ nc1 x c < 1 ∧
    0 ≤ npa c - nr1 x ∧ ne0 x ≤ (npa c - nr1 x) / nap x ∧ ns x c ≤ (9 / 25) := by
  refine ⟨lt_of_lt_of_le (by norm_num) (lowCoarseS7_hz12 hx hc).1,
    le_trans (by norm_num) (lowCoarseS7_hz38 hx hc).1, ?_,
    lt_of_le_of_lt (lowCoarseS7_hz46 hx hc).2 (by norm_num), ?_, ?_, (lowCoarseS7_hz106 hx hc).2.trans (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (lowCoarseS7_hz38 hx hc).1) (lowCoarseS7_hz38 hx hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) (lowCoarseS7_hz6 hx hc).1 2
    nlinarith only [h1,h2]
  · linarith only [(lowCoarseS7_hz55 hx hc).1,(lowCoarseS7_hz64 hx hc).2]
  · have hap : 0 < nap x := lt_of_lt_of_le (by norm_num) (lowCoarseS7_hz6 hx hc).1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul (lowCoarseS7_hz68 hx hc).2 (lowCoarseS7_hz6 hx hc).2 (le_trans (by norm_num) (lowCoarseS7_hz6 hx hc).1) (by norm_num)
    linarith only [h,(lowCoarseS7_hz55 hx hc).1,(lowCoarseS7_hz64 hx hc).2]

end BstLean.BlueprintLow
