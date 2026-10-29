import BstLean.Part264bNormalize
namespace BstLean.BlueprintLow
open Real BstLean.Part130 BstLean.Part182 BstLean.Part197 BstLean.Part246 BstLean.Part255
open BstLean.Part264b
theorem lowCoarseS40_hz0 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B 0 (1 / 8000) x := hx

theorem lowCoarseS40_hz1 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B (7 / 10) (71 / 100) c := hc

theorem lowCoarseS40_hz2 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B (6782329983125268139 / 500000000000000000) (13564659966250536279 / 1000000000000000000) (√(184 : ℝ)) := bsqrt (bpoint (184 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS40_hz3 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS40_hz4 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B 0 (847791247890659 / 500000000000000000) ((√(184 : ℝ)) * x) := bmul (lowCoarseS40_hz2 hx hc) (lowCoarseS40_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS40_hz5 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B 1 (500847791247890659 / 500000000000000000) ((1 : ℝ) + ((√(184 : ℝ)) * x)) := badd (bpoint (1 : ℝ)) (lowCoarseS40_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS40_hz6 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B 1 (500847791247890659 / 500000000000000000) (nap x) := by
    convert (lowCoarseS40_hz5 hx hc) using 1 <;>
      norm_num [nap] <;> ring

theorem lowCoarseS40_hz7 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B 0 (1 / 64000000) (x^2) := bsq (lowCoarseS40_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS40_hz8 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B 0 (1 / 32000000) ((2 : ℝ) * (x^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS40_hz7 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS40_hz9 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B (31999999 / 32000000) 1 ((1 : ℝ) - ((2 : ℝ) * (x^2))) := bsub (bpoint (1 : ℝ)) (lowCoarseS40_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS40_hz10 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B (999999984374999877 / 1000000000000000000) 1 (√((1 : ℝ) - ((2 : ℝ) * (x^2)))) := bsqrt (lowCoarseS40_hz9 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS40_hz11 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B (998304401879218559 / 1000000000000000000) 1 ((√((1 : ℝ) - ((2 : ℝ) * (x^2)))) - ((√(184 : ℝ)) * x)) := bsub (lowCoarseS40_hz10 hx hc) (lowCoarseS40_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS40_hz12 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B (998304401879218559 / 1000000000000000000) 1 (nam x) := by
    convert (lowCoarseS40_hz11 hx hc) using 1 <;>
      norm_num [nam] <;> ring

theorem lowCoarseS40_hz13 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B (746816688893365019 / 1000000000000000000) (373408344446682511 / 500000000000000000) (kdot ((7 / 10))) := by
    constructor
    · apply bkdot_lower (q := (210042012604201471 / 500000000000000000)) (a := (397699415092071779 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (420084025208402941 / 1000000000000000000)) (a := (397699415092071777 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS40_hz14 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B (49 / 100) (49 / 100) (((7 / 10) : ℝ)^2) := bsq (bpoint ((7 / 10) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS40_hz15 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B (51 / 100) (51 / 100) ((1 : ℝ) - (((7 / 10) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS40_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS40_hz16 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B (714142842854284999 / 1000000000000000000) (142828568570857 / 200000000000000) (√((1 : ℝ) - (((7 / 10) : ℝ)^2))) := bsqrt (lowCoarseS40_hz15 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS40_hz17 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B (45463745405583233 / 200000000000000000) (113659363513958083 / 500000000000000000) ((√((1 : ℝ) - (((7 / 10) : ℝ)^2))) / Real.pi) := bdiv (lowCoarseS40_hz16 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS40_hz18 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B (522771682225355513 / 1000000000000000000) (130692920556338879 / 250000000000000000) (((7 / 10) : ℝ) * (kdot ((7 / 10)))) := bmul (bpoint ((7 / 10) : ℝ)) (lowCoarseS40_hz13 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS40_hz19 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B (375045204626635839 / 500000000000000000) (375045204626635841 / 500000000000000000) (((√((1 : ℝ) - (((7 / 10) : ℝ)^2))) / Real.pi) + (((7 / 10) : ℝ) * (kdot ((7 / 10))))) := badd (lowCoarseS40_hz17 hx hc) (lowCoarseS40_hz18 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS40_hz20 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B (375045204626635839 / 500000000000000000) (375045204626635841 / 500000000000000000) (kappa ((7 / 10))) := by rw [kappa_eq]; exact (lowCoarseS40_hz19 hx hc)

theorem lowCoarseS40_hz21 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B (37565254257964327 / 50000000000000000) (375652542579643271 / 500000000000000000) (kdot ((71 / 100))) := by
    constructor
    · apply bkdot_lower (q := (411813845414228153 / 1000000000000000000)) (a := (97662264681090581 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (51476730676778519 / 125000000000000000)) (a := (390649058724362323 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS40_hz22 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B (5041 / 10000) (5041 / 10000) (((71 / 100) : ℝ)^2) := bsq (bpoint ((71 / 100) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS40_hz23 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B (4959 / 10000) (4959 / 10000) ((1 : ℝ) - (((71 / 100) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS40_hz22 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS40_hz24 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B (704201675658330139 / 1000000000000000000) (35210083782916507 / 50000000000000000) (√((1 : ℝ) - (((71 / 100) : ℝ)^2))) := bsqrt (lowCoarseS40_hz23 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS40_hz25 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B (11207717761461887 / 50000000000000000) (224154355229237741 / 1000000000000000000) ((√((1 : ℝ) - (((71 / 100) : ℝ)^2))) / Real.pi) := bdiv (lowCoarseS40_hz24 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS40_hz26 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B (533426610463093443 / 1000000000000000000) (106685322092618689 / 200000000000000000) (((71 / 100) : ℝ) * (kdot ((71 / 100)))) := bmul (bpoint ((71 / 100) : ℝ)) (lowCoarseS40_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS40_hz27 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B (757580965692331183 / 1000000000000000000) (378790482846165593 / 500000000000000000) (((√((1 : ℝ) - (((71 / 100) : ℝ)^2))) / Real.pi) + (((71 / 100) : ℝ) * (kdot ((71 / 100))))) := badd (lowCoarseS40_hz25 hx hc) (lowCoarseS40_hz26 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS40_hz28 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B (757580965692331183 / 1000000000000000000) (378790482846165593 / 500000000000000000) (kappa ((71 / 100))) := by rw [kappa_eq]; exact (lowCoarseS40_hz27 hx hc)

theorem lowCoarseS40_hz29 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B (375045204626635839 / 500000000000000000) (378790482846165593 / 500000000000000000) (kappa c) := bkappa (lowCoarseS40_hz1 hx hc) (by norm_num) (by norm_num) (lowCoarseS40_hz20 hx hc).1 (lowCoarseS40_hz28 hx hc).2

theorem lowCoarseS40_hz30 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B (121209517153834407 / 500000000000000000) (124954795373364161 / 500000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (lowCoarseS40_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS40_hz31 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B (121209517153834407 / 250000000000000000) (124954795373364161 / 250000000000000000) ((2 : ℝ) * ((1 : ℝ) - (kappa c))) := bmul (bpoint (2 : ℝ)) (lowCoarseS40_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS40_hz32 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B 0 (1 / 8000000) ((8 : ℝ) * (x^2)) := bmul (bpoint (8 : ℝ)) (lowCoarseS40_hz7 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS40_hz33 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B (121209485903834407 / 250000000000000000) (124954795373364161 / 250000000000000000) (((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2))) := bsub (lowCoarseS40_hz31 hx hc) (lowCoarseS40_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS40_hz34 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B (696303054434875811 / 1000000000000000000) (706978911632770447 / 1000000000000000000) (√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) := bsqrt (lowCoarseS40_hz33 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS40_hz35 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B (6782329983125268139 / 250000000000000000) (13564659966250536279 / 500000000000000000) ((2 : ℝ) * (√(184 : ℝ))) := bmul (bpoint (2 : ℝ)) (lowCoarseS40_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS40_hz36 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B 0 (678232998312527 / 200000000000000000) (((2 : ℝ) * (√(184 : ℝ))) * x) := bmul (lowCoarseS40_hz35 hx hc) (lowCoarseS40_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS40_hz37 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B (86613986180414147 / 125000000000000000) (706978911632770447 / 1000000000000000000) ((√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) - (((2 : ℝ) * (√(184 : ℝ))) * x)) := bsub (lowCoarseS40_hz34 hx hc) (lowCoarseS40_hz36 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS40_hz38 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B (86613986180414147 / 125000000000000000) (706978911632770447 / 1000000000000000000) (ndm x c) := by
    convert (lowCoarseS40_hz37 hx hc) using 1 <;>
      norm_num [ndm] <;> ring

theorem lowCoarseS40_hz39 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B 1 (1003394039991562637 / 1000000000000000000) ((nap x)^2) := bsq (lowCoarseS40_hz6 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS40_hz40 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B 2 (1003394039991562637 / 500000000000000000) ((2 : ℝ) * ((nap x)^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS40_hz39 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS40_hz41 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B (480126886531902261 / 1000000000000000000) (99963836298691329 / 200000000000000000) ((ndm x c)^2) := bsq (lowCoarseS40_hz38 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS40_hz42 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B (300036163701308671 / 200000000000000000) (1526661193451223013 / 1000000000000000000) (((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) := bsub (lowCoarseS40_hz40 hx hc) (lowCoarseS40_hz41 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS40_hz43 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B (199322335762284863 / 200000000000000000) 1 ((nam x)^2) := bsq (lowCoarseS40_hz12 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS40_hz44 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B (199322335762284863 / 100000000000000000) 2 ((2 : ℝ) * ((nam x)^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS40_hz43 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS40_hz45 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B (750090409253271677 / 1000000000000000000) (76592579934039333 / 100000000000000000) ((((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) / ((2 : ℝ) * ((nam x)^2))) := bdiv (lowCoarseS40_hz42 hx hc) (lowCoarseS40_hz44 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS40_hz46 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B (750090409253271677 / 1000000000000000000) (76592579934039333 / 100000000000000000) (nc1 x c) := by
    convert (lowCoarseS40_hz45 hx hc) using 1 <;>
      norm_num [nc1] <;> ring

theorem lowCoarseS40_hz47 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B (746816688893365019 / 1000000000000000000) (375652542579643271 / 500000000000000000) (kdot c) := bkdot (lowCoarseS40_hz1 hx hc) (lowCoarseS40_hz13 hx hc).1 (lowCoarseS40_hz21 hx hc).2

theorem lowCoarseS40_hz48 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B (76999005569665573 / 100000000000000000) (192497513924163933 / 250000000000000000) (kdot ((750090409253271677 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (94471590679960457 / 250000000000000000)) (a := (72259755127598387 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (377886362719841827 / 1000000000000000000)) (a := (361298775637991933 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS40_hz49 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B (777719031568960751 / 1000000000000000000) (777719031568960753 / 1000000000000000000) (kdot ((76592579934039333 / 100000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (72814948123094831 / 200000000000000000)) (a := (174579064363944413 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (182037370307737077 / 500000000000000000)) (a := (43644766090986103 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS40_hz50 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B (76999005569665573 / 100000000000000000) (777719031568960753 / 1000000000000000000) (kdot (nc1 x c)) := bkdot (lowCoarseS40_hz46 hx hc) (lowCoarseS40_hz48 hx hc).1 (lowCoarseS40_hz49 hx hc).2

theorem lowCoarseS40_hz51 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B (49 / 100) (5041 / 10000) (c^2) := bsq (lowCoarseS40_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS40_hz52 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B (4959 / 10000) (51 / 100) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS40_hz51 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS40_hz53 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B (704201675658330139 / 1000000000000000000) (142828568570857 / 200000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (lowCoarseS40_hz52 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS40_hz54 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B (525909563728313477 / 1000000000000000000) (536539149366533579 / 1000000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (lowCoarseS40_hz53 hx hc) (lowCoarseS40_hz47 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS40_hz55 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B (525909563728313477 / 1000000000000000000) (536539149366533579 / 1000000000000000000) (npa c) := by
    convert (lowCoarseS40_hz54 hx hc) using 1 <;>
      norm_num [npa] <;> ring

theorem lowCoarseS40_hz56 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B (11207717761461887 / 50000000000000000) (113659363513958083 / 500000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (lowCoarseS40_hz53 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS40_hz57 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B (522771682225355513 / 1000000000000000000) (106685322092618689 / 200000000000000000) (c * (kdot c)) := bmul (lowCoarseS40_hz1 hx hc) (lowCoarseS40_hz47 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS40_hz58 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B (-61854451046771141 / 200000000000000000) (-295452955197439347 / 1000000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (lowCoarseS40_hz56 hx hc) (lowCoarseS40_hz57 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS40_hz59 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B (-61854451046771141 / 200000000000000000) (-295452955197439347 / 1000000000000000000) (npp c) := by
    convert (lowCoarseS40_hz58 hx hc) using 1 <;>
      norm_num [npp] <;> ring

theorem lowCoarseS40_hz60 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B 0 (23 / 4000) ((46 : ℝ) * x) := bmul (bpoint (46 : ℝ)) (lowCoarseS40_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS40_hz61 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B (9591663046625439083 / 1000000000000000000) (2399353261656359771 / 250000000000000000) ((√(92 : ℝ)) + ((46 : ℝ) * x)) := badd (lowCoarseS40_hz3 hx hc) (lowCoarseS40_hz60 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS40_hz62 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B (28774989139876317249 / 250000000000000000) (7198059784969079313 / 62500000000000000) ((12 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (bpoint (12 : ℝ)) (lowCoarseS40_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS40_hz63 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B 0 (14396119569938159 / 1000000000000000000) (((12 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS40_hz62 hx hc) (lowCoarseS40_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS40_hz64 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B 0 (14396119569938159 / 1000000000000000000) (nr1 x) := by
    convert (lowCoarseS40_hz63 hx hc) using 1 <;>
      norm_num [nr1] <;> ring

theorem lowCoarseS40_hz65 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B (9591663046625439083 / 125000000000000000) (2399353261656359771 / 31250000000000000) ((8 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (bpoint (8 : ℝ)) (lowCoarseS40_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS40_hz66 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B 0 (59983831541409 / 6250000000000000) (((8 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS40_hz65 hx hc) (lowCoarseS40_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS40_hz67 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B 0 (59983831541409 / 6250000000000000) (nrpp x) := by
    convert (lowCoarseS40_hz66 hx hc) using 1 <;>
      norm_num [nrpp] <;> ring

theorem lowCoarseS40_hz68 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B 0 (847791247890659 / 500000000000000000) (ne0 x) := by
    convert (lowCoarseS40_hz4 hx hc) using 1 <;>
      norm_num [ne0] <;> ring

theorem lowCoarseS40_hz69 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B (525909563728313477 / 1000000000000000000) (275467634468235869 / 500000000000000000) ((npa c) + (nr1 x)) := badd (lowCoarseS40_hz55 hx hc) (lowCoarseS40_hz64 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS40_hz70 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B (525909563728313477 / 1000000000000000000) (551871020401578391 / 1000000000000000000) (((npa c) + (nr1 x)) / (nam x)) := bdiv (lowCoarseS40_hz69 hx hc) (lowCoarseS40_hz12 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS40_hz71 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B (525909563728313477 / 1000000000000000000) (553566602897359709 / 1000000000000000000) ((((npa c) + (nr1 x)) / (nam x)) + (ne0 x)) := badd (lowCoarseS40_hz70 hx hc) (lowCoarseS40_hz68 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS40_hz72 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B (525909563728313477 / 1000000000000000000) (553566602897359709 / 1000000000000000000) (nlam x c) := by
    convert (lowCoarseS40_hz71 hx hc) using 1 <;>
      norm_num [nlam] <;> ring

theorem lowCoarseS40_hz73 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS40_hz74 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B 0 (59947894041409 / 100000000000000000) ((√(23 : ℝ)) * x) := bmul (lowCoarseS40_hz73 hx hc) (lowCoarseS40_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS40_hz75 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B (1 / 2) (50059947894041409 / 100000000000000000) (((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)) := badd (bpoint ((1 / 2) : ℝ)) (lowCoarseS40_hz74 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS40_hz76 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B (176776695296636881 / 250000000000000000) (353765274914177413 / 500000000000000000) (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) := bsqrt (lowCoarseS40_hz75 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS40_hz77 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B 0 (59947894041409 / 50000000000000000) ((√(92 : ℝ)) * x) := bmul (lowCoarseS40_hz3 hx hc) (lowCoarseS40_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS40_hz78 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B (176776695296636881 / 250000000000000000) (354364753854591503 / 500000000000000000) ((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x)) := badd (lowCoarseS40_hz76 hx hc) (lowCoarseS40_hz77 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS40_hz79 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B (499999999999999999 / 1000000000000000000) (251148757548850447 / 500000000000000000) (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2) := bsq (lowCoarseS40_hz78 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS40_hz80 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B (499999999999999999 / 125000000000000000) (251148757548850447 / 62500000000000000) ((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) := bmul (bpoint (8 : ℝ)) (lowCoarseS40_hz79 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS40_hz81 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B (7673330437300351251 / 200000000000000000) (1928302689874485209 / 50000000000000000) (((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (lowCoarseS40_hz80 hx hc) (lowCoarseS40_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS40_hz82 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B 0 (2410378362343107 / 500000000000000000) ((((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS40_hz81 hx hc) (lowCoarseS40_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS40_hz83 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B 0 (2410378362343107 / 500000000000000000) (nrs x) := by
    convert (lowCoarseS40_hz82 hx hc) using 1 <;>
      norm_num [nrs] <;> ring

theorem lowCoarseS40_hz84 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B (-61854451046771141 / 200000000000000000) (-285855542150813907 / 1000000000000000000) ((npp c) + (nrpp x)) := badd (lowCoarseS40_hz59 hx hc) (lowCoarseS40_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS40_hz85 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B (-240526918831622713 / 1000000000000000000) (-142927771075406953 / 1000000000000000000) (if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) := bweaken (bfirst (lowCoarseS40_hz84 hx hc) (lowCoarseS40_hz50 hx hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem lowCoarseS40_hz86 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B (138290434610452507 / 500000000000000000) (61287196768664627 / 200000000000000000) ((nlam x c)^2) := bsq (lowCoarseS40_hz72 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS40_hz87 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B (35164726378358787 / 62500000000000000) (146660582523805117 / 250000000000000000) ((nc1 x c)^2) := bsq (lowCoarseS40_hz46 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS40_hz88 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B (103339417476194883 / 250000000000000000) (27335273621641213 / 62500000000000000) ((1 : ℝ) - ((nc1 x c)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS40_hz87 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS40_hz89 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B (642928977341027561 / 1000000000000000000) (2645341196734393 / 4000000000000000) (√((1 : ℝ) - ((nc1 x c)^2))) := bsqrt (lowCoarseS40_hz88 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS40_hz90 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B (252477618999321353 / 125000000000000000) (2077646117474800249 / 1000000000000000000) (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))) := bmul pi_mem (lowCoarseS40_hz89 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS40_hz91 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B (6656111136892389 / 50000000000000000) (4741075928362579 / 31250000000000000) (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2))))) := bdiv (lowCoarseS40_hz86 hx hc) (lowCoarseS40_hz90 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS40_hz92 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B (-107404696093774933 / 1000000000000000000) (351466345287823 / 40000000000000000) ((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) := badd (lowCoarseS40_hz85 hx hc) (lowCoarseS40_hz91 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS40_hz93 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B 0 (2875000000001 / 1000000000000000000) ((ne0 x)^2) := bsq (lowCoarseS40_hz68 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS40_hz94 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B (-107404696093774933 / 1000000000000000000) (1098691704024447 / 125000000000000000) (((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) + ((ne0 x)^2)) := badd (lowCoarseS40_hz92 hx hc) (lowCoarseS40_hz93 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS40_hz95 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B (-107404696093774933 / 1000000000000000000) (1361029035688179 / 100000000000000000) ((((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) + ((ne0 x)^2)) + (nrs x)) := badd (lowCoarseS40_hz94 hx hc) (lowCoarseS40_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS40_hz96 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B (-107404696093774933 / 1000000000000000000) (1361029035688179 / 100000000000000000) (nu x c) := by
    convert (lowCoarseS40_hz95 hx hc) using 1 <;>
      norm_num [nu] <;> ring

theorem lowCoarseS40_hz97 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B (-63773933656096229 / 200000000000000000) (-295452955197439347 / 1000000000000000000) ((npp c) - (nrpp x)) := bsub (lowCoarseS40_hz59 hx hc) (lowCoarseS40_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS40_hz98 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B (-63773933656096229 / 200000000000000000) (-295452955197439347 / 1000000000000000000) (min ((npp c) - (nrpp x)) (0 : ℝ)) := bweaken (bmin (lowCoarseS40_hz97 hx hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem lowCoarseS40_hz99 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B (-247991009611811559 / 1000000000000000000) (-56873959357054463 / 250000000000000000) ((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) := bmul (lowCoarseS40_hz50 hx hc) (lowCoarseS40_hz98 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS40_hz100 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B (-6199847115295289 / 25000000000000000) (-56873959357054463 / 250000000000000000) (((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) - ((ne0 x)^2)) := bsub (lowCoarseS40_hz99 hx hc) (lowCoarseS40_hz93 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS40_hz101 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B (-126407320668248887 / 500000000000000000) (-56873959357054463 / 250000000000000000) ((((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) - ((ne0 x)^2)) - (nrs x)) := bsub (lowCoarseS40_hz100 hx hc) (lowCoarseS40_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS40_hz102 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B (-126407320668248887 / 500000000000000000) (-56873959357054463 / 250000000000000000) (nl x c) := by
    convert (lowCoarseS40_hz101 hx hc) using 1 <;>
      norm_num [nl] <;> ring

theorem lowCoarseS40_hz103 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B 0 (107404696093774933 / 1000000000000000000) |(nu x c)| := bweaken (babs (lowCoarseS40_hz96 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS40_hz104 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B 0 (126407320668248887 / 500000000000000000) |(nl x c)| := bweaken (babs (lowCoarseS40_hz102 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS40_hz105 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B 0 (126407320668248887 / 500000000000000000) (max |(nu x c)| |(nl x c)|) := bweaken (bmax (lowCoarseS40_hz103 hx hc) (lowCoarseS40_hz104 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS40_hz106 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) : B 0 (126407320668248887 / 500000000000000000) (ns x c) := by
    convert (lowCoarseS40_hz105 hx hc) using 1 <;>
      norm_num [ns] <;> ring

theorem lowCoarseS40 {x c : ℝ}
    (hx : B 0 (1/8000) x) (hc : B (7 / 10) (71 / 100) c) :
    0 < nam x ∧ 0 ≤ ndm x c ∧ ndm x c ^ 2 ≤ 2 * nap x ^ 2 ∧ nc1 x c < 1 ∧
    0 ≤ npa c - nr1 x ∧ ne0 x ≤ (npa c - nr1 x) / nap x ∧ ns x c ≤ (9 / 25) := by
  refine ⟨lt_of_lt_of_le (by norm_num) (lowCoarseS40_hz12 hx hc).1,
    le_trans (by norm_num) (lowCoarseS40_hz38 hx hc).1, ?_,
    lt_of_le_of_lt (lowCoarseS40_hz46 hx hc).2 (by norm_num), ?_, ?_, (lowCoarseS40_hz106 hx hc).2.trans (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (lowCoarseS40_hz38 hx hc).1) (lowCoarseS40_hz38 hx hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) (lowCoarseS40_hz6 hx hc).1 2
    nlinarith only [h1,h2]
  · linarith only [(lowCoarseS40_hz55 hx hc).1,(lowCoarseS40_hz64 hx hc).2]
  · have hap : 0 < nap x := lt_of_lt_of_le (by norm_num) (lowCoarseS40_hz6 hx hc).1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul (lowCoarseS40_hz68 hx hc).2 (lowCoarseS40_hz6 hx hc).2 (le_trans (by norm_num) (lowCoarseS40_hz6 hx hc).1) (by norm_num)
    linarith only [h,(lowCoarseS40_hz55 hx hc).1,(lowCoarseS40_hz64 hx hc).2]

theorem lowCoarseS41_hz0 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B 0 (1 / 8000) x := hx

theorem lowCoarseS41_hz1 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B (71 / 100) (18 / 25) c := hc

theorem lowCoarseS41_hz2 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B (6782329983125268139 / 500000000000000000) (13564659966250536279 / 1000000000000000000) (√(184 : ℝ)) := bsqrt (bpoint (184 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS41_hz3 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS41_hz4 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B 0 (847791247890659 / 500000000000000000) ((√(184 : ℝ)) * x) := bmul (lowCoarseS41_hz2 hx hc) (lowCoarseS41_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS41_hz5 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B 1 (500847791247890659 / 500000000000000000) ((1 : ℝ) + ((√(184 : ℝ)) * x)) := badd (bpoint (1 : ℝ)) (lowCoarseS41_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS41_hz6 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B 1 (500847791247890659 / 500000000000000000) (nap x) := by
    convert (lowCoarseS41_hz5 hx hc) using 1 <;>
      norm_num [nap] <;> ring

theorem lowCoarseS41_hz7 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B 0 (1 / 64000000) (x^2) := bsq (lowCoarseS41_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS41_hz8 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B 0 (1 / 32000000) ((2 : ℝ) * (x^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS41_hz7 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS41_hz9 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B (31999999 / 32000000) 1 ((1 : ℝ) - ((2 : ℝ) * (x^2))) := bsub (bpoint (1 : ℝ)) (lowCoarseS41_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS41_hz10 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B (999999984374999877 / 1000000000000000000) 1 (√((1 : ℝ) - ((2 : ℝ) * (x^2)))) := bsqrt (lowCoarseS41_hz9 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS41_hz11 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B (998304401879218559 / 1000000000000000000) 1 ((√((1 : ℝ) - ((2 : ℝ) * (x^2)))) - ((√(184 : ℝ)) * x)) := bsub (lowCoarseS41_hz10 hx hc) (lowCoarseS41_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS41_hz12 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B (998304401879218559 / 1000000000000000000) 1 (nam x) := by
    convert (lowCoarseS41_hz11 hx hc) using 1 <;>
      norm_num [nam] <;> ring

theorem lowCoarseS41_hz13 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B (37565254257964327 / 50000000000000000) (375652542579643271 / 500000000000000000) (kdot ((71 / 100))) := by
    constructor
    · apply bkdot_lower (q := (411813845414228153 / 1000000000000000000)) (a := (97662264681090581 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (51476730676778519 / 125000000000000000)) (a := (390649058724362323 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS41_hz14 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B (5041 / 10000) (5041 / 10000) (((71 / 100) : ℝ)^2) := bsq (bpoint ((71 / 100) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS41_hz15 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B (4959 / 10000) (4959 / 10000) ((1 : ℝ) - (((71 / 100) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS41_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS41_hz16 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B (704201675658330139 / 1000000000000000000) (35210083782916507 / 50000000000000000) (√((1 : ℝ) - (((71 / 100) : ℝ)^2))) := bsqrt (lowCoarseS41_hz15 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS41_hz17 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B (11207717761461887 / 50000000000000000) (224154355229237741 / 1000000000000000000) ((√((1 : ℝ) - (((71 / 100) : ℝ)^2))) / Real.pi) := bdiv (lowCoarseS41_hz16 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS41_hz18 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B (533426610463093443 / 1000000000000000000) (106685322092618689 / 200000000000000000) (((71 / 100) : ℝ) * (kdot ((71 / 100)))) := bmul (bpoint ((71 / 100) : ℝ)) (lowCoarseS41_hz13 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS41_hz19 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B (757580965692331183 / 1000000000000000000) (378790482846165593 / 500000000000000000) (((√((1 : ℝ) - (((71 / 100) : ℝ)^2))) / Real.pi) + (((71 / 100) : ℝ) * (kdot ((71 / 100))))) := badd (lowCoarseS41_hz17 hx hc) (lowCoarseS41_hz18 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS41_hz20 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B (757580965692331183 / 1000000000000000000) (378790482846165593 / 500000000000000000) (kappa ((71 / 100))) := by rw [kappa_eq]; exact (lowCoarseS41_hz19 hx hc)

theorem lowCoarseS41_hz21 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B (377929112326919899 / 500000000000000000) (755858224653839801 / 1000000000000000000) (kdot ((18 / 25))) := by
    constructor
    · apply bkdot_lower (q := (16138931695718579 / 40000000000000000)) (a := (191748501965466647 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (201736646196482237 / 500000000000000000)) (a := (95874250982733323 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS41_hz22 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B (324 / 625) (324 / 625) (((18 / 25) : ℝ)^2) := bsq (bpoint ((18 / 25) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS41_hz23 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B (301 / 625) (301 / 625) ((1 : ℝ) - (((18 / 25) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS41_hz22 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS41_hz24 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B (43373378932243681 / 62500000000000000) (693974062915898897 / 1000000000000000000) (√((1 : ℝ) - (((18 / 25) : ℝ)^2))) := bsqrt (lowCoarseS41_hz23 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS41_hz25 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B (55224701245315641 / 250000000000000000) (44179760996252513 / 200000000000000000) ((√((1 : ℝ) - (((18 / 25) : ℝ)^2))) / Real.pi) := bdiv (lowCoarseS41_hz24 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS41_hz26 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B (272108960875382327 / 500000000000000000) (544217921750764657 / 1000000000000000000) (((18 / 25) : ℝ) * (kdot ((18 / 25)))) := bmul (bpoint ((18 / 25) : ℝ)) (lowCoarseS41_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS41_hz27 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B (382558363366013609 / 500000000000000000) (382558363366013611 / 500000000000000000) (((√((1 : ℝ) - (((18 / 25) : ℝ)^2))) / Real.pi) + (((18 / 25) : ℝ) * (kdot ((18 / 25))))) := badd (lowCoarseS41_hz25 hx hc) (lowCoarseS41_hz26 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS41_hz28 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B (382558363366013609 / 500000000000000000) (382558363366013611 / 500000000000000000) (kappa ((18 / 25))) := by rw [kappa_eq]; exact (lowCoarseS41_hz27 hx hc)

theorem lowCoarseS41_hz29 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B (757580965692331183 / 1000000000000000000) (382558363366013611 / 500000000000000000) (kappa c) := bkappa (lowCoarseS41_hz1 hx hc) (by norm_num) (by norm_num) (lowCoarseS41_hz20 hx hc).1 (lowCoarseS41_hz28 hx hc).2

theorem lowCoarseS41_hz30 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B (117441636633986389 / 500000000000000000) (242419034307668817 / 1000000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (lowCoarseS41_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS41_hz31 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B (117441636633986389 / 250000000000000000) (242419034307668817 / 500000000000000000) ((2 : ℝ) * ((1 : ℝ) - (kappa c))) := bmul (bpoint (2 : ℝ)) (lowCoarseS41_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS41_hz32 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B 0 (1 / 8000000) ((8 : ℝ) * (x^2)) := bmul (bpoint (8 : ℝ)) (lowCoarseS41_hz7 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS41_hz33 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B (117441605383986389 / 250000000000000000) (242419034307668817 / 500000000000000000) (((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2))) := bsub (lowCoarseS41_hz31 hx hc) (lowCoarseS41_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS41_hz34 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B (137079016853192459 / 200000000000000000) (139260628838927427 / 200000000000000000) (√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) := bsqrt (lowCoarseS41_hz33 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS41_hz35 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B (6782329983125268139 / 250000000000000000) (13564659966250536279 / 500000000000000000) ((2 : ℝ) * (√(184 : ℝ))) := bmul (bpoint (2 : ℝ)) (lowCoarseS41_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS41_hz36 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B 0 (678232998312527 / 200000000000000000) (((2 : ℝ) * (√(184 : ℝ))) * x) := bmul (lowCoarseS41_hz35 hx hc) (lowCoarseS41_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS41_hz37 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B (34100195963719983 / 50000000000000000) (139260628838927427 / 200000000000000000) ((√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) - (((2 : ℝ) * (√(184 : ℝ))) * x)) := bsub (lowCoarseS41_hz34 hx hc) (lowCoarseS41_hz36 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS41_hz38 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B (34100195963719983 / 50000000000000000) (139260628838927427 / 200000000000000000) (ndm x c) := by
    convert (lowCoarseS41_hz37 hx hc) using 1 <;>
      norm_num [ndm] <;> ring

theorem lowCoarseS41_hz39 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B 1 (1003394039991562637 / 1000000000000000000) ((nap x)^2) := bsq (lowCoarseS41_hz6 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS41_hz40 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B 2 (1003394039991562637 / 500000000000000000) ((2 : ℝ) * ((nap x)^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS41_hz39 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS41_hz41 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B (58141168238205231 / 125000000000000000) (96967613723067527 / 200000000000000000) ((ndm x c)^2) := bsq (lowCoarseS41_hz38 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS41_hz42 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B (303032386276932473 / 200000000000000000) (770829367038741713 / 500000000000000000) (((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) := bsub (lowCoarseS41_hz40 hx hc) (lowCoarseS41_hz41 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS41_hz43 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B (199322335762284863 / 200000000000000000) 1 ((nam x)^2) := bsq (lowCoarseS41_hz12 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS41_hz44 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B (199322335762284863 / 100000000000000000) 2 ((2 : ℝ) * ((nam x)^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS41_hz43 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS41_hz45 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B (378790482846165591 / 500000000000000000) (386725032139923171 / 500000000000000000) ((((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) / ((2 : ℝ) * ((nam x)^2))) := bdiv (lowCoarseS41_hz42 hx hc) (lowCoarseS41_hz44 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS41_hz46 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B (378790482846165591 / 500000000000000000) (386725032139923171 / 500000000000000000) (nc1 x c) := by
    convert (lowCoarseS41_hz45 hx hc) using 1 <;>
      norm_num [nc1] <;> ring

theorem lowCoarseS41_hz47 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B (37565254257964327 / 50000000000000000) (755858224653839801 / 1000000000000000000) (kdot c) := bkdot (lowCoarseS41_hz1 hx hc) (lowCoarseS41_hz13 hx hc).1 (lowCoarseS41_hz21 hx hc).2

theorem lowCoarseS41_hz48 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B (773618904300984613 / 1000000000000000000) (96702363037623077 / 125000000000000000) (kdot ((378790482846165591 / 500000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (371386136697946109 / 1000000000000000000)) (a := (177799296789908669 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (92846534174486527 / 250000000000000000)) (a := (44449824197477167 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS41_hz49 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B (195367667529186519 / 250000000000000000) (781470670116746077 / 1000000000000000000) (kdot ((386725032139923171 / 500000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (71482952995230349 / 200000000000000000)) (a := (171632534338782749 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (5584605702752371 / 15625000000000000)) (a := (343265068677565497 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS41_hz50 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B (773618904300984613 / 1000000000000000000) (781470670116746077 / 1000000000000000000) (kdot (nc1 x c)) := bkdot (lowCoarseS41_hz46 hx hc) (lowCoarseS41_hz48 hx hc).1 (lowCoarseS41_hz49 hx hc).2

theorem lowCoarseS41_hz51 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B (5041 / 10000) (324 / 625) (c^2) := bsq (lowCoarseS41_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS41_hz52 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B (301 / 625) (4959 / 10000) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS41_hz51 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS41_hz53 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B (43373378932243681 / 62500000000000000) (35210083782916507 / 50000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (lowCoarseS41_hz52 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS41_hz54 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B (104277248487473099 / 200000000000000000) (266138314180682267 / 500000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (lowCoarseS41_hz53 hx hc) (lowCoarseS41_hz47 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS41_hz55 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B (104277248487473099 / 200000000000000000) (266138314180682267 / 500000000000000000) (npa c) := by
    convert (lowCoarseS41_hz54 hx hc) using 1 <;>
      norm_num [npa] <;> ring

theorem lowCoarseS41_hz56 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B (55224701245315641 / 250000000000000000) (224154355229237741 / 1000000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (lowCoarseS41_hz53 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS41_hz57 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B (533426610463093443 / 1000000000000000000) (544217921750764657 / 1000000000000000000) (c * (kdot c)) := bmul (lowCoarseS41_hz1 hx hc) (lowCoarseS41_hz47 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS41_hz58 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B (-323319116769502093 / 1000000000000000000) (-154636127616927851 / 500000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (lowCoarseS41_hz56 hx hc) (lowCoarseS41_hz57 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS41_hz59 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B (-323319116769502093 / 1000000000000000000) (-154636127616927851 / 500000000000000000) (npp c) := by
    convert (lowCoarseS41_hz58 hx hc) using 1 <;>
      norm_num [npp] <;> ring

theorem lowCoarseS41_hz60 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B 0 (23 / 4000) ((46 : ℝ) * x) := bmul (bpoint (46 : ℝ)) (lowCoarseS41_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS41_hz61 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B (9591663046625439083 / 1000000000000000000) (2399353261656359771 / 250000000000000000) ((√(92 : ℝ)) + ((46 : ℝ) * x)) := badd (lowCoarseS41_hz3 hx hc) (lowCoarseS41_hz60 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS41_hz62 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B (28774989139876317249 / 250000000000000000) (7198059784969079313 / 62500000000000000) ((12 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (bpoint (12 : ℝ)) (lowCoarseS41_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS41_hz63 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B 0 (14396119569938159 / 1000000000000000000) (((12 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS41_hz62 hx hc) (lowCoarseS41_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS41_hz64 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B 0 (14396119569938159 / 1000000000000000000) (nr1 x) := by
    convert (lowCoarseS41_hz63 hx hc) using 1 <;>
      norm_num [nr1] <;> ring

theorem lowCoarseS41_hz65 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B (9591663046625439083 / 125000000000000000) (2399353261656359771 / 31250000000000000) ((8 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (bpoint (8 : ℝ)) (lowCoarseS41_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS41_hz66 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B 0 (59983831541409 / 6250000000000000) (((8 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS41_hz65 hx hc) (lowCoarseS41_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS41_hz67 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B 0 (59983831541409 / 6250000000000000) (nrpp x) := by
    convert (lowCoarseS41_hz66 hx hc) using 1 <;>
      norm_num [nrpp] <;> ring

theorem lowCoarseS41_hz68 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B 0 (847791247890659 / 500000000000000000) (ne0 x) := by
    convert (lowCoarseS41_hz4 hx hc) using 1 <;>
      norm_num [ne0] <;> ring

theorem lowCoarseS41_hz69 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B (104277248487473099 / 200000000000000000) (546672747931302693 / 1000000000000000000) ((npa c) + (nr1 x)) := badd (lowCoarseS41_hz55 hx hc) (lowCoarseS41_hz64 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS41_hz70 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B (104277248487473099 / 200000000000000000) (547601259598014637 / 1000000000000000000) (((npa c) + (nr1 x)) / (nam x)) := bdiv (lowCoarseS41_hz69 hx hc) (lowCoarseS41_hz12 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS41_hz71 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B (104277248487473099 / 200000000000000000) (109859368418759191 / 200000000000000000) ((((npa c) + (nr1 x)) / (nam x)) + (ne0 x)) := badd (lowCoarseS41_hz70 hx hc) (lowCoarseS41_hz68 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS41_hz72 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B (104277248487473099 / 200000000000000000) (109859368418759191 / 200000000000000000) (nlam x c) := by
    convert (lowCoarseS41_hz71 hx hc) using 1 <;>
      norm_num [nlam] <;> ring

theorem lowCoarseS41_hz73 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS41_hz74 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B 0 (59947894041409 / 100000000000000000) ((√(23 : ℝ)) * x) := bmul (lowCoarseS41_hz73 hx hc) (lowCoarseS41_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS41_hz75 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B (1 / 2) (50059947894041409 / 100000000000000000) (((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)) := badd (bpoint ((1 / 2) : ℝ)) (lowCoarseS41_hz74 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS41_hz76 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B (176776695296636881 / 250000000000000000) (353765274914177413 / 500000000000000000) (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) := bsqrt (lowCoarseS41_hz75 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS41_hz77 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B 0 (59947894041409 / 50000000000000000) ((√(92 : ℝ)) * x) := bmul (lowCoarseS41_hz3 hx hc) (lowCoarseS41_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS41_hz78 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B (176776695296636881 / 250000000000000000) (354364753854591503 / 500000000000000000) ((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x)) := badd (lowCoarseS41_hz76 hx hc) (lowCoarseS41_hz77 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS41_hz79 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B (499999999999999999 / 1000000000000000000) (251148757548850447 / 500000000000000000) (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2) := bsq (lowCoarseS41_hz78 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS41_hz80 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B (499999999999999999 / 125000000000000000) (251148757548850447 / 62500000000000000) ((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) := bmul (bpoint (8 : ℝ)) (lowCoarseS41_hz79 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS41_hz81 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B (7673330437300351251 / 200000000000000000) (1928302689874485209 / 50000000000000000) (((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (lowCoarseS41_hz80 hx hc) (lowCoarseS41_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS41_hz82 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B 0 (2410378362343107 / 500000000000000000) ((((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS41_hz81 hx hc) (lowCoarseS41_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS41_hz83 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B 0 (2410378362343107 / 500000000000000000) (nrs x) := by
    convert (lowCoarseS41_hz82 hx hc) using 1 <;>
      norm_num [nrs] <;> ring

theorem lowCoarseS41_hz84 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B (-323319116769502093 / 1000000000000000000) (-149837421093615131 / 500000000000000000) ((npp c) + (nrpp x)) := badd (lowCoarseS41_hz59 hx hc) (lowCoarseS41_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS41_hz85 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B (-10106576273736691 / 40000000000000000) (-149837421093615131 / 1000000000000000000) (if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) := bweaken (bfirst (lowCoarseS41_hz84 hx hc) (lowCoarseS41_hz50 hx hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem lowCoarseS41_hz86 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B (271843613802955267 / 1000000000000000000) (9428969397944269 / 31250000000000000) ((nlam x c)^2) := bsq (lowCoarseS41_hz72 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS41_hz87 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B (22957156783173003 / 40000000000000000) (598225001934498439 / 1000000000000000000) ((nc1 x c)^2) := bsq (lowCoarseS41_hz46 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS41_hz88 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B (401774998065501561 / 1000000000000000000) (17042843216826997 / 40000000000000000) ((1 : ℝ) - ((nc1 x c)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS41_hz87 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS41_hz89 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B (158464309480380621 / 250000000000000000) (652741204782320239 / 1000000000000000000) (√((1 : ℝ) - ((nc1 x c)^2))) := bsqrt (lowCoarseS41_hz88 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS41_hz90 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B (1991321242078972739 / 1000000000000000000) (2050646973639488077 / 1000000000000000000) (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))) := bmul pi_mem (lowCoarseS41_hz89 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS41_hz91 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B (132564803838706203 / 1000000000000000000) (75760508741223627 / 500000000000000000) (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2))))) := bdiv (lowCoarseS41_hz86 hx hc) (lowCoarseS41_hz90 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS41_hz92 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B (-3753112593897221 / 31250000000000000) (1683596388832123 / 1000000000000000000) ((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) := badd (lowCoarseS41_hz85 hx hc) (lowCoarseS41_hz91 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS41_hz93 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B 0 (2875000000001 / 1000000000000000000) ((ne0 x)^2) := bsq (lowCoarseS41_hz68 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS41_hz94 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B (-3753112593897221 / 31250000000000000) (421617847208031 / 250000000000000000) (((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) + ((ne0 x)^2)) := badd (lowCoarseS41_hz92 hx hc) (lowCoarseS41_hz93 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS41_hz95 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B (-3753112593897221 / 31250000000000000) (3253614056759169 / 500000000000000000) ((((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) + ((ne0 x)^2)) + (nrs x)) := badd (lowCoarseS41_hz94 hx hc) (lowCoarseS41_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS41_hz96 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B (-3753112593897221 / 31250000000000000) (3253614056759169 / 500000000000000000) (nu x c) := by
    convert (lowCoarseS41_hz95 hx hc) using 1 <;>
      norm_num [nu] <;> ring

theorem lowCoarseS41_hz97 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B (-332916529816127533 / 1000000000000000000) (-154636127616927851 / 500000000000000000) ((npp c) - (nrpp x)) := bsub (lowCoarseS41_hz59 hx hc) (lowCoarseS41_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS41_hz98 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B (-332916529816127533 / 1000000000000000000) (-154636127616927851 / 500000000000000000) (min ((npp c) - (nrpp x)) (0 : ℝ)) := bweaken (bmin (lowCoarseS41_hz97 hx hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem lowCoarseS41_hz99 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B (-260164503648350859 / 1000000000000000000) (-239258863224709901 / 1000000000000000000) ((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) := bmul (lowCoarseS41_hz50 hx hc) (lowCoarseS41_hz98 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS41_hz100 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B (-13008368932417543 / 50000000000000000) (-239258863224709901 / 1000000000000000000) (((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) - ((ne0 x)^2)) := bsub (lowCoarseS41_hz99 hx hc) (lowCoarseS41_hz93 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS41_hz101 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B (-132494067686518537 / 500000000000000000) (-239258863224709901 / 1000000000000000000) ((((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) - ((ne0 x)^2)) - (nrs x)) := bsub (lowCoarseS41_hz100 hx hc) (lowCoarseS41_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS41_hz102 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B (-132494067686518537 / 500000000000000000) (-239258863224709901 / 1000000000000000000) (nl x c) := by
    convert (lowCoarseS41_hz101 hx hc) using 1 <;>
      norm_num [nl] <;> ring

theorem lowCoarseS41_hz103 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B 0 (3753112593897221 / 31250000000000000) |(nu x c)| := bweaken (babs (lowCoarseS41_hz96 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS41_hz104 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B 0 (132494067686518537 / 500000000000000000) |(nl x c)| := bweaken (babs (lowCoarseS41_hz102 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS41_hz105 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B 0 (132494067686518537 / 500000000000000000) (max |(nu x c)| |(nl x c)|) := bweaken (bmax (lowCoarseS41_hz103 hx hc) (lowCoarseS41_hz104 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS41_hz106 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) : B 0 (132494067686518537 / 500000000000000000) (ns x c) := by
    convert (lowCoarseS41_hz105 hx hc) using 1 <;>
      norm_num [ns] <;> ring

theorem lowCoarseS41 {x c : ℝ}
    (hx : B 0 (1/8000) x) (hc : B (71 / 100) (18 / 25) c) :
    0 < nam x ∧ 0 ≤ ndm x c ∧ ndm x c ^ 2 ≤ 2 * nap x ^ 2 ∧ nc1 x c < 1 ∧
    0 ≤ npa c - nr1 x ∧ ne0 x ≤ (npa c - nr1 x) / nap x ∧ ns x c ≤ (9 / 25) := by
  refine ⟨lt_of_lt_of_le (by norm_num) (lowCoarseS41_hz12 hx hc).1,
    le_trans (by norm_num) (lowCoarseS41_hz38 hx hc).1, ?_,
    lt_of_le_of_lt (lowCoarseS41_hz46 hx hc).2 (by norm_num), ?_, ?_, (lowCoarseS41_hz106 hx hc).2.trans (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (lowCoarseS41_hz38 hx hc).1) (lowCoarseS41_hz38 hx hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) (lowCoarseS41_hz6 hx hc).1 2
    nlinarith only [h1,h2]
  · linarith only [(lowCoarseS41_hz55 hx hc).1,(lowCoarseS41_hz64 hx hc).2]
  · have hap : 0 < nap x := lt_of_lt_of_le (by norm_num) (lowCoarseS41_hz6 hx hc).1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul (lowCoarseS41_hz68 hx hc).2 (lowCoarseS41_hz6 hx hc).2 (le_trans (by norm_num) (lowCoarseS41_hz6 hx hc).1) (by norm_num)
    linarith only [h,(lowCoarseS41_hz55 hx hc).1,(lowCoarseS41_hz64 hx hc).2]

theorem lowCoarseS42_hz0 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B 0 (1 / 8000) x := hx

theorem lowCoarseS42_hz1 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B (18 / 25) (73 / 100) c := hc

theorem lowCoarseS42_hz2 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B (6782329983125268139 / 500000000000000000) (13564659966250536279 / 1000000000000000000) (√(184 : ℝ)) := bsqrt (bpoint (184 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS42_hz3 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS42_hz4 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B 0 (847791247890659 / 500000000000000000) ((√(184 : ℝ)) * x) := bmul (lowCoarseS42_hz2 hx hc) (lowCoarseS42_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS42_hz5 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B 1 (500847791247890659 / 500000000000000000) ((1 : ℝ) + ((√(184 : ℝ)) * x)) := badd (bpoint (1 : ℝ)) (lowCoarseS42_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS42_hz6 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B 1 (500847791247890659 / 500000000000000000) (nap x) := by
    convert (lowCoarseS42_hz5 hx hc) using 1 <;>
      norm_num [nap] <;> ring

theorem lowCoarseS42_hz7 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B 0 (1 / 64000000) (x^2) := bsq (lowCoarseS42_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS42_hz8 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B 0 (1 / 32000000) ((2 : ℝ) * (x^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS42_hz7 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS42_hz9 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B (31999999 / 32000000) 1 ((1 : ℝ) - ((2 : ℝ) * (x^2))) := bsub (bpoint (1 : ℝ)) (lowCoarseS42_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS42_hz10 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B (999999984374999877 / 1000000000000000000) 1 (√((1 : ℝ) - ((2 : ℝ) * (x^2)))) := bsqrt (lowCoarseS42_hz9 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS42_hz11 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B (998304401879218559 / 1000000000000000000) 1 ((√((1 : ℝ) - ((2 : ℝ) * (x^2)))) - ((√(184 : ℝ)) * x)) := bsub (lowCoarseS42_hz10 hx hc) (lowCoarseS42_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS42_hz12 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B (998304401879218559 / 1000000000000000000) 1 (nam x) := by
    convert (lowCoarseS42_hz11 hx hc) using 1 <;>
      norm_num [nam] <;> ring

theorem lowCoarseS42_hz13 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B (377929112326919899 / 500000000000000000) (755858224653839801 / 1000000000000000000) (kdot ((18 / 25))) := by
    constructor
    · apply bkdot_lower (q := (16138931695718579 / 40000000000000000)) (a := (191748501965466647 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (201736646196482237 / 500000000000000000)) (a := (95874250982733323 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS42_hz14 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B (324 / 625) (324 / 625) (((18 / 25) : ℝ)^2) := bsq (bpoint ((18 / 25) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS42_hz15 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B (301 / 625) (301 / 625) ((1 : ℝ) - (((18 / 25) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS42_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS42_hz16 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B (43373378932243681 / 62500000000000000) (693974062915898897 / 1000000000000000000) (√((1 : ℝ) - (((18 / 25) : ℝ)^2))) := bsqrt (lowCoarseS42_hz15 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS42_hz17 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B (55224701245315641 / 250000000000000000) (44179760996252513 / 200000000000000000) ((√((1 : ℝ) - (((18 / 25) : ℝ)^2))) / Real.pi) := bdiv (lowCoarseS42_hz16 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS42_hz18 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B (272108960875382327 / 500000000000000000) (544217921750764657 / 1000000000000000000) (((18 / 25) : ℝ) * (kdot ((18 / 25)))) := bmul (bpoint ((18 / 25) : ℝ)) (lowCoarseS42_hz13 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS42_hz19 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B (382558363366013609 / 500000000000000000) (382558363366013611 / 500000000000000000) (((√((1 : ℝ) - (((18 / 25) : ℝ)^2))) / Real.pi) + (((18 / 25) : ℝ) * (kdot ((18 / 25))))) := badd (lowCoarseS42_hz17 hx hc) (lowCoarseS42_hz18 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS42_hz20 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B (382558363366013609 / 500000000000000000) (382558363366013611 / 500000000000000000) (kappa ((18 / 25))) := by rw [kappa_eq]; exact (lowCoarseS42_hz19 hx hc)

theorem lowCoarseS42_hz21 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B (760479966967229373 / 1000000000000000000) (1216767947147567 / 1600000000000000) (kdot ((73 / 100))) := by
    constructor
    · apply bkdot_lower (q := (395056153175532391 / 1000000000000000000)) (a := (188118594040834201 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (39505615317553239 / 100000000000000000)) (a := (940592970204171 / 2500000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS42_hz22 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B (5329 / 10000) (5329 / 10000) (((73 / 100) : ℝ)^2) := bsq (bpoint ((73 / 100) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS42_hz23 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B (4671 / 10000) (4671 / 10000) ((1 : ℝ) - (((73 / 100) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS42_hz22 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS42_hz24 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B (136689428998734207 / 200000000000000000) (170861786248417759 / 250000000000000000) (√((1 : ℝ) - (((73 / 100) : ℝ)^2))) := bsqrt (lowCoarseS42_hz23 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS42_hz25 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B (217547982935572107 / 1000000000000000000) (54386995733893027 / 250000000000000000) ((√((1 : ℝ) - (((73 / 100) : ℝ)^2))) / Real.pi) := bdiv (lowCoarseS42_hz24 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS42_hz26 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B (277575187943038721 / 500000000000000000) (138787593971519361 / 250000000000000000) (((73 / 100) : ℝ) * (kdot ((73 / 100)))) := bmul (bpoint ((73 / 100) : ℝ)) (lowCoarseS42_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS42_hz27 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B (772698358821649549 / 1000000000000000000) (48293647426353097 / 62500000000000000) (((√((1 : ℝ) - (((73 / 100) : ℝ)^2))) / Real.pi) + (((73 / 100) : ℝ) * (kdot ((73 / 100))))) := badd (lowCoarseS42_hz25 hx hc) (lowCoarseS42_hz26 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS42_hz28 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B (772698358821649549 / 1000000000000000000) (48293647426353097 / 62500000000000000) (kappa ((73 / 100))) := by rw [kappa_eq]; exact (lowCoarseS42_hz27 hx hc)

theorem lowCoarseS42_hz29 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B (382558363366013609 / 500000000000000000) (48293647426353097 / 62500000000000000) (kappa c) := bkappa (lowCoarseS42_hz1 hx hc) (by norm_num) (by norm_num) (lowCoarseS42_hz20 hx hc).1 (lowCoarseS42_hz28 hx hc).2

theorem lowCoarseS42_hz30 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B (14206352573646903 / 62500000000000000) (117441636633986391 / 500000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (lowCoarseS42_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS42_hz31 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B (14206352573646903 / 31250000000000000) (117441636633986391 / 250000000000000000) ((2 : ℝ) * ((1 : ℝ) - (kappa c))) := bmul (bpoint (2 : ℝ)) (lowCoarseS42_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS42_hz32 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B 0 (1 / 8000000) ((8 : ℝ) * (x^2)) := bmul (bpoint (8 : ℝ)) (lowCoarseS42_hz7 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS42_hz33 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B (14206348667396903 / 31250000000000000) (117441636633986391 / 250000000000000000) (((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2))) := bsub (lowCoarseS42_hz31 hx hc) (lowCoarseS42_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS42_hz34 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B (674242654655355437 / 1000000000000000000) (685395175454237907 / 1000000000000000000) (√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) := bsqrt (lowCoarseS42_hz33 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS42_hz35 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B (6782329983125268139 / 250000000000000000) (13564659966250536279 / 500000000000000000) ((2 : ℝ) * (√(184 : ℝ))) := bmul (bpoint (2 : ℝ)) (lowCoarseS42_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS42_hz36 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B 0 (678232998312527 / 200000000000000000) (((2 : ℝ) * (√(184 : ℝ))) * x) := bmul (lowCoarseS42_hz35 hx hc) (lowCoarseS42_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS42_hz37 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B (335425744831896401 / 500000000000000000) (685395175454237907 / 1000000000000000000) ((√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) - (((2 : ℝ) * (√(184 : ℝ))) * x)) := bsub (lowCoarseS42_hz34 hx hc) (lowCoarseS42_hz36 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS42_hz38 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B (335425744831896401 / 500000000000000000) (685395175454237907 / 1000000000000000000) (ndm x c) := by
    convert (lowCoarseS42_hz37 hx hc) using 1 <;>
      norm_num [ndm] <;> ring

theorem lowCoarseS42_hz39 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B 1 (1003394039991562637 / 1000000000000000000) ((nap x)^2) := bsq (lowCoarseS42_hz6 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS42_hz40 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B 2 (1003394039991562637 / 500000000000000000) ((2 : ℝ) * ((nap x)^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS42_hz39 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS42_hz41 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B (4500417211841299 / 10000000000000000) (93953309307189113 / 200000000000000000) ((ndm x c)^2) := bsq (lowCoarseS42_hz38 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS42_hz42 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B (306046690692810887 / 200000000000000000) (778373179399497687 / 500000000000000000) (((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) := bsub (lowCoarseS42_hz40 hx hc) (lowCoarseS42_hz41 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS42_hz43 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B (199322335762284863 / 200000000000000000) 1 ((nam x)^2) := bsq (lowCoarseS42_hz12 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS42_hz44 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B (199322335762284863 / 100000000000000000) 2 ((2 : ℝ) * ((nam x)^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS42_hz43 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS42_hz45 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B (765116726732027217 / 1000000000000000000) (781019524402722737 / 1000000000000000000) ((((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) / ((2 : ℝ) * ((nam x)^2))) := bdiv (lowCoarseS42_hz42 hx hc) (lowCoarseS42_hz44 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS42_hz46 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B (765116726732027217 / 1000000000000000000) (781019524402722737 / 1000000000000000000) (nc1 x c) := by
    convert (lowCoarseS42_hz45 hx hc) using 1 <;>
      norm_num [nc1] <;> ring

theorem lowCoarseS42_hz47 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B (377929112326919899 / 500000000000000000) (1216767947147567 / 1600000000000000) (kdot c) := bkdot (lowCoarseS42_hz1 hx hc) (lowCoarseS42_hz13 hx hc).1 (lowCoarseS42_hz21 hx hc).2

theorem lowCoarseS42_hz48 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B (777318764771578703 / 1000000000000000000) (388659382385789353 / 500000000000000000) (kdot ((765116726732027217 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (18239349039720271 / 50000000000000000)) (a := (43723358292869313 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (364786980794405419 / 1000000000000000000)) (a := (174893433171477251 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS42_hz49 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B (157060019006144627 / 200000000000000000) (785300095030723137 / 1000000000000000000) (kdot ((781019524402722737 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (35064557052607587 / 100000000000000000)) (a := (33724982208895347 / 100000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (350645570526075869 / 1000000000000000000)) (a := (84312455522238367 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS42_hz50 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B (777318764771578703 / 1000000000000000000) (785300095030723137 / 1000000000000000000) (kdot (nc1 x c)) := bkdot (lowCoarseS42_hz46 hx hc) (lowCoarseS42_hz48 hx hc).1 (lowCoarseS42_hz49 hx hc).2

theorem lowCoarseS42_hz51 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B (324 / 625) (5329 / 10000) (c^2) := bsq (lowCoarseS42_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS42_hz52 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B (4671 / 10000) (301 / 625) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS42_hz51 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS42_hz53 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B (136689428998734207 / 200000000000000000) (693974062915898897 / 1000000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (lowCoarseS42_hz52 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS42_hz54 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B (258294572829825811 / 500000000000000000) (263876686221198377 / 500000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (lowCoarseS42_hz53 hx hc) (lowCoarseS42_hz47 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS42_hz55 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B (258294572829825811 / 500000000000000000) (263876686221198377 / 500000000000000000) (npa c) := by
    convert (lowCoarseS42_hz54 hx hc) using 1 <;>
      norm_num [npa] <;> ring

theorem lowCoarseS42_hz56 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B (217547982935572107 / 1000000000000000000) (44179760996252513 / 200000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (lowCoarseS42_hz53 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS42_hz57 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B (272108960875382327 / 500000000000000000) (138787593971519361 / 250000000000000000) (c * (kdot c)) := bmul (lowCoarseS42_hz1 hx hc) (lowCoarseS42_hz47 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS42_hz58 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B (-337602392950505337 / 1000000000000000000) (-323319116769502089 / 1000000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (lowCoarseS42_hz56 hx hc) (lowCoarseS42_hz57 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS42_hz59 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B (-337602392950505337 / 1000000000000000000) (-323319116769502089 / 1000000000000000000) (npp c) := by
    convert (lowCoarseS42_hz58 hx hc) using 1 <;>
      norm_num [npp] <;> ring

theorem lowCoarseS42_hz60 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B 0 (23 / 4000) ((46 : ℝ) * x) := bmul (bpoint (46 : ℝ)) (lowCoarseS42_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS42_hz61 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B (9591663046625439083 / 1000000000000000000) (2399353261656359771 / 250000000000000000) ((√(92 : ℝ)) + ((46 : ℝ) * x)) := badd (lowCoarseS42_hz3 hx hc) (lowCoarseS42_hz60 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS42_hz62 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B (28774989139876317249 / 250000000000000000) (7198059784969079313 / 62500000000000000) ((12 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (bpoint (12 : ℝ)) (lowCoarseS42_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS42_hz63 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B 0 (14396119569938159 / 1000000000000000000) (((12 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS42_hz62 hx hc) (lowCoarseS42_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS42_hz64 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B 0 (14396119569938159 / 1000000000000000000) (nr1 x) := by
    convert (lowCoarseS42_hz63 hx hc) using 1 <;>
      norm_num [nr1] <;> ring

theorem lowCoarseS42_hz65 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B (9591663046625439083 / 125000000000000000) (2399353261656359771 / 31250000000000000) ((8 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (bpoint (8 : ℝ)) (lowCoarseS42_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS42_hz66 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B 0 (59983831541409 / 6250000000000000) (((8 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS42_hz65 hx hc) (lowCoarseS42_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS42_hz67 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B 0 (59983831541409 / 6250000000000000) (nrpp x) := by
    convert (lowCoarseS42_hz66 hx hc) using 1 <;>
      norm_num [nrpp] <;> ring

theorem lowCoarseS42_hz68 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B 0 (847791247890659 / 500000000000000000) (ne0 x) := by
    convert (lowCoarseS42_hz4 hx hc) using 1 <;>
      norm_num [ne0] <;> ring

theorem lowCoarseS42_hz69 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B (258294572829825811 / 500000000000000000) (542149492012334913 / 1000000000000000000) ((npa c) + (nr1 x)) := badd (lowCoarseS42_hz55 hx hc) (lowCoarseS42_hz64 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS42_hz70 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B (258294572829825811 / 500000000000000000) (135767580257030593 / 250000000000000000) (((npa c) + (nr1 x)) / (nam x)) := bdiv (lowCoarseS42_hz69 hx hc) (lowCoarseS42_hz12 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS42_hz71 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B (258294572829825811 / 500000000000000000) (54476590352390369 / 100000000000000000) ((((npa c) + (nr1 x)) / (nam x)) + (ne0 x)) := badd (lowCoarseS42_hz70 hx hc) (lowCoarseS42_hz68 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS42_hz72 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B (258294572829825811 / 500000000000000000) (54476590352390369 / 100000000000000000) (nlam x c) := by
    convert (lowCoarseS42_hz71 hx hc) using 1 <;>
      norm_num [nlam] <;> ring

theorem lowCoarseS42_hz73 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS42_hz74 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B 0 (59947894041409 / 100000000000000000) ((√(23 : ℝ)) * x) := bmul (lowCoarseS42_hz73 hx hc) (lowCoarseS42_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS42_hz75 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B (1 / 2) (50059947894041409 / 100000000000000000) (((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)) := badd (bpoint ((1 / 2) : ℝ)) (lowCoarseS42_hz74 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS42_hz76 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B (176776695296636881 / 250000000000000000) (353765274914177413 / 500000000000000000) (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) := bsqrt (lowCoarseS42_hz75 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS42_hz77 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B 0 (59947894041409 / 50000000000000000) ((√(92 : ℝ)) * x) := bmul (lowCoarseS42_hz3 hx hc) (lowCoarseS42_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS42_hz78 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B (176776695296636881 / 250000000000000000) (354364753854591503 / 500000000000000000) ((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x)) := badd (lowCoarseS42_hz76 hx hc) (lowCoarseS42_hz77 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS42_hz79 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B (499999999999999999 / 1000000000000000000) (251148757548850447 / 500000000000000000) (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2) := bsq (lowCoarseS42_hz78 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS42_hz80 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B (499999999999999999 / 125000000000000000) (251148757548850447 / 62500000000000000) ((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) := bmul (bpoint (8 : ℝ)) (lowCoarseS42_hz79 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS42_hz81 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B (7673330437300351251 / 200000000000000000) (1928302689874485209 / 50000000000000000) (((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (lowCoarseS42_hz80 hx hc) (lowCoarseS42_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS42_hz82 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B 0 (2410378362343107 / 500000000000000000) ((((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS42_hz81 hx hc) (lowCoarseS42_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS42_hz83 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B 0 (2410378362343107 / 500000000000000000) (nrs x) := by
    convert (lowCoarseS42_hz82 hx hc) using 1 <;>
      norm_num [nrs] <;> ring

theorem lowCoarseS42_hz84 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B (-337602392950505337 / 1000000000000000000) (-313721703722876649 / 1000000000000000000) ((npp c) + (nrpp x)) := badd (lowCoarseS42_hz59 hx hc) (lowCoarseS42_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS42_hz85 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B (-265119191266631377 / 1000000000000000000) (-39215212965359581 / 250000000000000000) (if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) := bweaken (bfirst (lowCoarseS42_hz84 hx hc) (lowCoarseS42_hz50 hx hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem lowCoarseS42_hz86 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B (6671608635334219 / 25000000000000000) (296769889642215143 / 1000000000000000000) ((nlam x c)^2) := bsq (lowCoarseS42_hz72 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS42_hz87 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B (585403605525131611 / 1000000000000000000) (609991497498255217 / 1000000000000000000) ((nc1 x c)^2) := bsq (lowCoarseS42_hz46 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS42_hz88 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B (390008502501744783 / 1000000000000000000) (414596394474868389 / 1000000000000000000) ((1 : ℝ) - ((nc1 x c)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS42_hz87 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS42_hz89 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B (312253303626136509 / 500000000000000000) (643891601494279773 / 1000000000000000000) (√((1 : ℝ) - ((nc1 x c)^2))) := bsqrt (lowCoarseS42_hz88 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS42_hz90 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B (392389073892405441 / 200000000000000000) (202284512496259607 / 100000000000000000) (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))) := bmul pi_mem (lowCoarseS42_hz89 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS42_hz91 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B (131925248314946149 / 1000000000000000000) (30252615007683987 / 200000000000000000) (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2))))) := bdiv (lowCoarseS42_hz86 hx hc) (lowCoarseS42_hz90 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS42_hz92 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B (-33298485737921307 / 250000000000000000) (-5597776823018389 / 1000000000000000000) ((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) := badd (lowCoarseS42_hz85 hx hc) (lowCoarseS42_hz91 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS42_hz93 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B 0 (2875000000001 / 1000000000000000000) ((ne0 x)^2) := bsq (lowCoarseS42_hz68 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS42_hz94 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B (-33298485737921307 / 250000000000000000) (-1398725455754597 / 250000000000000000) (((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) + ((ne0 x)^2)) := badd (lowCoarseS42_hz92 hx hc) (lowCoarseS42_hz93 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS42_hz95 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B (-33298485737921307 / 250000000000000000) (-387072549166087 / 500000000000000000) ((((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) + ((ne0 x)^2)) + (nrs x)) := badd (lowCoarseS42_hz94 hx hc) (lowCoarseS42_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS42_hz96 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B (-33298485737921307 / 250000000000000000) (-387072549166087 / 500000000000000000) (nu x c) := by
    convert (lowCoarseS42_hz95 hx hc) using 1 <;>
      norm_num [nu] <;> ring

theorem lowCoarseS42_hz97 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B (-347199805997130777 / 1000000000000000000) (-323319116769502089 / 1000000000000000000) ((npp c) - (nrpp x)) := bsub (lowCoarseS42_hz59 hx hc) (lowCoarseS42_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS42_hz98 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B (-347199805997130777 / 1000000000000000000) (-323319116769502089 / 1000000000000000000) (min ((npp c) - (nrpp x)) (0 : ℝ)) := bweaken (bmin (lowCoarseS42_hz97 hx hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem lowCoarseS42_hz99 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B (-272656040644195437 / 1000000000000000000) (-251322016474307181 / 1000000000000000000) ((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) := bmul (lowCoarseS42_hz50 hx hc) (lowCoarseS42_hz98 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS42_hz100 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B (-136329457822097719 / 500000000000000000) (-251322016474307181 / 1000000000000000000) (((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) - ((ne0 x)^2)) := bsub (lowCoarseS42_hz99 hx hc) (lowCoarseS42_hz93 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS42_hz101 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B (-69369918092220413 / 250000000000000000) (-251322016474307181 / 1000000000000000000) ((((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) - ((ne0 x)^2)) - (nrs x)) := bsub (lowCoarseS42_hz100 hx hc) (lowCoarseS42_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS42_hz102 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B (-69369918092220413 / 250000000000000000) (-251322016474307181 / 1000000000000000000) (nl x c) := by
    convert (lowCoarseS42_hz101 hx hc) using 1 <;>
      norm_num [nl] <;> ring

theorem lowCoarseS42_hz103 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B 0 (33298485737921307 / 250000000000000000) |(nu x c)| := bweaken (babs (lowCoarseS42_hz96 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS42_hz104 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B 0 (69369918092220413 / 250000000000000000) |(nl x c)| := bweaken (babs (lowCoarseS42_hz102 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS42_hz105 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B 0 (69369918092220413 / 250000000000000000) (max |(nu x c)| |(nl x c)|) := bweaken (bmax (lowCoarseS42_hz103 hx hc) (lowCoarseS42_hz104 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS42_hz106 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) : B 0 (69369918092220413 / 250000000000000000) (ns x c) := by
    convert (lowCoarseS42_hz105 hx hc) using 1 <;>
      norm_num [ns] <;> ring

theorem lowCoarseS42 {x c : ℝ}
    (hx : B 0 (1/8000) x) (hc : B (18 / 25) (73 / 100) c) :
    0 < nam x ∧ 0 ≤ ndm x c ∧ ndm x c ^ 2 ≤ 2 * nap x ^ 2 ∧ nc1 x c < 1 ∧
    0 ≤ npa c - nr1 x ∧ ne0 x ≤ (npa c - nr1 x) / nap x ∧ ns x c ≤ (9 / 25) := by
  refine ⟨lt_of_lt_of_le (by norm_num) (lowCoarseS42_hz12 hx hc).1,
    le_trans (by norm_num) (lowCoarseS42_hz38 hx hc).1, ?_,
    lt_of_le_of_lt (lowCoarseS42_hz46 hx hc).2 (by norm_num), ?_, ?_, (lowCoarseS42_hz106 hx hc).2.trans (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (lowCoarseS42_hz38 hx hc).1) (lowCoarseS42_hz38 hx hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) (lowCoarseS42_hz6 hx hc).1 2
    nlinarith only [h1,h2]
  · linarith only [(lowCoarseS42_hz55 hx hc).1,(lowCoarseS42_hz64 hx hc).2]
  · have hap : 0 < nap x := lt_of_lt_of_le (by norm_num) (lowCoarseS42_hz6 hx hc).1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul (lowCoarseS42_hz68 hx hc).2 (lowCoarseS42_hz6 hx hc).2 (le_trans (by norm_num) (lowCoarseS42_hz6 hx hc).1) (by norm_num)
    linarith only [h,(lowCoarseS42_hz55 hx hc).1,(lowCoarseS42_hz64 hx hc).2]

theorem lowCoarseS43_hz0 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B 0 (1 / 8000) x := hx

theorem lowCoarseS43_hz1 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B (73 / 100) (37 / 50) c := hc

theorem lowCoarseS43_hz2 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B (6782329983125268139 / 500000000000000000) (13564659966250536279 / 1000000000000000000) (√(184 : ℝ)) := bsqrt (bpoint (184 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS43_hz3 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS43_hz4 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B 0 (847791247890659 / 500000000000000000) ((√(184 : ℝ)) * x) := bmul (lowCoarseS43_hz2 hx hc) (lowCoarseS43_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS43_hz5 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B 1 (500847791247890659 / 500000000000000000) ((1 : ℝ) + ((√(184 : ℝ)) * x)) := badd (bpoint (1 : ℝ)) (lowCoarseS43_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS43_hz6 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B 1 (500847791247890659 / 500000000000000000) (nap x) := by
    convert (lowCoarseS43_hz5 hx hc) using 1 <;>
      norm_num [nap] <;> ring

theorem lowCoarseS43_hz7 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B 0 (1 / 64000000) (x^2) := bsq (lowCoarseS43_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS43_hz8 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B 0 (1 / 32000000) ((2 : ℝ) * (x^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS43_hz7 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS43_hz9 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B (31999999 / 32000000) 1 ((1 : ℝ) - ((2 : ℝ) * (x^2))) := bsub (bpoint (1 : ℝ)) (lowCoarseS43_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS43_hz10 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B (999999984374999877 / 1000000000000000000) 1 (√((1 : ℝ) - ((2 : ℝ) * (x^2)))) := bsqrt (lowCoarseS43_hz9 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS43_hz11 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B (998304401879218559 / 1000000000000000000) 1 ((√((1 : ℝ) - ((2 : ℝ) * (x^2)))) - ((√(184 : ℝ)) * x)) := bsub (lowCoarseS43_hz10 hx hc) (lowCoarseS43_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS43_hz12 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B (998304401879218559 / 1000000000000000000) 1 (nam x) := by
    convert (lowCoarseS43_hz11 hx hc) using 1 <;>
      norm_num [nam] <;> ring

theorem lowCoarseS43_hz13 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B (760479966967229373 / 1000000000000000000) (1216767947147567 / 1600000000000000) (kdot ((73 / 100))) := by
    constructor
    · apply bkdot_lower (q := (395056153175532391 / 1000000000000000000)) (a := (188118594040834201 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (39505615317553239 / 100000000000000000)) (a := (940592970204171 / 2500000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS43_hz14 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B (5329 / 10000) (5329 / 10000) (((73 / 100) : ℝ)^2) := bsq (bpoint ((73 / 100) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS43_hz15 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B (4671 / 10000) (4671 / 10000) ((1 : ℝ) - (((73 / 100) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS43_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS43_hz16 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B (136689428998734207 / 200000000000000000) (170861786248417759 / 250000000000000000) (√((1 : ℝ) - (((73 / 100) : ℝ)^2))) := bsqrt (lowCoarseS43_hz15 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS43_hz17 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B (217547982935572107 / 1000000000000000000) (54386995733893027 / 250000000000000000) ((√((1 : ℝ) - (((73 / 100) : ℝ)^2))) / Real.pi) := bdiv (lowCoarseS43_hz16 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS43_hz18 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B (277575187943038721 / 500000000000000000) (138787593971519361 / 250000000000000000) (((73 / 100) : ℝ) * (kdot ((73 / 100)))) := bmul (bpoint ((73 / 100) : ℝ)) (lowCoarseS43_hz13 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS43_hz19 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B (772698358821649549 / 1000000000000000000) (48293647426353097 / 62500000000000000) (((√((1 : ℝ) - (((73 / 100) : ℝ)^2))) / Real.pi) + (((73 / 100) : ℝ) * (kdot ((73 / 100))))) := badd (lowCoarseS43_hz17 hx hc) (lowCoarseS43_hz18 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS43_hz20 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B (772698358821649549 / 1000000000000000000) (48293647426353097 / 62500000000000000) (kappa ((73 / 100))) := by rw [kappa_eq]; exact (lowCoarseS43_hz19 hx hc)

theorem lowCoarseS43_hz21 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B (765174530946819623 / 1000000000000000000) (382587265473409813 / 500000000000000000) (kdot ((37 / 50))) := by
    constructor
    · apply bkdot_lower (q := (193277835871267091 / 500000000000000000)) (a := (73772596845324881 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (386555671742534181 / 1000000000000000000)) (a := (368862984226624403 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS43_hz22 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B (1369 / 2500) (1369 / 2500) (((37 / 50) : ℝ)^2) := bsq (bpoint ((37 / 50) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS43_hz23 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B (1131 / 2500) (1131 / 2500) ((1 : ℝ) - (((37 / 50) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS43_hz22 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS43_hz24 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B (26904274753280379 / 40000000000000000) (168151717208002369 / 250000000000000000) (√((1 : ℝ) - (((37 / 50) : ℝ)^2))) := bsqrt (lowCoarseS43_hz23 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS43_hz25 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B (214097415864352757 / 1000000000000000000) (107048707932176379 / 500000000000000000) ((√((1 : ℝ) - (((37 / 50) : ℝ)^2))) / Real.pi) := bdiv (lowCoarseS43_hz24 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS43_hz26 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B (566229152900646521 / 1000000000000000000) (141557288225161631 / 250000000000000000) (((37 / 50) : ℝ) * (kdot ((37 / 50)))) := bmul (bpoint ((37 / 50) : ℝ)) (lowCoarseS43_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS43_hz27 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B (390163284382499639 / 500000000000000000) (390163284382499641 / 500000000000000000) (((√((1 : ℝ) - (((37 / 50) : ℝ)^2))) / Real.pi) + (((37 / 50) : ℝ) * (kdot ((37 / 50))))) := badd (lowCoarseS43_hz25 hx hc) (lowCoarseS43_hz26 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS43_hz28 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B (390163284382499639 / 500000000000000000) (390163284382499641 / 500000000000000000) (kappa ((37 / 50))) := by rw [kappa_eq]; exact (lowCoarseS43_hz27 hx hc)

theorem lowCoarseS43_hz29 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B (772698358821649549 / 1000000000000000000) (390163284382499641 / 500000000000000000) (kappa c) := bkappa (lowCoarseS43_hz1 hx hc) (by norm_num) (by norm_num) (lowCoarseS43_hz20 hx hc).1 (lowCoarseS43_hz28 hx hc).2

theorem lowCoarseS43_hz30 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B (109836715617500359 / 500000000000000000) (227301641178350451 / 1000000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (lowCoarseS43_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS43_hz31 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B (109836715617500359 / 250000000000000000) (227301641178350451 / 500000000000000000) ((2 : ℝ) * ((1 : ℝ) - (kappa c))) := bmul (bpoint (2 : ℝ)) (lowCoarseS43_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS43_hz32 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B 0 (1 / 8000000) ((8 : ℝ) * (x^2)) := bmul (bpoint (8 : ℝ)) (lowCoarseS43_hz7 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS43_hz33 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B (109836684367500359 / 250000000000000000) (227301641178350451 / 500000000000000000) (((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2))) := bsub (lowCoarseS43_hz31 hx hc) (lowCoarseS43_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS43_hz34 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B (662832360005153517 / 1000000000000000000) (674242747351946607 / 1000000000000000000) (√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) := bsqrt (lowCoarseS43_hz33 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS43_hz35 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B (6782329983125268139 / 250000000000000000) (13564659966250536279 / 500000000000000000) ((2 : ℝ) * (√(184 : ℝ))) := bmul (bpoint (2 : ℝ)) (lowCoarseS43_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS43_hz36 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B 0 (678232998312527 / 200000000000000000) (((2 : ℝ) * (√(184 : ℝ))) * x) := bmul (lowCoarseS43_hz35 hx hc) (lowCoarseS43_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS43_hz37 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B (329720597506795441 / 500000000000000000) (674242747351946607 / 1000000000000000000) ((√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) - (((2 : ℝ) * (√(184 : ℝ))) * x)) := bsub (lowCoarseS43_hz34 hx hc) (lowCoarseS43_hz36 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS43_hz38 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B (329720597506795441 / 500000000000000000) (674242747351946607 / 1000000000000000000) (ndm x c) := by
    convert (lowCoarseS43_hz37 hx hc) using 1 <;>
      norm_num [ndm] <;> ring

theorem lowCoarseS43_hz39 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B 1 (1003394039991562637 / 1000000000000000000) ((nap x)^2) := bsq (lowCoarseS43_hz6 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS43_hz40 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B 2 (1003394039991562637 / 500000000000000000) ((2 : ℝ) * ((nap x)^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS43_hz39 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS43_hz41 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B (434862689680952799 / 1000000000000000000) (56825410294587613 / 125000000000000000) ((ndm x c)^2) := bsq (lowCoarseS43_hz38 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS43_hz42 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B (193174589705412387 / 125000000000000000) (62877015612086899 / 40000000000000000) (((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) := bsub (lowCoarseS43_hz40 hx hc) (lowCoarseS43_hz41 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS43_hz43 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B (199322335762284863 / 200000000000000000) 1 ((nam x)^2) := bsq (lowCoarseS43_hz12 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS43_hz44 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B (199322335762284863 / 100000000000000000) 2 ((2 : ℝ) * ((nam x)^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS43_hz43 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS43_hz45 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B (193174589705412387 / 250000000000000000) (157726968660138207 / 200000000000000000) ((((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) / ((2 : ℝ) * ((nam x)^2))) := bdiv (lowCoarseS43_hz42 hx hc) (lowCoarseS43_hz44 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS43_hz46 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B (193174589705412387 / 250000000000000000) (157726968660138207 / 200000000000000000) (nc1 x c) := by
    convert (lowCoarseS43_hz45 hx hc) using 1 <;>
      norm_num [nc1] <;> ring

theorem lowCoarseS43_hz47 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B (760479966967229373 / 1000000000000000000) (382587265473409813 / 500000000000000000) (kdot c) := bkdot (lowCoarseS43_hz1 hx hc) (lowCoarseS43_hz13 hx hc).1 (lowCoarseS43_hz21 hx hc).2

theorem lowCoarseS43_hz48 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B (48818340747612993 / 62500000000000000) (781093451961807891 / 1000000000000000000) (kdot ((193174589705412387 / 250000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (44760391599248409 / 125000000000000000)) (a := (343857601569742751 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (358083132793987271 / 1000000000000000000)) (a := (343857601569742749 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS43_hz49 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B (197302941498213521 / 250000000000000000) (789211765992854087 / 1000000000000000000) (kdot ((157726968660138207 / 200000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (343760406792794397 / 1000000000000000000)) (a := (82776345927501979 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (85940101698198599 / 250000000000000000)) (a := (165552691855003957 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS43_hz50 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B (48818340747612993 / 62500000000000000) (789211765992854087 / 1000000000000000000) (kdot (nc1 x c)) := bkdot (lowCoarseS43_hz46 hx hc) (lowCoarseS43_hz48 hx hc).1 (lowCoarseS43_hz49 hx hc).2

theorem lowCoarseS43_hz51 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B (5329 / 10000) (1369 / 2500) (c^2) := bsq (lowCoarseS43_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS43_hz52 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B (1131 / 2500) (4671 / 10000) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS43_hz51 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS43_hz53 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B (26904274753280379 / 40000000000000000) (170861786248417759 / 250000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (lowCoarseS43_hz52 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS43_hz54 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B (102300809878259629 / 200000000000000000) (522956348597475259 / 1000000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (lowCoarseS43_hz53 hx hc) (lowCoarseS43_hz47 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS43_hz55 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B (102300809878259629 / 200000000000000000) (522956348597475259 / 1000000000000000000) (npa c) := by
    convert (lowCoarseS43_hz54 hx hc) using 1 <;>
      norm_num [npa] <;> ring

theorem lowCoarseS43_hz56 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B (214097415864352757 / 1000000000000000000) (54386995733893027 / 250000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (lowCoarseS43_hz53 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS43_hz57 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B (277575187943038721 / 500000000000000000) (141557288225161631 / 250000000000000000) (c * (kdot c)) := bmul (lowCoarseS43_hz1 hx hc) (lowCoarseS43_hz47 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS43_hz58 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B (-352131737036293767 / 1000000000000000000) (-168801196475252667 / 500000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (lowCoarseS43_hz56 hx hc) (lowCoarseS43_hz57 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS43_hz59 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B (-352131737036293767 / 1000000000000000000) (-168801196475252667 / 500000000000000000) (npp c) := by
    convert (lowCoarseS43_hz58 hx hc) using 1 <;>
      norm_num [npp] <;> ring

theorem lowCoarseS43_hz60 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B 0 (23 / 4000) ((46 : ℝ) * x) := bmul (bpoint (46 : ℝ)) (lowCoarseS43_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS43_hz61 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B (9591663046625439083 / 1000000000000000000) (2399353261656359771 / 250000000000000000) ((√(92 : ℝ)) + ((46 : ℝ) * x)) := badd (lowCoarseS43_hz3 hx hc) (lowCoarseS43_hz60 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS43_hz62 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B (28774989139876317249 / 250000000000000000) (7198059784969079313 / 62500000000000000) ((12 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (bpoint (12 : ℝ)) (lowCoarseS43_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS43_hz63 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B 0 (14396119569938159 / 1000000000000000000) (((12 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS43_hz62 hx hc) (lowCoarseS43_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS43_hz64 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B 0 (14396119569938159 / 1000000000000000000) (nr1 x) := by
    convert (lowCoarseS43_hz63 hx hc) using 1 <;>
      norm_num [nr1] <;> ring

theorem lowCoarseS43_hz65 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B (9591663046625439083 / 125000000000000000) (2399353261656359771 / 31250000000000000) ((8 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (bpoint (8 : ℝ)) (lowCoarseS43_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS43_hz66 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B 0 (59983831541409 / 6250000000000000) (((8 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS43_hz65 hx hc) (lowCoarseS43_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS43_hz67 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B 0 (59983831541409 / 6250000000000000) (nrpp x) := by
    convert (lowCoarseS43_hz66 hx hc) using 1 <;>
      norm_num [nrpp] <;> ring

theorem lowCoarseS43_hz68 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B 0 (847791247890659 / 500000000000000000) (ne0 x) := by
    convert (lowCoarseS43_hz4 hx hc) using 1 <;>
      norm_num [ne0] <;> ring

theorem lowCoarseS43_hz69 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B (102300809878259629 / 200000000000000000) (268676234083706709 / 500000000000000000) ((npa c) + (nr1 x)) := badd (lowCoarseS43_hz55 hx hc) (lowCoarseS43_hz64 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS43_hz70 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B (102300809878259629 / 200000000000000000) (538265149543461453 / 1000000000000000000) (((npa c) + (nr1 x)) / (nam x)) := bdiv (lowCoarseS43_hz69 hx hc) (lowCoarseS43_hz12 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS43_hz71 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B (102300809878259629 / 200000000000000000) (539960732039242771 / 1000000000000000000) ((((npa c) + (nr1 x)) / (nam x)) + (ne0 x)) := badd (lowCoarseS43_hz70 hx hc) (lowCoarseS43_hz68 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS43_hz72 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B (102300809878259629 / 200000000000000000) (539960732039242771 / 1000000000000000000) (nlam x c) := by
    convert (lowCoarseS43_hz71 hx hc) using 1 <;>
      norm_num [nlam] <;> ring

theorem lowCoarseS43_hz73 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS43_hz74 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B 0 (59947894041409 / 100000000000000000) ((√(23 : ℝ)) * x) := bmul (lowCoarseS43_hz73 hx hc) (lowCoarseS43_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS43_hz75 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B (1 / 2) (50059947894041409 / 100000000000000000) (((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)) := badd (bpoint ((1 / 2) : ℝ)) (lowCoarseS43_hz74 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS43_hz76 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B (176776695296636881 / 250000000000000000) (353765274914177413 / 500000000000000000) (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) := bsqrt (lowCoarseS43_hz75 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS43_hz77 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B 0 (59947894041409 / 50000000000000000) ((√(92 : ℝ)) * x) := bmul (lowCoarseS43_hz3 hx hc) (lowCoarseS43_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS43_hz78 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B (176776695296636881 / 250000000000000000) (354364753854591503 / 500000000000000000) ((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x)) := badd (lowCoarseS43_hz76 hx hc) (lowCoarseS43_hz77 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS43_hz79 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B (499999999999999999 / 1000000000000000000) (251148757548850447 / 500000000000000000) (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2) := bsq (lowCoarseS43_hz78 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS43_hz80 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B (499999999999999999 / 125000000000000000) (251148757548850447 / 62500000000000000) ((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) := bmul (bpoint (8 : ℝ)) (lowCoarseS43_hz79 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS43_hz81 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B (7673330437300351251 / 200000000000000000) (1928302689874485209 / 50000000000000000) (((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (lowCoarseS43_hz80 hx hc) (lowCoarseS43_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS43_hz82 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B 0 (2410378362343107 / 500000000000000000) ((((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS43_hz81 hx hc) (lowCoarseS43_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS43_hz83 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B 0 (2410378362343107 / 500000000000000000) (nrs x) := by
    convert (lowCoarseS43_hz82 hx hc) using 1 <;>
      norm_num [nrs] <;> ring

theorem lowCoarseS43_hz84 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B (-352131737036293767 / 1000000000000000000) (-164002489951939947 / 500000000000000000) ((npp c) + (nrpp x)) := badd (lowCoarseS43_hz59 hx hc) (lowCoarseS43_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS43_hz85 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B (-69476627512136177 / 250000000000000000) (-164002489951939947 / 1000000000000000000) (if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) := bweaken (bfirst (lowCoarseS43_hz84 hx hc) (lowCoarseS43_hz50 hx hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem lowCoarseS43_hz86 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B (65409098135923893 / 250000000000000000) (58311518428870987 / 200000000000000000) ((nlam x c)^2) := bsq (lowCoarseS43_hz72 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS43_hz87 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B (597062753725670677 / 1000000000000000000) (19435778627122047 / 31250000000000000) ((nc1 x c)^2) := bsq (lowCoarseS43_hz46 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS43_hz88 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B (11814221372877953 / 31250000000000000) (402937246274329323 / 1000000000000000000) ((1 : ℝ) - ((nc1 x c)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS43_hz87 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS43_hz89 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B (614861841336811611 / 1000000000000000000) (634773381825616033 / 1000000000000000000) (√((1 : ℝ) - ((nc1 x c)^2))) := bsqrt (lowCoarseS43_hz88 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS43_hz90 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B (482911360929105103 / 250000000000000000) (997099696518852053 / 500000000000000000) (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))) := bmul pi_mem (lowCoarseS43_hz89 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS43_hz91 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B (524794849416041 / 4000000000000000) (150937426478954649 / 1000000000000000000) (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2))))) := bdiv (lowCoarseS43_hz86 hx hc) (lowCoarseS43_hz90 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS43_hz92 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B (-73353898847267229 / 500000000000000000) (-6532531736492649 / 500000000000000000) ((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) := badd (lowCoarseS43_hz85 hx hc) (lowCoarseS43_hz91 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS43_hz93 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B 0 (2875000000001 / 1000000000000000000) ((ne0 x)^2) := bsq (lowCoarseS43_hz68 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS43_hz94 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B (-73353898847267229 / 500000000000000000) (-13062188472985297 / 1000000000000000000) (((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) + ((ne0 x)^2)) := badd (lowCoarseS43_hz92 hx hc) (lowCoarseS43_hz93 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS43_hz95 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B (-73353898847267229 / 500000000000000000) (-8241431748299083 / 1000000000000000000) ((((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) + ((ne0 x)^2)) + (nrs x)) := badd (lowCoarseS43_hz94 hx hc) (lowCoarseS43_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS43_hz96 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B (-73353898847267229 / 500000000000000000) (-8241431748299083 / 1000000000000000000) (nu x c) := by
    convert (lowCoarseS43_hz95 hx hc) using 1 <;>
      norm_num [nu] <;> ring

theorem lowCoarseS43_hz97 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B (-361729150082919207 / 1000000000000000000) (-168801196475252667 / 500000000000000000) ((npp c) - (nrpp x)) := bsub (lowCoarseS43_hz59 hx hc) (lowCoarseS43_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS43_hz98 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B (-361729150082919207 / 1000000000000000000) (-168801196475252667 / 500000000000000000) (min ((npp c) - (nrpp x)) (0 : ℝ)) := bweaken (bmin (lowCoarseS43_hz97 hx hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem lowCoarseS43_hz99 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B (-285480901348034829 / 1000000000000000000) (-4120297164066827 / 15625000000000000) ((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) := bmul (lowCoarseS43_hz50 hx hc) (lowCoarseS43_hz98 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS43_hz100 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B (-28548377634803483 / 100000000000000000) (-4120297164066827 / 15625000000000000) (((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) - ((ne0 x)^2)) := bsub (lowCoarseS43_hz99 hx hc) (lowCoarseS43_hz93 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS43_hz101 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B (-72576133268180261 / 250000000000000000) (-4120297164066827 / 15625000000000000) ((((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) - ((ne0 x)^2)) - (nrs x)) := bsub (lowCoarseS43_hz100 hx hc) (lowCoarseS43_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS43_hz102 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B (-72576133268180261 / 250000000000000000) (-4120297164066827 / 15625000000000000) (nl x c) := by
    convert (lowCoarseS43_hz101 hx hc) using 1 <;>
      norm_num [nl] <;> ring

theorem lowCoarseS43_hz103 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B 0 (73353898847267229 / 500000000000000000) |(nu x c)| := bweaken (babs (lowCoarseS43_hz96 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS43_hz104 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B 0 (72576133268180261 / 250000000000000000) |(nl x c)| := bweaken (babs (lowCoarseS43_hz102 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS43_hz105 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B 0 (72576133268180261 / 250000000000000000) (max |(nu x c)| |(nl x c)|) := bweaken (bmax (lowCoarseS43_hz103 hx hc) (lowCoarseS43_hz104 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS43_hz106 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) : B 0 (72576133268180261 / 250000000000000000) (ns x c) := by
    convert (lowCoarseS43_hz105 hx hc) using 1 <;>
      norm_num [ns] <;> ring

theorem lowCoarseS43 {x c : ℝ}
    (hx : B 0 (1/8000) x) (hc : B (73 / 100) (37 / 50) c) :
    0 < nam x ∧ 0 ≤ ndm x c ∧ ndm x c ^ 2 ≤ 2 * nap x ^ 2 ∧ nc1 x c < 1 ∧
    0 ≤ npa c - nr1 x ∧ ne0 x ≤ (npa c - nr1 x) / nap x ∧ ns x c ≤ (9 / 25) := by
  refine ⟨lt_of_lt_of_le (by norm_num) (lowCoarseS43_hz12 hx hc).1,
    le_trans (by norm_num) (lowCoarseS43_hz38 hx hc).1, ?_,
    lt_of_le_of_lt (lowCoarseS43_hz46 hx hc).2 (by norm_num), ?_, ?_, (lowCoarseS43_hz106 hx hc).2.trans (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (lowCoarseS43_hz38 hx hc).1) (lowCoarseS43_hz38 hx hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) (lowCoarseS43_hz6 hx hc).1 2
    nlinarith only [h1,h2]
  · linarith only [(lowCoarseS43_hz55 hx hc).1,(lowCoarseS43_hz64 hx hc).2]
  · have hap : 0 < nap x := lt_of_lt_of_le (by norm_num) (lowCoarseS43_hz6 hx hc).1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul (lowCoarseS43_hz68 hx hc).2 (lowCoarseS43_hz6 hx hc).2 (le_trans (by norm_num) (lowCoarseS43_hz6 hx hc).1) (by norm_num)
    linarith only [h,(lowCoarseS43_hz55 hx hc).1,(lowCoarseS43_hz64 hx hc).2]

end BstLean.BlueprintLow
