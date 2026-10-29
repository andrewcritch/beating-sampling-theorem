import BstLean.Part291Windows
namespace BstLean.BlueprintLow
open Real BstLean.Part130 BstLean.Part182 BstLean.Part197 BstLean.Part246 BstLean.Part255 BstLean.Part264b
theorem lowGroupedE12W_hz0 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B 0 (1 / 8000) x := hx

theorem lowGroupedE12W_hz1 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B (95039643 / 250000000) (729879757 / 1000000000) c := hc

theorem lowGroupedE12W_hz2 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B (6782329983125268139 / 500000000000000000) (13564659966250536279 / 1000000000000000000) (√(184 : ℝ)) := bsqrt (bpoint (184 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE12W_hz3 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE12W_hz4 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (1414213562373095049 / 1000000000000000000) (√(2 : ℝ)) := bsqrt (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE12W_hz5 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B 0 (847791247890659 / 500000000000000000) ((√(184 : ℝ)) * x) := bmul (lowGroupedE12W_hz2 hx hc) (lowGroupedE12W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12W_hz6 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B 1 (500847791247890659 / 500000000000000000) ((1 : ℝ) + ((√(184 : ℝ)) * x)) := badd (bpoint (1 : ℝ)) (lowGroupedE12W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12W_hz7 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B 1 (500847791247890659 / 500000000000000000) (nap x) := by
    convert (lowGroupedE12W_hz6 hx hc) using 1 <;>
      norm_num [nap] <;> ring

theorem lowGroupedE12W_hz8 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B 0 (1 / 64000000) (x^2) := bsq (lowGroupedE12W_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE12W_hz9 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B 0 (1 / 32000000) ((2 : ℝ) * (x^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE12W_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12W_hz10 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B (31999999 / 32000000) 1 ((1 : ℝ) - ((2 : ℝ) * (x^2))) := bsub (bpoint (1 : ℝ)) (lowGroupedE12W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12W_hz11 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B (999999984374999877 / 1000000000000000000) 1 (√((1 : ℝ) - ((2 : ℝ) * (x^2)))) := bsqrt (lowGroupedE12W_hz10 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE12W_hz12 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B (998304401879218559 / 1000000000000000000) 1 ((√((1 : ℝ) - ((2 : ℝ) * (x^2)))) - ((√(184 : ℝ)) * x)) := bsub (lowGroupedE12W_hz11 hx hc) (lowGroupedE12W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12W_hz13 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B (998304401879218559 / 1000000000000000000) 1 (nam x) := by
    convert (lowGroupedE12W_hz12 hx hc) using 1 <;>
      norm_num [nam] <;> ring

theorem lowGroupedE12W_hz14 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B (624130585078544481 / 1000000000000000000) (124826117031498039 / 200000000000000000) (kdot ((95039643 / 250000000))) := by
    constructor
    · apply bkdot_lower (q := (335077919748257003 / 500000000000000000)) (a := (295207148156584617 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (134031167899302801 / 200000000000000000)) (a := (295207148094580799 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE12W_hz15 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B (9032533741567449 / 62500000000000000) (9032533741567449 / 62500000000000000) (((95039643 / 250000000) : ℝ)^2) := bsq (bpoint ((95039643 / 250000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE12W_hz16 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B (53467466258432551 / 62500000000000000) (53467466258432551 / 62500000000000000) ((1 : ℝ) - (((95039643 / 250000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowGroupedE12W_hz15 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12W_hz17 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B (924921326456969969 / 1000000000000000000) (92492132645696997 / 100000000000000000) (√((1 : ℝ) - (((95039643 / 250000000) : ℝ)^2))) := bsqrt (lowGroupedE12W_hz16 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE12W_hz18 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B (147205801076739403 / 500000000000000000) (294411602153478807 / 1000000000000000000) ((√((1 : ℝ) - (((95039643 / 250000000) : ℝ)^2))) / Real.pi) := bdiv (lowGroupedE12W_hz17 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE12W_hz19 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B (237268591964983977 / 1000000000000000000) (59317147998748967 / 250000000000000000) (((95039643 / 250000000) : ℝ) * (kdot ((95039643 / 250000000)))) := bmul (bpoint ((95039643 / 250000000) : ℝ)) (lowGroupedE12W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12W_hz20 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B (531680194118462783 / 1000000000000000000) (21267207765938987 / 40000000000000000) (((√((1 : ℝ) - (((95039643 / 250000000) : ℝ)^2))) / Real.pi) + (((95039643 / 250000000) : ℝ) * (kdot ((95039643 / 250000000))))) := badd (lowGroupedE12W_hz18 hx hc) (lowGroupedE12W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12W_hz21 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B (531680194118462783 / 1000000000000000000) (21267207765938987 / 40000000000000000) (kappa ((95039643 / 250000000))) := by rw [kappa_eq]; exact (lowGroupedE12W_hz20 hx hc)

theorem lowGroupedE12W_hz22 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B (380211985019853361 / 500000000000000000) (190105992509926681 / 250000000000000000) (kdot ((729879757 / 1000000000))) := by
    constructor
    · apply bkdot_lower (q := (197578922151301239 / 500000000000000000)) (a := (376325147849732783 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (395157844302602477 / 1000000000000000000)) (a := (376325147849732781 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE12W_hz23 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B (532724459678379049 / 1000000000000000000) (532724459678379049 / 1000000000000000000) (((729879757 / 1000000000) : ℝ)^2) := bsq (bpoint ((729879757 / 1000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE12W_hz24 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B (467275540321620951 / 1000000000000000000) (467275540321620951 / 1000000000000000000) ((1 : ℝ) - (((729879757 / 1000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowGroupedE12W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12W_hz25 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B (42723472229926863 / 62500000000000000) (683575555678829809 / 1000000000000000000) (√((1 : ℝ) - (((729879757 / 1000000000) : ℝ)^2))) := bsqrt (lowGroupedE12W_hz24 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE12W_hz26 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B (217588857326149779 / 1000000000000000000) (10879442866307489 / 50000000000000000) ((√((1 : ℝ) - (((729879757 / 1000000000) : ℝ)^2))) / Real.pi) := bdiv (lowGroupedE12W_hz25 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE12W_hz27 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B (277509031234778211 / 500000000000000000) (22200722498782257 / 40000000000000000) (((729879757 / 1000000000) : ℝ) * (kdot ((729879757 / 1000000000)))) := bmul (bpoint ((729879757 / 1000000000) : ℝ)) (lowGroupedE12W_hz22 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12W_hz28 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B (772606919795706201 / 1000000000000000000) (154521383959141241 / 200000000000000000) (((√((1 : ℝ) - (((729879757 / 1000000000) : ℝ)^2))) / Real.pi) + (((729879757 / 1000000000) : ℝ) * (kdot ((729879757 / 1000000000))))) := badd (lowGroupedE12W_hz26 hx hc) (lowGroupedE12W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12W_hz29 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B (772606919795706201 / 1000000000000000000) (154521383959141241 / 200000000000000000) (kappa ((729879757 / 1000000000))) := by rw [kappa_eq]; exact (lowGroupedE12W_hz28 hx hc)

theorem lowGroupedE12W_hz30 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B (531680194118462783 / 1000000000000000000) (154521383959141241 / 200000000000000000) (kappa c) := bkappa (lowGroupedE12W_hz1 hx hc) (by norm_num) (by norm_num) (lowGroupedE12W_hz21 hx hc).1 (lowGroupedE12W_hz29 hx hc).2

theorem lowGroupedE12W_hz31 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B (45478616040858759 / 200000000000000000) (468319805881537217 / 1000000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (lowGroupedE12W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12W_hz32 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B (45478616040858759 / 100000000000000000) (468319805881537217 / 500000000000000000) ((2 : ℝ) * ((1 : ℝ) - (kappa c))) := bmul (bpoint (2 : ℝ)) (lowGroupedE12W_hz31 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12W_hz33 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B 0 (1 / 8000000) ((8 : ℝ) * (x^2)) := bmul (bpoint (8 : ℝ)) (lowGroupedE12W_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12W_hz34 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B (45478603540858759 / 100000000000000000) (468319805881537217 / 500000000000000000) (((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2))) := bsub (lowGroupedE12W_hz32 hx hc) (lowGroupedE12W_hz33 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12W_hz35 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B (67437825840442661 / 100000000000000000) (483900715995304773 / 500000000000000000) (√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) := bsqrt (lowGroupedE12W_hz34 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE12W_hz36 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B (6782329983125268139 / 250000000000000000) (13564659966250536279 / 500000000000000000) ((2 : ℝ) * (√(184 : ℝ))) := bmul (bpoint (2 : ℝ)) (lowGroupedE12W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12W_hz37 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B 0 (678232998312527 / 200000000000000000) (((2 : ℝ) * (√(184 : ℝ))) * x) := bmul (lowGroupedE12W_hz36 hx hc) (lowGroupedE12W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12W_hz38 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B (26839483736514559 / 40000000000000000) (483900715995304773 / 500000000000000000) ((√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) - (((2 : ℝ) * (√(184 : ℝ))) * x)) := bsub (lowGroupedE12W_hz35 hx hc) (lowGroupedE12W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12W_hz39 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B (26839483736514559 / 40000000000000000) (483900715995304773 / 500000000000000000) (ndm x c) := by
    convert (lowGroupedE12W_hz38 hx hc) using 1 <;>
      norm_num [ndm] <;> ring

theorem lowGroupedE12W_hz40 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B 1 (1003394039991562637 / 1000000000000000000) ((nap x)^2) := bsq (lowGroupedE12W_hz7 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE12W_hz41 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B 2 (1003394039991562637 / 500000000000000000) ((2 : ℝ) * ((nap x)^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE12W_hz40 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12W_hz42 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B (90044735905328689 / 200000000000000000) (187327922352614887 / 200000000000000000) ((ndm x c)^2) := bsq (lowGroupedE12W_hz39 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE12W_hz43 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B (212672077647385113 / 200000000000000000) (1556564400456481829 / 1000000000000000000) (((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) := bsub (lowGroupedE12W_hz41 hx hc) (lowGroupedE12W_hz42 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12W_hz44 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B (199322335762284863 / 200000000000000000) 1 ((nam x)^2) := bsq (lowGroupedE12W_hz13 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE12W_hz45 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B (199322335762284863 / 100000000000000000) 2 ((2 : ℝ) * ((nam x)^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE12W_hz44 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12W_hz46 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B (265840097059231391 / 500000000000000000) (390464117958377343 / 500000000000000000) ((((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) / ((2 : ℝ) * ((nam x)^2))) := bdiv (lowGroupedE12W_hz43 hx hc) (lowGroupedE12W_hz45 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE12W_hz47 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B (265840097059231391 / 500000000000000000) (390464117958377343 / 500000000000000000) (nc1 x c) := by
    convert (lowGroupedE12W_hz46 hx hc) using 1 <;>
      norm_num [nc1] <;> ring

theorem lowGroupedE12W_hz48 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B (42402447645530313 / 62500000000000000) (678439162328491413 / 1000000000000000000) (kdot ((265840097059231391 / 500000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (138237930294728233 / 250000000000000000)) (a := (505106582655505767 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (552951721178912931 / 1000000000000000000)) (a := (505106582655495707 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE12W_hz49 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B (785253569706960071 / 1000000000000000000) (98156696213370009 / 125000000000000000) (kdot ((390464117958377343 / 500000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (87681910003627299 / 250000000000000000)) (a := (67464580779324687 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (70145528002901839 / 200000000000000000)) (a := (168661451948311717 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE12W_hz50 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B (42402447645530313 / 62500000000000000) (98156696213370009 / 125000000000000000) (kdot (nc1 x c)) := bkdot (lowGroupedE12W_hz47 hx hc) (lowGroupedE12W_hz48 hx hc).1 (lowGroupedE12W_hz49 hx hc).2

theorem lowGroupedE12W_hz51 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE12W_hz52 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B 0 (59947894041409 / 100000000000000000) ((√(23 : ℝ)) * x) := bmul (lowGroupedE12W_hz51 hx hc) (lowGroupedE12W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12W_hz53 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B (1 / 2) (50059947894041409 / 100000000000000000) (((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)) := badd (bpoint ((1 / 2) : ℝ)) (lowGroupedE12W_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12W_hz54 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B (42402447645530313 / 125000000000000000) (98156696213370009 / 250000000000000000) ((kdot (nc1 x c)) / (2 : ℝ)) := bdiv (lowGroupedE12W_hz50 hx hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE12W_hz55 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B (42402447645530313 / 125000000000000000) (196613131896947063 / 500000000000000000) (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)) := badd (lowGroupedE12W_hz54 hx hc) (lowGroupedE12W_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12W_hz56 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B (380211985019853361 / 1000000000000000000) (190105992509926681 / 500000000000000000) ((kdot ((729879757 / 1000000000))) / (2 : ℝ)) := bdiv (lowGroupedE12W_hz22 hx hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE12W_hz57 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B (380211985019853361 / 1000000000000000000) (95202865990066863 / 250000000000000000) (((kdot ((729879757 / 1000000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x)) := badd (lowGroupedE12W_hz56 hx hc) (lowGroupedE12W_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12W_hz58 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B (176776695296636881 / 250000000000000000) (353765274914177413 / 500000000000000000) (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE12W_hz53 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE12W_hz59 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGroupedE12W_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE12W_hz60 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B (176776695296636881 / 250000000000000000) (28748435588634151 / 40000000000000000) ((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) := badd (lowGroupedE12W_hz58 hx hc) (lowGroupedE12W_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12W_hz61 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B 0 (59947894041409 / 50000000000000000) ((√(92 : ℝ)) * x) := bmul (lowGroupedE12W_hz3 hx hc) (lowGroupedE12W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12W_hz62 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B (176776695296636881 / 250000000000000000) (143981969519336391 / 200000000000000000) (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE12W_hz60 hx hc) (lowGroupedE12W_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12W_hz63 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B (499999999999999999 / 500000000000000000) (1018106270157175527 / 1000000000000000000) ((√(2 : ℝ)) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE12W_hz4 hx hc) (lowGroupedE12W_hz62 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12W_hz64 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B (499999999999999999 / 500000000000000000) (1018106270157175527 / 1000000000000000000) (neb x (1/2+√23*x)) := by
    convert (lowGroupedE12W_hz63 hx hc) using 1 <;>
      norm_num [neb] <;> ring

theorem lowGroupedE12W_hz65 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B (154153329719927993 / 250000000000000000) (123419846695783487 / 200000000000000000) (√(((kdot ((729879757 / 1000000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE12W_hz57 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE12W_hz66 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B (154153329719927993 / 250000000000000000) (613554270865641 / 976562500000000) ((√(((kdot ((729879757 / 1000000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) := badd (lowGroupedE12W_hz65 hx hc) (lowGroupedE12W_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12W_hz67 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B (154153329719927993 / 250000000000000000) (157369632811811141 / 250000000000000000) (((√(((kdot ((729879757 / 1000000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE12W_hz66 hx hc) (lowGroupedE12W_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12W_hz68 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B (872022918299574693 / 1000000000000000000) (890217076112549361 / 1000000000000000000) ((√(2 : ℝ)) * (((√(((kdot ((729879757 / 1000000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE12W_hz4 hx hc) (lowGroupedE12W_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12W_hz69 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B (872022918299574693 / 1000000000000000000) (890217076112549361 / 1000000000000000000) (neb x (kdot (729879757 / 1000000000)/2+√23*x)) := by
    convert (lowGroupedE12W_hz68 hx hc) using 1 <;>
      norm_num [neb] <;> ring

theorem lowGroupedE12W_hz70 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B 0 (7905694150420949 / 500000000000000000) ((√(2 : ℝ)) * (√x)) := bmul (lowGroupedE12W_hz4 hx hc) (lowGroupedE12W_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12W_hz71 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B 1 (507905694150420949 / 500000000000000000) (((√(2 : ℝ)) * (√x)) + (1 : ℝ)) := badd (lowGroupedE12W_hz70 hx hc) (bpoint (1 : ℝ)) (by norm_num) (by norm_num)

theorem lowGroupedE12W_hz72 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B 0 (107238052947636089 / 1000000000000000000) ((√(92 : ℝ)) * (√x)) := bmul (lowGroupedE12W_hz3 hx hc) (lowGroupedE12W_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12W_hz73 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B 1 (1123049441248477987 / 1000000000000000000) ((((√(2 : ℝ)) * (√x)) + (1 : ℝ)) + ((√(92 : ℝ)) * (√x))) := badd (lowGroupedE12W_hz71 hx hc) (lowGroupedE12W_hz72 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12W_hz74 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (12408060554915031 / 7812500000000000) ((√(2 : ℝ)) * ((((√(2 : ℝ)) * (√x)) + (1 : ℝ)) + ((√(92 : ℝ)) * (√x)))) := bmul (lowGroupedE12W_hz4 hx hc) (lowGroupedE12W_hz73 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12W_hz75 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (12408060554915031 / 7812500000000000) (np1 x) := by
    convert (lowGroupedE12W_hz74 hx hc) using 1 <;>
      norm_num [np1] <;> ring

theorem lowGroupedE12W_hz76 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B (11005876608998534131 / 1000000000000000000) (11005876608998534133 / 1000000000000000000) ((√(2 : ℝ)) + (√(92 : ℝ))) := badd (lowGroupedE12W_hz4 hx hc) (lowGroupedE12W_hz3 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12W_hz77 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B 0 (1375734576124817 / 1000000000000000000) (((√(2 : ℝ)) + (√(92 : ℝ))) * x) := bmul (lowGroupedE12W_hz76 hx hc) (lowGroupedE12W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12W_hz78 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B 1 (1001375734576124817 / 1000000000000000000) ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x)) := badd (bpoint (1 : ℝ)) (lowGroupedE12W_hz77 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12W_hz79 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (1416159144868876367 / 1000000000000000000) ((√(2 : ℝ)) * ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x))) := bmul (lowGroupedE12W_hz4 hx hc) (lowGroupedE12W_hz78 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12W_hz80 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B (1999999999999999997 / 1000000000000000000) (140574307399437647 / 62500000000000000) (((√(2 : ℝ)) * ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x))) * (np1 x)) := bmul (lowGroupedE12W_hz79 hx hc) (lowGroupedE12W_hz75 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12W_hz81 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B (1999999999999999997 / 1000000000000000000) (140574307399437647 / 62500000000000000) (ntf x (np1 x)) := by
    convert (lowGroupedE12W_hz80 hx hc) using 1 <;>
      norm_num [ntf] <;> ring

theorem lowGroupedE12W_hz82 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (1430024950673936947 / 1000000000000000000) (((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) := badd (lowGroupedE12W_hz70 hx hc) (lowGroupedE12W_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12W_hz83 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (384315750905393259 / 250000000000000000) ((((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) + ((√(92 : ℝ)) * (√x))) := badd (lowGroupedE12W_hz82 hx hc) (lowGroupedE12W_hz72 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12W_hz84 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B (1999999999999999997 / 1000000000000000000) (2174018188656028919 / 1000000000000000000) ((√(2 : ℝ)) * ((((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) + ((√(92 : ℝ)) * (√x)))) := bmul (lowGroupedE12W_hz4 hx hc) (lowGroupedE12W_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12W_hz85 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B (1999999999999999997 / 1000000000000000000) (2174018188656028919 / 1000000000000000000) (nz x) := by
    convert (lowGroupedE12W_hz84 hx hc) using 1 <;>
      norm_num [nz] <;> ring

theorem lowGroupedE12W_hz86 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B (582425601398361011 / 1000000000000000000) (156769389509299241 / 250000000000000000) (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE12W_hz55 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE12W_hz87 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B (582425601398361011 / 500000000000000000) (156769389509299241 / 125000000000000000) ((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) := bmul (bpoint (2 : ℝ)) (lowGroupedE12W_hz86 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12W_hz88 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B 0 (8505173090835039 / 500000000000000000) (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE12W_hz70 hx hc) (lowGroupedE12W_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12W_hz89 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B 0 (21333612689938061 / 1000000000000000000) (((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE12W_hz87 hx hc) (lowGroupedE12W_hz88 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12W_hz90 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B 0 (144675938610129 / 500000000000000000) ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2) := bsq (lowGroupedE12W_hz88 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE12W_hz91 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B 0 (21622964567158319 / 1000000000000000000) ((((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) + ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2)) := badd (lowGroupedE12W_hz89 hx hc) (lowGroupedE12W_hz90 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12W_hz92 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B 0 (21622964567158319 / 500000000000000000) ((2 : ℝ) * ((((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) + ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2))) := bmul (bpoint (2 : ℝ)) (lowGroupedE12W_hz91 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12W_hz93 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B 0 (21622964567158319 / 500000000000000000) (nrad x (kdot (nc1 x c)/2+√23*x)) := by
    convert (lowGroupedE12W_hz92 hx hc) using 1 <;>
      norm_num [nrad] <;> ring

theorem lowGroupedE12W_hz94 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B (999999999999999997 / 250000000000000000) (5058850790612887039 / 1000000000000000000) ((ntf x (np1 x))^2) := bsq (lowGroupedE12W_hz81 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE12W_hz95 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B 0 (632356348826611 / 1000000000000000000) (((ntf x (np1 x))^2) * x) := bmul (lowGroupedE12W_hz94 hx hc) (lowGroupedE12W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12W_hz96 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B (1999999999999999997 / 500000000000000000) (140574307399437647 / 31250000000000000) ((2 : ℝ) * (ntf x (np1 x))) := bmul (bpoint (2 : ℝ)) (lowGroupedE12W_hz81 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12W_hz97 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B (999999999999999997 / 125000000000000000) (611222202288202473 / 62500000000000000) (((2 : ℝ) * (ntf x (np1 x))) * (nz x)) := bmul (lowGroupedE12W_hz96 hx hc) (lowGroupedE12W_hz85 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12W_hz98 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B (199999999999999999 / 25000000000000000) (1991325301148468661 / 200000000000000000) ((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) := bmul (lowGroupedE12W_hz97 hx hc) (lowGroupedE12W_hz64 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12W_hz99 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B 0 (1244578313217793 / 1000000000000000000) (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x) := bmul (lowGroupedE12W_hz98 hx hc) (lowGroupedE12W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12W_hz100 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B 0 (469233665511101 / 250000000000000000) ((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) := badd (lowGroupedE12W_hz95 hx hc) (lowGroupedE12W_hz99 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12W_hz101 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B (249999999999999999 / 250000000000000000) (6478377358333473 / 6250000000000000) ((neb x (1/2+√23*x))^2) := bsq (lowGroupedE12W_hz64 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE12W_hz102 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B 0 (700408620359627 / 15625000000000000) ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2)) := bmul (lowGroupedE12W_hz93 hx hc) (lowGroupedE12W_hz101 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12W_hz103 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B 0 (11675771591265133 / 250000000000000000) (((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) + ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2))) := badd (lowGroupedE12W_hz100 hx hc) (lowGroupedE12W_hz102 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12W_hz104 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B (42402447645530313 / 62500000000000000) (196613131896947063 / 250000000000000000) ((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bmul (bpoint (2 : ℝ)) (lowGroupedE12W_hz55 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12W_hz105 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B (760423970039706719 / 1000000000000000000) (792486442602376503 / 1000000000000000000) ((neb x (kdot (729879757 / 1000000000)/2+√23*x))^2) := bsq (lowGroupedE12W_hz69 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE12W_hz106 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B (1999999999999999997 / 1000000000000000000) (2522480094977037223 / 1000000000000000000) ((np1 x)^2) := bsq (lowGroupedE12W_hz75 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE12W_hz107 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B 0 (31531001187213 / 100000000000000000) (((np1 x)^2) * x) := bmul (lowGroupedE12W_hz106 hx hc) (lowGroupedE12W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12W_hz108 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B (760423970039706719 / 1000000000000000000) (792801752614248633 / 1000000000000000000) (((neb x (kdot (729879757 / 1000000000)/2+√23*x))^2) + (((np1 x)^2) * x)) := badd (lowGroupedE12W_hz105 hx hc) (lowGroupedE12W_hz107 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12W_hz109 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B (515901401248239607 / 1000000000000000000) (2494003768878017 / 4000000000000000) (((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) * (((neb x (kdot (729879757 / 1000000000)/2+√23*x))^2) + (((np1 x)^2) * x))) := bmul (lowGroupedE12W_hz104 hx hc) (lowGroupedE12W_hz108 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12W_hz110 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B (515901401248239607 / 1000000000000000000) (335102014292282391 / 500000000000000000) ((((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) + ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2))) + (((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) * (((neb x (kdot (729879757 / 1000000000)/2+√23*x))^2) + (((np1 x)^2) * x)))) := badd (lowGroupedE12W_hz103 hx hc) (lowGroupedE12W_hz109 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12W_hz111 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) : B (515901401248239607 / 1000000000000000000) (335102014292282391 / 500000000000000000) (ne x (kdot (nc1 x c)/2+√23*x) (neb x (1/2+√23*x)) (neb x (kdot (729879757 / 1000000000)/2+√23*x)^2) (np1 x)) := by
    convert (lowGroupedE12W_hz110 hx hc) using 1 <;>
      norm_num [ne] <;> ring

theorem lowGroupedE12W {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (95039643 / 250000000) (729879757 / 1000000000) c) :
    ne x (kdot (nc1 x c)/2+√23*x) (neb x (1/2+√23*x))
      (neb x (kdot (729879757 / 1000000000)/2+√23*x)^2) (np1 x) ≤ (670204029 / 1000000000) :=
  (lowGroupedE12W_hz111 hx hc).2.trans (by norm_num)

theorem lowGroupedE12C_hz0 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B 0 (1 / 8000) x := hx

theorem lowGroupedE12C_hz1 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B (455396707 / 1000000000) (622385613 / 1000000000) c := hc

theorem lowGroupedE12C_hz2 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B (6782329983125268139 / 500000000000000000) (13564659966250536279 / 1000000000000000000) (√(184 : ℝ)) := bsqrt (bpoint (184 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE12C_hz3 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE12C_hz4 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (1414213562373095049 / 1000000000000000000) (√(2 : ℝ)) := bsqrt (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE12C_hz5 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B 0 (847791247890659 / 500000000000000000) ((√(184 : ℝ)) * x) := bmul (lowGroupedE12C_hz2 hx hc) (lowGroupedE12C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12C_hz6 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B 1 (500847791247890659 / 500000000000000000) ((1 : ℝ) + ((√(184 : ℝ)) * x)) := badd (bpoint (1 : ℝ)) (lowGroupedE12C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12C_hz7 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B 1 (500847791247890659 / 500000000000000000) (nap x) := by
    convert (lowGroupedE12C_hz6 hx hc) using 1 <;>
      norm_num [nap] <;> ring

theorem lowGroupedE12C_hz8 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B 0 (1 / 64000000) (x^2) := bsq (lowGroupedE12C_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE12C_hz9 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B 0 (1 / 32000000) ((2 : ℝ) * (x^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE12C_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12C_hz10 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B (31999999 / 32000000) 1 ((1 : ℝ) - ((2 : ℝ) * (x^2))) := bsub (bpoint (1 : ℝ)) (lowGroupedE12C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12C_hz11 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B (999999984374999877 / 1000000000000000000) 1 (√((1 : ℝ) - ((2 : ℝ) * (x^2)))) := bsqrt (lowGroupedE12C_hz10 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE12C_hz12 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B (998304401879218559 / 1000000000000000000) 1 ((√((1 : ℝ) - ((2 : ℝ) * (x^2)))) - ((√(184 : ℝ)) * x)) := bsub (lowGroupedE12C_hz11 hx hc) (lowGroupedE12C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12C_hz13 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B (998304401879218559 / 1000000000000000000) 1 (nam x) := by
    convert (lowGroupedE12C_hz12 hx hc) using 1 <;>
      norm_num [nam] <;> ring

theorem lowGroupedE12C_hz14 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B (325251283219208941 / 500000000000000000) (650502566439320777 / 1000000000000000000) (kdot ((455396707 / 1000000000))) := by
    constructor
    · apply bkdot_lower (q := (12234308661756581 / 20000000000000000)) (a := (274494642431388307 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (611715433087829049 / 1000000000000000000)) (a := (548989284861358351 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE12C_hz15 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B (207386160746443849 / 1000000000000000000) (207386160746443849 / 1000000000000000000) (((455396707 / 1000000000) : ℝ)^2) := bsq (bpoint ((455396707 / 1000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE12C_hz16 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B (792613839253556151 / 1000000000000000000) (792613839253556151 / 1000000000000000000) ((1 : ℝ) - (((455396707 / 1000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowGroupedE12C_hz15 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12C_hz17 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B (22257215673427631 / 25000000000000000) (890288626937105241 / 1000000000000000000) (√((1 : ℝ) - (((455396707 / 1000000000) : ℝ)^2))) := bsqrt (lowGroupedE12C_hz16 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE12C_hz18 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B (141693835755536621 / 500000000000000000) (70846917877768311 / 250000000000000000) ((√((1 : ℝ) - (((455396707 / 1000000000) : ℝ)^2))) / Real.pi) := bdiv (lowGroupedE12C_hz17 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE12C_hz19 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B (296236726651104221 / 1000000000000000000) (148118363325757699 / 500000000000000000) (((455396707 / 1000000000) : ℝ) * (kdot ((455396707 / 1000000000)))) := bmul (bpoint ((455396707 / 1000000000) : ℝ)) (lowGroupedE12C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12C_hz20 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B (579624398162177463 / 1000000000000000000) (289812199081294321 / 500000000000000000) (((√((1 : ℝ) - (((455396707 / 1000000000) : ℝ)^2))) / Real.pi) + (((455396707 / 1000000000) : ℝ) * (kdot ((455396707 / 1000000000))))) := badd (lowGroupedE12C_hz18 hx hc) (lowGroupedE12C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12C_hz21 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B (579624398162177463 / 1000000000000000000) (289812199081294321 / 500000000000000000) (kappa ((455396707 / 1000000000))) := by rw [kappa_eq]; exact (lowGroupedE12C_hz20 hx hc)

theorem lowGroupedE12C_hz22 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B (71383641459931043 / 100000000000000000) (17845910364982761 / 25000000000000000) (kdot ((622385613 / 1000000000))) := by
    constructor
    · apply bkdot_lower (q := (482444348158260921 / 1000000000000000000)) (a := (5618808860123261 / 12500000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (12061108703956523 / 25000000000000000)) (a := (224752354404930433 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE12C_hz23 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B (387363851269385769 / 1000000000000000000) (387363851269385769 / 1000000000000000000) (((622385613 / 1000000000) : ℝ)^2) := bsq (bpoint ((622385613 / 1000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE12C_hz24 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B (612636148730614231 / 1000000000000000000) (612636148730614231 / 1000000000000000000) ((1 : ℝ) - (((622385613 / 1000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowGroupedE12C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12C_hz25 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B (156542153905025113 / 200000000000000000) (391355384762562783 / 500000000000000000) (√((1 : ℝ) - (((622385613 / 1000000000) : ℝ)^2))) := bsqrt (lowGroupedE12C_hz24 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE12C_hz26 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B (24914457596236993 / 100000000000000000) (62286143990592483 / 250000000000000000) ((√((1 : ℝ) - (((622385613 / 1000000000) : ℝ)^2))) / Real.pi) := bdiv (lowGroupedE12C_hz25 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE12C_hz27 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B (444281514482113971 / 1000000000000000000) (222140757241056989 / 500000000000000000) (((622385613 / 1000000000) : ℝ) * (kdot ((622385613 / 1000000000)))) := bmul (bpoint ((622385613 / 1000000000) : ℝ)) (lowGroupedE12C_hz22 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12C_hz28 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B (693426090444483901 / 1000000000000000000) (69342609044448391 / 100000000000000000) (((√((1 : ℝ) - (((622385613 / 1000000000) : ℝ)^2))) / Real.pi) + (((622385613 / 1000000000) : ℝ) * (kdot ((622385613 / 1000000000))))) := badd (lowGroupedE12C_hz26 hx hc) (lowGroupedE12C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12C_hz29 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B (693426090444483901 / 1000000000000000000) (69342609044448391 / 100000000000000000) (kappa ((622385613 / 1000000000))) := by rw [kappa_eq]; exact (lowGroupedE12C_hz28 hx hc)

theorem lowGroupedE12C_hz30 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B (579624398162177463 / 1000000000000000000) (69342609044448391 / 100000000000000000) (kappa c) := bkappa (lowGroupedE12C_hz1 hx hc) (by norm_num) (by norm_num) (lowGroupedE12C_hz21 hx hc).1 (lowGroupedE12C_hz29 hx hc).2

theorem lowGroupedE12C_hz31 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B (30657390955551609 / 100000000000000000) (420375601837822537 / 1000000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (lowGroupedE12C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12C_hz32 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B (30657390955551609 / 50000000000000000) (420375601837822537 / 500000000000000000) ((2 : ℝ) * ((1 : ℝ) - (kappa c))) := bmul (bpoint (2 : ℝ)) (lowGroupedE12C_hz31 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12C_hz33 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B 0 (1 / 8000000) ((8 : ℝ) * (x^2)) := bmul (bpoint (8 : ℝ)) (lowGroupedE12C_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12C_hz34 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B (30657384705551609 / 50000000000000000) (420375601837822537 / 500000000000000000) (((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2))) := bsub (lowGroupedE12C_hz32 hx hc) (lowGroupedE12C_hz33 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12C_hz35 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B (783037479378242903 / 1000000000000000000) (229231215652946833 / 250000000000000000) (√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) := bsqrt (lowGroupedE12C_hz34 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE12C_hz36 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B (6782329983125268139 / 250000000000000000) (13564659966250536279 / 500000000000000000) ((2 : ℝ) * (√(184 : ℝ))) := bmul (bpoint (2 : ℝ)) (lowGroupedE12C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12C_hz37 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B 0 (678232998312527 / 200000000000000000) (((2 : ℝ) * (√(184 : ℝ))) * x) := bmul (lowGroupedE12C_hz36 hx hc) (lowGroupedE12C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12C_hz38 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B (194911578596670067 / 250000000000000000) (229231215652946833 / 250000000000000000) ((√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) - (((2 : ℝ) * (√(184 : ℝ))) * x)) := bsub (lowGroupedE12C_hz35 hx hc) (lowGroupedE12C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12C_hz39 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B (194911578596670067 / 250000000000000000) (229231215652946833 / 250000000000000000) (ndm x c) := by
    convert (lowGroupedE12C_hz38 hx hc) using 1 <;>
      norm_num [ndm] <;> ring

theorem lowGroupedE12C_hz40 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B 1 (1003394039991562637 / 1000000000000000000) ((nap x)^2) := bsq (lowGroupedE12C_hz7 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE12C_hz41 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B 2 (1003394039991562637 / 500000000000000000) ((2 : ℝ) * ((nap x)^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE12C_hz40 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12C_hz42 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B (607848375536734287 / 1000000000000000000) (33630048147025803 / 40000000000000000) ((ndm x c)^2) := bsq (lowGroupedE12C_hz39 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE12C_hz43 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B (46369951852974197 / 40000000000000000) (1398939704446390987 / 1000000000000000000) (((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) := bsub (lowGroupedE12C_hz41 hx hc) (lowGroupedE12C_hz42 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12C_hz44 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B (199322335762284863 / 200000000000000000) 1 ((nam x)^2) := bsq (lowGroupedE12C_hz13 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE12C_hz45 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B (199322335762284863 / 100000000000000000) 2 ((2 : ℝ) * ((nam x)^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE12C_hz44 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12C_hz46 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B (289812199081088731 / 500000000000000000) (701847938464252083 / 1000000000000000000) ((((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) / ((2 : ℝ) * ((nam x)^2))) := bdiv (lowGroupedE12C_hz43 hx hc) (lowGroupedE12C_hz45 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE12C_hz47 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B (289812199081088731 / 500000000000000000) (701847938464252083 / 1000000000000000000) (nc1 x c) := by
    convert (lowGroupedE12C_hz46 hx hc) using 1 <;>
      norm_num [nc1] <;> ring

theorem lowGroupedE12C_hz48 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B (139360143491564409 / 200000000000000000) (696800717457822261 / 1000000000000000000) (kdot ((289812199081088731 / 500000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (515871855356500769 / 1000000000000000000)) (a := (95252863860820231 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (16120995479890649 / 31250000000000000)) (a := (238132159652050409 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE12C_hz49 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B (747641405711918001 / 1000000000000000000) (747641405711918003 / 1000000000000000000) (kdot ((701847938464252083 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (418560780193985073 / 1000000000000000000)) (a := (198201976471421391 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (26160048762124067 / 62500000000000000)) (a := (19820197647142139 / 50000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE12C_hz50 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B (139360143491564409 / 200000000000000000) (747641405711918003 / 1000000000000000000) (kdot (nc1 x c)) := bkdot (lowGroupedE12C_hz47 hx hc) (lowGroupedE12C_hz48 hx hc).1 (lowGroupedE12C_hz49 hx hc).2

theorem lowGroupedE12C_hz51 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE12C_hz52 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B 0 (59947894041409 / 100000000000000000) ((√(23 : ℝ)) * x) := bmul (lowGroupedE12C_hz51 hx hc) (lowGroupedE12C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12C_hz53 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B (1 / 2) (50059947894041409 / 100000000000000000) (((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)) := badd (bpoint ((1 / 2) : ℝ)) (lowGroupedE12C_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12C_hz54 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B (174200179364455511 / 500000000000000000) (186910351427979501 / 500000000000000000) ((kdot (nc1 x c)) / (2 : ℝ)) := bdiv (lowGroupedE12C_hz50 hx hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE12C_hz55 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B (174200179364455511 / 500000000000000000) (93605045449093273 / 250000000000000000) (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)) := badd (lowGroupedE12C_hz54 hx hc) (lowGroupedE12C_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12C_hz56 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B (71383641459931043 / 200000000000000000) (17845910364982761 / 50000000000000000) ((kdot ((622385613 / 1000000000))) / (2 : ℝ)) := bdiv (lowGroupedE12C_hz22 hx hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE12C_hz57 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B (71383641459931043 / 200000000000000000) (35751768624006931 / 100000000000000000) (((kdot ((622385613 / 1000000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x)) := badd (lowGroupedE12C_hz56 hx hc) (lowGroupedE12C_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12C_hz58 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B (176776695296636881 / 250000000000000000) (353765274914177413 / 500000000000000000) (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE12C_hz53 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE12C_hz59 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGroupedE12C_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE12C_hz60 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B (176776695296636881 / 250000000000000000) (28748435588634151 / 40000000000000000) ((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) := badd (lowGroupedE12C_hz58 hx hc) (lowGroupedE12C_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12C_hz61 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B 0 (59947894041409 / 50000000000000000) ((√(92 : ℝ)) * x) := bmul (lowGroupedE12C_hz3 hx hc) (lowGroupedE12C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12C_hz62 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B (176776695296636881 / 250000000000000000) (143981969519336391 / 200000000000000000) (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE12C_hz60 hx hc) (lowGroupedE12C_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12C_hz63 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B (499999999999999999 / 500000000000000000) (1018106270157175527 / 1000000000000000000) ((√(2 : ℝ)) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE12C_hz4 hx hc) (lowGroupedE12C_hz62 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12C_hz64 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B (499999999999999999 / 500000000000000000) (1018106270157175527 / 1000000000000000000) (neb x (1/2+√23*x)) := by
    convert (lowGroupedE12C_hz63 hx hc) using 1 <;>
      norm_num [neb] <;> ring

theorem lowGroupedE12C_hz65 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B (597426319557194613 / 1000000000000000000) (298963913474548509 / 500000000000000000) (√(((kdot ((622385613 / 1000000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE12C_hz57 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE12C_hz66 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B (597426319557194613 / 1000000000000000000) (609108166836595967 / 1000000000000000000) ((√(((kdot ((622385613 / 1000000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) := badd (lowGroupedE12C_hz65 hx hc) (lowGroupedE12C_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12C_hz67 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B (597426319557194613 / 1000000000000000000) (610307124717424147 / 1000000000000000000) (((√(((kdot ((622385613 / 1000000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE12C_hz66 hx hc) (lowGroupedE12C_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12C_hz68 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B (844888403636427257 / 1000000000000000000) (863104612988309213 / 1000000000000000000) ((√(2 : ℝ)) * (((√(((kdot ((622385613 / 1000000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE12C_hz4 hx hc) (lowGroupedE12C_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12C_hz69 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B (844888403636427257 / 1000000000000000000) (863104612988309213 / 1000000000000000000) (neb x (kdot (622385613 / 1000000000)/2+√23*x)) := by
    convert (lowGroupedE12C_hz68 hx hc) using 1 <;>
      norm_num [neb] <;> ring

theorem lowGroupedE12C_hz70 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B 0 (7905694150420949 / 500000000000000000) ((√(2 : ℝ)) * (√x)) := bmul (lowGroupedE12C_hz4 hx hc) (lowGroupedE12C_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12C_hz71 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B 1 (507905694150420949 / 500000000000000000) (((√(2 : ℝ)) * (√x)) + (1 : ℝ)) := badd (lowGroupedE12C_hz70 hx hc) (bpoint (1 : ℝ)) (by norm_num) (by norm_num)

theorem lowGroupedE12C_hz72 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B 0 (107238052947636089 / 1000000000000000000) ((√(92 : ℝ)) * (√x)) := bmul (lowGroupedE12C_hz3 hx hc) (lowGroupedE12C_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12C_hz73 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B 1 (1123049441248477987 / 1000000000000000000) ((((√(2 : ℝ)) * (√x)) + (1 : ℝ)) + ((√(92 : ℝ)) * (√x))) := badd (lowGroupedE12C_hz71 hx hc) (lowGroupedE12C_hz72 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12C_hz74 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (12408060554915031 / 7812500000000000) ((√(2 : ℝ)) * ((((√(2 : ℝ)) * (√x)) + (1 : ℝ)) + ((√(92 : ℝ)) * (√x)))) := bmul (lowGroupedE12C_hz4 hx hc) (lowGroupedE12C_hz73 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12C_hz75 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (12408060554915031 / 7812500000000000) (np1 x) := by
    convert (lowGroupedE12C_hz74 hx hc) using 1 <;>
      norm_num [np1] <;> ring

theorem lowGroupedE12C_hz76 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B (11005876608998534131 / 1000000000000000000) (11005876608998534133 / 1000000000000000000) ((√(2 : ℝ)) + (√(92 : ℝ))) := badd (lowGroupedE12C_hz4 hx hc) (lowGroupedE12C_hz3 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12C_hz77 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B 0 (1375734576124817 / 1000000000000000000) (((√(2 : ℝ)) + (√(92 : ℝ))) * x) := bmul (lowGroupedE12C_hz76 hx hc) (lowGroupedE12C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12C_hz78 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B 1 (1001375734576124817 / 1000000000000000000) ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x)) := badd (bpoint (1 : ℝ)) (lowGroupedE12C_hz77 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12C_hz79 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (1416159144868876367 / 1000000000000000000) ((√(2 : ℝ)) * ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x))) := bmul (lowGroupedE12C_hz4 hx hc) (lowGroupedE12C_hz78 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12C_hz80 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B (1999999999999999997 / 1000000000000000000) (140574307399437647 / 62500000000000000) (((√(2 : ℝ)) * ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x))) * (np1 x)) := bmul (lowGroupedE12C_hz79 hx hc) (lowGroupedE12C_hz75 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12C_hz81 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B (1999999999999999997 / 1000000000000000000) (140574307399437647 / 62500000000000000) (ntf x (np1 x)) := by
    convert (lowGroupedE12C_hz80 hx hc) using 1 <;>
      norm_num [ntf] <;> ring

theorem lowGroupedE12C_hz82 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (1430024950673936947 / 1000000000000000000) (((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) := badd (lowGroupedE12C_hz70 hx hc) (lowGroupedE12C_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12C_hz83 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (384315750905393259 / 250000000000000000) ((((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) + ((√(92 : ℝ)) * (√x))) := badd (lowGroupedE12C_hz82 hx hc) (lowGroupedE12C_hz72 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12C_hz84 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B (1999999999999999997 / 1000000000000000000) (2174018188656028919 / 1000000000000000000) ((√(2 : ℝ)) * ((((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) + ((√(92 : ℝ)) * (√x)))) := bmul (lowGroupedE12C_hz4 hx hc) (lowGroupedE12C_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12C_hz85 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B (1999999999999999997 / 1000000000000000000) (2174018188656028919 / 1000000000000000000) (nz x) := by
    convert (lowGroupedE12C_hz84 hx hc) using 1 <;>
      norm_num [nz] <;> ring

theorem lowGroupedE12C_hz86 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B (295127243205753127 / 500000000000000000) (611898832975168447 / 1000000000000000000) (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE12C_hz55 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE12C_hz87 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B (295127243205753127 / 250000000000000000) (611898832975168447 / 500000000000000000) ((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) := bmul (bpoint (2 : ℝ)) (lowGroupedE12C_hz86 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12C_hz88 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B 0 (8505173090835039 / 500000000000000000) (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE12C_hz70 hx hc) (lowGroupedE12C_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12C_hz89 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B 0 (20817221954135067 / 1000000000000000000) (((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE12C_hz87 hx hc) (lowGroupedE12C_hz88 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12C_hz90 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B 0 (144675938610129 / 500000000000000000) ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2) := bsq (lowGroupedE12C_hz88 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE12C_hz91 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B 0 (844262953254213 / 40000000000000000) ((((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) + ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2)) := badd (lowGroupedE12C_hz89 hx hc) (lowGroupedE12C_hz90 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12C_hz92 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B 0 (844262953254213 / 20000000000000000) ((2 : ℝ) * ((((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) + ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2))) := bmul (bpoint (2 : ℝ)) (lowGroupedE12C_hz91 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12C_hz93 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B 0 (844262953254213 / 20000000000000000) (nrad x (kdot (nc1 x c)/2+√23*x)) := by
    convert (lowGroupedE12C_hz92 hx hc) using 1 <;>
      norm_num [nrad] <;> ring

theorem lowGroupedE12C_hz94 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B (999999999999999997 / 250000000000000000) (5058850790612887039 / 1000000000000000000) ((ntf x (np1 x))^2) := bsq (lowGroupedE12C_hz81 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE12C_hz95 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B 0 (632356348826611 / 1000000000000000000) (((ntf x (np1 x))^2) * x) := bmul (lowGroupedE12C_hz94 hx hc) (lowGroupedE12C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12C_hz96 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B (1999999999999999997 / 500000000000000000) (140574307399437647 / 31250000000000000) ((2 : ℝ) * (ntf x (np1 x))) := bmul (bpoint (2 : ℝ)) (lowGroupedE12C_hz81 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12C_hz97 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B (999999999999999997 / 125000000000000000) (611222202288202473 / 62500000000000000) (((2 : ℝ) * (ntf x (np1 x))) * (nz x)) := bmul (lowGroupedE12C_hz96 hx hc) (lowGroupedE12C_hz85 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12C_hz98 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B (199999999999999999 / 25000000000000000) (1991325301148468661 / 200000000000000000) ((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) := bmul (lowGroupedE12C_hz97 hx hc) (lowGroupedE12C_hz64 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12C_hz99 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B 0 (1244578313217793 / 1000000000000000000) (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x) := bmul (lowGroupedE12C_hz98 hx hc) (lowGroupedE12C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12C_hz100 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B 0 (469233665511101 / 250000000000000000) ((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) := badd (lowGroupedE12C_hz95 hx hc) (lowGroupedE12C_hz99 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12C_hz101 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B (249999999999999999 / 250000000000000000) (6478377358333473 / 6250000000000000) ((neb x (1/2+√23*x))^2) := bsq (lowGroupedE12C_hz64 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE12C_hz102 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B 0 (43755632006734759 / 1000000000000000000) ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2)) := bmul (lowGroupedE12C_hz93 hx hc) (lowGroupedE12C_hz101 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12C_hz103 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B 0 (45632566668779163 / 1000000000000000000) (((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) + ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2))) := badd (lowGroupedE12C_hz100 hx hc) (lowGroupedE12C_hz102 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12C_hz104 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B (174200179364455511 / 250000000000000000) (93605045449093273 / 125000000000000000) ((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bmul (bpoint (2 : ℝ)) (lowGroupedE12C_hz55 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12C_hz105 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B (356918207299655213 / 500000000000000000) (29797982918467961 / 40000000000000000) ((neb x (kdot (622385613 / 1000000000)/2+√23*x))^2) := bsq (lowGroupedE12C_hz69 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE12C_hz106 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B (1999999999999999997 / 1000000000000000000) (2522480094977037223 / 1000000000000000000) ((np1 x)^2) := bsq (lowGroupedE12C_hz75 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE12C_hz107 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B 0 (31531001187213 / 100000000000000000) (((np1 x)^2) * x) := bmul (lowGroupedE12C_hz106 hx hc) (lowGroupedE12C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12C_hz108 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B (356918207299655213 / 500000000000000000) (149052976594714231 / 200000000000000000) (((neb x (kdot (622385613 / 1000000000)/2+√23*x))^2) + (((np1 x)^2) * x)) := badd (lowGroupedE12C_hz105 hx hc) (lowGroupedE12C_hz107 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12C_hz109 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B (248700862920159409 / 500000000000000000) (558084425938834459 / 1000000000000000000) (((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) * (((neb x (kdot (622385613 / 1000000000)/2+√23*x))^2) + (((np1 x)^2) * x))) := bmul (lowGroupedE12C_hz104 hx hc) (lowGroupedE12C_hz108 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12C_hz110 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B (248700862920159409 / 500000000000000000) (301858496303806811 / 500000000000000000) ((((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) + ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2))) + (((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) * (((neb x (kdot (622385613 / 1000000000)/2+√23*x))^2) + (((np1 x)^2) * x)))) := badd (lowGroupedE12C_hz103 hx hc) (lowGroupedE12C_hz109 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE12C_hz111 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) : B (248700862920159409 / 500000000000000000) (301858496303806811 / 500000000000000000) (ne x (kdot (nc1 x c)/2+√23*x) (neb x (1/2+√23*x)) (neb x (kdot (622385613 / 1000000000)/2+√23*x)^2) (np1 x)) := by
    convert (lowGroupedE12C_hz110 hx hc) using 1 <;>
      norm_num [ne] <;> ring

theorem lowGroupedE12C {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (455396707 / 1000000000) (622385613 / 1000000000) c) :
    ne x (kdot (nc1 x c)/2+√23*x) (neb x (1/2+√23*x))
      (neb x (kdot (622385613 / 1000000000)/2+√23*x)^2) (np1 x) ≤ (603716993 / 1000000000) :=
  (lowGroupedE12C_hz111 hx hc).2.trans (by norm_num)

theorem lowGroupedE14W_hz0 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B 0 (1 / 8000) x := hx

theorem lowGroupedE14W_hz1 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B (5923997 / 15625000) (728962483 / 1000000000) c := hc

theorem lowGroupedE14W_hz2 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B (6782329983125268139 / 500000000000000000) (13564659966250536279 / 1000000000000000000) (√(184 : ℝ)) := bsqrt (bpoint (184 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE14W_hz3 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE14W_hz4 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (1414213562373095049 / 1000000000000000000) (√(2 : ℝ)) := bsqrt (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE14W_hz5 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B 0 (847791247890659 / 500000000000000000) ((√(184 : ℝ)) * x) := bmul (lowGroupedE14W_hz2 hx hc) (lowGroupedE14W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14W_hz6 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B 1 (500847791247890659 / 500000000000000000) ((1 : ℝ) + ((√(184 : ℝ)) * x)) := badd (bpoint (1 : ℝ)) (lowGroupedE14W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14W_hz7 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B 1 (500847791247890659 / 500000000000000000) (nap x) := by
    convert (lowGroupedE14W_hz6 hx hc) using 1 <;>
      norm_num [nap] <;> ring

theorem lowGroupedE14W_hz8 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B 0 (1 / 64000000) (x^2) := bsq (lowGroupedE14W_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE14W_hz9 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B 0 (1 / 32000000) ((2 : ℝ) * (x^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE14W_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14W_hz10 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B (31999999 / 32000000) 1 ((1 : ℝ) - ((2 : ℝ) * (x^2))) := bsub (bpoint (1 : ℝ)) (lowGroupedE14W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14W_hz11 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B (999999984374999877 / 1000000000000000000) 1 (√((1 : ℝ) - ((2 : ℝ) * (x^2)))) := bsqrt (lowGroupedE14W_hz10 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE14W_hz12 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B (998304401879218559 / 1000000000000000000) 1 ((√((1 : ℝ) - ((2 : ℝ) * (x^2)))) - ((√(184 : ℝ)) * x)) := bsub (lowGroupedE14W_hz11 hx hc) (lowGroupedE14W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14W_hz13 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B (998304401879218559 / 1000000000000000000) 1 (nam x) := by
    convert (lowGroupedE14W_hz12 hx hc) using 1 <;>
      norm_num [nam] <;> ring

theorem lowGroupedE14W_hz14 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B (155944670676018837 / 250000000000000000) (311889341393890879 / 500000000000000000) (kdot ((5923997 / 15625000))) := by
    constructor
    · apply bkdot_lower (q := (670957155905340623 / 1000000000000000000)) (a := (2363868253081503 / 4000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (335478577952670311 / 500000000000000000)) (a := (590967063138890031 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE14W_hz15 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B (35093740456009 / 244140625000000) (35093740456009 / 244140625000000) (((5923997 / 15625000) : ℝ)^2) := bsq (bpoint ((5923997 / 15625000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE14W_hz16 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B (209046884543991 / 244140625000000) (209046884543991 / 244140625000000) ((1 : ℝ) - (((5923997 / 15625000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowGroupedE14W_hz15 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14W_hz17 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B (92534103934289391 / 100000000000000000) (925341039342893911 / 1000000000000000000) (√((1 : ℝ) - (((5923997 / 15625000) : ℝ)^2))) := bsqrt (lowGroupedE14W_hz16 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE14W_hz18 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B (147272600457213563 / 500000000000000000) (294545200914427127 / 1000000000000000000) ((√((1 : ℝ) - (((5923997 / 15625000) : ℝ)^2))) / Real.pi) := bdiv (lowGroupedE14W_hz17 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE14W_hz19 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B (236496834880185231 / 1000000000000000000) (23649683491192133 / 100000000000000000) (((5923997 / 15625000) : ℝ) * (kdot ((5923997 / 15625000)))) := bmul (bpoint ((5923997 / 15625000) : ℝ)) (lowGroupedE14W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14W_hz20 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B (531042035794612357 / 1000000000000000000) (531042035826348457 / 1000000000000000000) (((√((1 : ℝ) - (((5923997 / 15625000) : ℝ)^2))) / Real.pi) + (((5923997 / 15625000) : ℝ) * (kdot ((5923997 / 15625000))))) := badd (lowGroupedE14W_hz18 hx hc) (lowGroupedE14W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14W_hz21 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B (531042035794612357 / 1000000000000000000) (531042035826348457 / 1000000000000000000) (kappa ((5923997 / 15625000))) := by rw [kappa_eq]; exact (lowGroupedE14W_hz20 hx hc)

theorem lowGroupedE14W_hz22 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B (23749910715570371 / 31250000000000000) (1215995428637203 / 1600000000000000) (kdot ((728962483 / 1000000000))) := by
    constructor
    · apply bkdot_lower (q := (395933200254448323 / 1000000000000000000)) (a := (188497803177853213 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (197966600127224161 / 500000000000000000)) (a := (47124450794463303 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE14W_hz23 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B (531386301621525289 / 1000000000000000000) (531386301621525289 / 1000000000000000000) (((728962483 / 1000000000) : ℝ)^2) := bsq (bpoint ((728962483 / 1000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE14W_hz24 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B (468613698378474711 / 1000000000000000000) (468613698378474711 / 1000000000000000000) ((1 : ℝ) - (((728962483 / 1000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowGroupedE14W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14W_hz25 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B (342276824507033601 / 500000000000000000) (684553649014067203 / 1000000000000000000) (√((1 : ℝ) - (((728962483 / 1000000000) : ℝ)^2))) := bsqrt (lowGroupedE14W_hz24 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE14W_hz26 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B (108950097052183159 / 500000000000000000) (217900194104366319 / 1000000000000000000) ((√((1 : ℝ) - (((728962483 / 1000000000) : ℝ)^2))) / Real.pi) := bdiv (lowGroupedE14W_hz25 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE14W_hz27 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B (1108018808720031 / 2000000000000000) (34625587772500969 / 62500000000000000) (((728962483 / 1000000000) : ℝ) * (kdot ((728962483 / 1000000000)))) := bmul (bpoint ((728962483 / 1000000000) : ℝ)) (lowGroupedE14W_hz22 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14W_hz28 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B (385954799232190909 / 500000000000000000) (771909598464381823 / 1000000000000000000) (((√((1 : ℝ) - (((728962483 / 1000000000) : ℝ)^2))) / Real.pi) + (((728962483 / 1000000000) : ℝ) * (kdot ((728962483 / 1000000000))))) := badd (lowGroupedE14W_hz26 hx hc) (lowGroupedE14W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14W_hz29 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B (385954799232190909 / 500000000000000000) (771909598464381823 / 1000000000000000000) (kappa ((728962483 / 1000000000))) := by rw [kappa_eq]; exact (lowGroupedE14W_hz28 hx hc)

theorem lowGroupedE14W_hz30 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B (531042035794612357 / 1000000000000000000) (771909598464381823 / 1000000000000000000) (kappa c) := bkappa (lowGroupedE14W_hz1 hx hc) (by norm_num) (by norm_num) (lowGroupedE14W_hz21 hx hc).1 (lowGroupedE14W_hz29 hx hc).2

theorem lowGroupedE14W_hz31 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B (228090401535618177 / 1000000000000000000) (468957964205387643 / 1000000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (lowGroupedE14W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14W_hz32 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B (228090401535618177 / 500000000000000000) (468957964205387643 / 500000000000000000) ((2 : ℝ) * ((1 : ℝ) - (kappa c))) := bmul (bpoint (2 : ℝ)) (lowGroupedE14W_hz31 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14W_hz33 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B 0 (1 / 8000000) ((8 : ℝ) * (x^2)) := bmul (bpoint (8 : ℝ)) (lowGroupedE14W_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14W_hz34 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B (228090339035618177 / 500000000000000000) (468957964205387643 / 500000000000000000) (((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2))) := bsub (lowGroupedE14W_hz32 hx hc) (lowGroupedE14W_hz33 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14W_hz35 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B (675411487962143233 / 1000000000000000000) (968460597242229203 / 1000000000000000000) (√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) := bsqrt (lowGroupedE14W_hz34 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE14W_hz36 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B (6782329983125268139 / 250000000000000000) (13564659966250536279 / 500000000000000000) ((2 : ℝ) * (√(184 : ℝ))) := bmul (bpoint (2 : ℝ)) (lowGroupedE14W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14W_hz37 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B 0 (678232998312527 / 200000000000000000) (((2 : ℝ) * (√(184 : ℝ))) * x) := bmul (lowGroupedE14W_hz36 hx hc) (lowGroupedE14W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14W_hz38 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B (336010161485290299 / 500000000000000000) (968460597242229203 / 1000000000000000000) ((√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) - (((2 : ℝ) * (√(184 : ℝ))) * x)) := bsub (lowGroupedE14W_hz35 hx hc) (lowGroupedE14W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14W_hz39 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B (336010161485290299 / 500000000000000000) (968460597242229203 / 1000000000000000000) (ndm x c) := by
    convert (lowGroupedE14W_hz38 hx hc) using 1 <;>
      norm_num [ndm] <;> ring

theorem lowGroupedE14W_hz40 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B 1 (1003394039991562637 / 1000000000000000000) ((nap x)^2) := bsq (lowGroupedE14W_hz7 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE14W_hz41 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B 2 (1003394039991562637 / 500000000000000000) ((2 : ℝ) * ((nap x)^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE14W_hz40 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14W_hz42 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B (7056426788835679 / 15625000000000000) (937915928410775287 / 1000000000000000000) ((ndm x c)^2) := bsq (lowGroupedE14W_hz39 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE14W_hz43 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B (1062084071589224713 / 1000000000000000000) (777588382748820909 / 500000000000000000) (((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) := bsub (lowGroupedE14W_hz41 hx hc) (lowGroupedE14W_hz42 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14W_hz44 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B (199322335762284863 / 200000000000000000) 1 ((nam x)^2) := bsq (lowGroupedE14W_hz13 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE14W_hz45 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B (199322335762284863 / 100000000000000000) 2 ((2 : ℝ) * ((nam x)^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE14W_hz44 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14W_hz46 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B (132760508948653089 / 250000000000000000) (390116029784131049 / 500000000000000000) ((((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) / ((2 : ℝ) * ((nam x)^2))) := bdiv (lowGroupedE14W_hz43 hx hc) (lowGroupedE14W_hz45 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE14W_hz47 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B (132760508948653089 / 250000000000000000) (390116029784131049 / 500000000000000000) (nc1 x c) := by
    convert (lowGroupedE14W_hz46 hx hc) using 1 <;>
      norm_num [nc1] <;> ring

theorem lowGroupedE14W_hz48 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B (678199378096994323 / 1000000000000000000) (678199378097001013 / 1000000000000000000) (kdot ((132760508948653089 / 250000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (553443639362861347 / 1000000000000000000)) (a := (31592702177847167 / 62500000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (276721819681430673 / 500000000000000000)) (a := (126370808711386041 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE14W_hz49 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B (784899041497840271 / 1000000000000000000) (784899041497840273 / 1000000000000000000) (kdot ((390116029784131049 / 500000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (5489893078603547 / 15625000000000000)) (a := (33787979550525399 / 100000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (351353157030627007 / 1000000000000000000)) (a := (84469948876313497 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE14W_hz50 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B (678199378096994323 / 1000000000000000000) (784899041497840273 / 1000000000000000000) (kdot (nc1 x c)) := bkdot (lowGroupedE14W_hz47 hx hc) (lowGroupedE14W_hz48 hx hc).1 (lowGroupedE14W_hz49 hx hc).2

theorem lowGroupedE14W_hz51 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE14W_hz52 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B 0 (59947894041409 / 100000000000000000) ((√(23 : ℝ)) * x) := bmul (lowGroupedE14W_hz51 hx hc) (lowGroupedE14W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14W_hz53 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B (1 / 2) (50059947894041409 / 100000000000000000) (((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)) := badd (bpoint ((1 / 2) : ℝ)) (lowGroupedE14W_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14W_hz54 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B (339099689048497161 / 1000000000000000000) (392449520748920137 / 1000000000000000000) ((kdot (nc1 x c)) / (2 : ℝ)) := bdiv (lowGroupedE14W_hz50 hx hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE14W_hz55 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B (339099689048497161 / 1000000000000000000) (393048999689334227 / 1000000000000000000) (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)) := badd (lowGroupedE14W_hz54 hx hc) (lowGroupedE14W_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14W_hz56 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B (23749910715570371 / 62500000000000000) (189999285724562969 / 500000000000000000) ((kdot ((728962483 / 1000000000))) / (2 : ℝ)) := bdiv (lowGroupedE14W_hz22 hx hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE14W_hz57 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B (23749910715570371 / 62500000000000000) (95149512597385007 / 250000000000000000) (((kdot ((728962483 / 1000000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x)) := badd (lowGroupedE14W_hz56 hx hc) (lowGroupedE14W_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14W_hz58 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B (176776695296636881 / 250000000000000000) (353765274914177413 / 500000000000000000) (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE14W_hz53 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE14W_hz59 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGroupedE14W_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE14W_hz60 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B (176776695296636881 / 250000000000000000) (28748435588634151 / 40000000000000000) ((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) := badd (lowGroupedE14W_hz58 hx hc) (lowGroupedE14W_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14W_hz61 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B 0 (59947894041409 / 50000000000000000) ((√(92 : ℝ)) * x) := bmul (lowGroupedE14W_hz3 hx hc) (lowGroupedE14W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14W_hz62 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B (176776695296636881 / 250000000000000000) (143981969519336391 / 200000000000000000) (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE14W_hz60 hx hc) (lowGroupedE14W_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14W_hz63 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B (499999999999999999 / 500000000000000000) (1018106270157175527 / 1000000000000000000) ((√(2 : ℝ)) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE14W_hz4 hx hc) (lowGroupedE14W_hz62 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14W_hz64 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B (499999999999999999 / 500000000000000000) (1018106270157175527 / 1000000000000000000) (neb x (1/2+√23*x)) := by
    convert (lowGroupedE14W_hz63 hx hc) using 1 <;>
      norm_num [neb] <;> ring

theorem lowGroupedE14W_hz65 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B (308220120794021953 / 500000000000000000) (308463146254759269 / 500000000000000000) (√(((kdot ((728962483 / 1000000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE14W_hz57 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE14W_hz66 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B (308220120794021953 / 500000000000000000) (628106632397017487 / 1000000000000000000) ((√(((kdot ((728962483 / 1000000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) := badd (lowGroupedE14W_hz65 hx hc) (lowGroupedE14W_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14W_hz67 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B (308220120794021953 / 500000000000000000) (629305590277845667 / 1000000000000000000) (((√(((kdot ((728962483 / 1000000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE14W_hz66 hx hc) (lowGroupedE14W_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14W_hz68 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B (87177815004635891 / 100000000000000000) (889972500648135491 / 1000000000000000000) ((√(2 : ℝ)) * (((√(((kdot ((728962483 / 1000000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE14W_hz4 hx hc) (lowGroupedE14W_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14W_hz69 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B (87177815004635891 / 100000000000000000) (889972500648135491 / 1000000000000000000) (neb x (kdot (728962483 / 1000000000)/2+√23*x)) := by
    convert (lowGroupedE14W_hz68 hx hc) using 1 <;>
      norm_num [neb] <;> ring

theorem lowGroupedE14W_hz70 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B 0 (7905694150420949 / 500000000000000000) ((√(2 : ℝ)) * (√x)) := bmul (lowGroupedE14W_hz4 hx hc) (lowGroupedE14W_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14W_hz71 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B 1 (507905694150420949 / 500000000000000000) (((√(2 : ℝ)) * (√x)) + (1 : ℝ)) := badd (lowGroupedE14W_hz70 hx hc) (bpoint (1 : ℝ)) (by norm_num) (by norm_num)

theorem lowGroupedE14W_hz72 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B 0 (107238052947636089 / 1000000000000000000) ((√(92 : ℝ)) * (√x)) := bmul (lowGroupedE14W_hz3 hx hc) (lowGroupedE14W_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14W_hz73 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B 1 (1123049441248477987 / 1000000000000000000) ((((√(2 : ℝ)) * (√x)) + (1 : ℝ)) + ((√(92 : ℝ)) * (√x))) := badd (lowGroupedE14W_hz71 hx hc) (lowGroupedE14W_hz72 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14W_hz74 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (12408060554915031 / 7812500000000000) ((√(2 : ℝ)) * ((((√(2 : ℝ)) * (√x)) + (1 : ℝ)) + ((√(92 : ℝ)) * (√x)))) := bmul (lowGroupedE14W_hz4 hx hc) (lowGroupedE14W_hz73 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14W_hz75 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (12408060554915031 / 7812500000000000) (np1 x) := by
    convert (lowGroupedE14W_hz74 hx hc) using 1 <;>
      norm_num [np1] <;> ring

theorem lowGroupedE14W_hz76 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B (11005876608998534131 / 1000000000000000000) (11005876608998534133 / 1000000000000000000) ((√(2 : ℝ)) + (√(92 : ℝ))) := badd (lowGroupedE14W_hz4 hx hc) (lowGroupedE14W_hz3 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14W_hz77 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B 0 (1375734576124817 / 1000000000000000000) (((√(2 : ℝ)) + (√(92 : ℝ))) * x) := bmul (lowGroupedE14W_hz76 hx hc) (lowGroupedE14W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14W_hz78 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B 1 (1001375734576124817 / 1000000000000000000) ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x)) := badd (bpoint (1 : ℝ)) (lowGroupedE14W_hz77 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14W_hz79 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (1416159144868876367 / 1000000000000000000) ((√(2 : ℝ)) * ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x))) := bmul (lowGroupedE14W_hz4 hx hc) (lowGroupedE14W_hz78 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14W_hz80 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B (1999999999999999997 / 1000000000000000000) (140574307399437647 / 62500000000000000) (((√(2 : ℝ)) * ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x))) * (np1 x)) := bmul (lowGroupedE14W_hz79 hx hc) (lowGroupedE14W_hz75 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14W_hz81 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B (1999999999999999997 / 1000000000000000000) (140574307399437647 / 62500000000000000) (ntf x (np1 x)) := by
    convert (lowGroupedE14W_hz80 hx hc) using 1 <;>
      norm_num [ntf] <;> ring

theorem lowGroupedE14W_hz82 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (1430024950673936947 / 1000000000000000000) (((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) := badd (lowGroupedE14W_hz70 hx hc) (lowGroupedE14W_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14W_hz83 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (384315750905393259 / 250000000000000000) ((((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) + ((√(92 : ℝ)) * (√x))) := badd (lowGroupedE14W_hz82 hx hc) (lowGroupedE14W_hz72 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14W_hz84 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B (1999999999999999997 / 1000000000000000000) (2174018188656028919 / 1000000000000000000) ((√(2 : ℝ)) * ((((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) + ((√(92 : ℝ)) * (√x)))) := bmul (lowGroupedE14W_hz4 hx hc) (lowGroupedE14W_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14W_hz85 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B (1999999999999999997 / 1000000000000000000) (2174018188656028919 / 1000000000000000000) (nz x) := by
    convert (lowGroupedE14W_hz84 hx hc) using 1 <;>
      norm_num [nz] <;> ring

theorem lowGroupedE14W_hz86 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B (582322667469245233 / 1000000000000000000) (125387240130618431 / 200000000000000000) (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE14W_hz55 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE14W_hz87 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B (582322667469245233 / 500000000000000000) (125387240130618431 / 100000000000000000) ((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) := bmul (bpoint (2 : ℝ)) (lowGroupedE14W_hz86 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14W_hz88 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B 0 (8505173090835039 / 500000000000000000) (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE14W_hz70 hx hc) (lowGroupedE14W_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14W_hz89 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B 0 (4265760722772029 / 200000000000000000) (((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE14W_hz87 hx hc) (lowGroupedE14W_hz88 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14W_hz90 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B 0 (144675938610129 / 500000000000000000) ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2) := bsq (lowGroupedE14W_hz88 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE14W_hz91 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B 0 (21618155491080403 / 1000000000000000000) ((((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) + ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2)) := badd (lowGroupedE14W_hz89 hx hc) (lowGroupedE14W_hz90 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14W_hz92 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B 0 (21618155491080403 / 500000000000000000) ((2 : ℝ) * ((((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) + ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2))) := bmul (bpoint (2 : ℝ)) (lowGroupedE14W_hz91 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14W_hz93 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B 0 (21618155491080403 / 500000000000000000) (nrad x (kdot (nc1 x c)/2+√23*x)) := by
    convert (lowGroupedE14W_hz92 hx hc) using 1 <;>
      norm_num [nrad] <;> ring

theorem lowGroupedE14W_hz94 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B (999999999999999997 / 250000000000000000) (5058850790612887039 / 1000000000000000000) ((ntf x (np1 x))^2) := bsq (lowGroupedE14W_hz81 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE14W_hz95 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B 0 (632356348826611 / 1000000000000000000) (((ntf x (np1 x))^2) * x) := bmul (lowGroupedE14W_hz94 hx hc) (lowGroupedE14W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14W_hz96 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B (1999999999999999997 / 500000000000000000) (140574307399437647 / 31250000000000000) ((2 : ℝ) * (ntf x (np1 x))) := bmul (bpoint (2 : ℝ)) (lowGroupedE14W_hz81 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14W_hz97 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B (999999999999999997 / 125000000000000000) (611222202288202473 / 62500000000000000) (((2 : ℝ) * (ntf x (np1 x))) * (nz x)) := bmul (lowGroupedE14W_hz96 hx hc) (lowGroupedE14W_hz85 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14W_hz98 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B (199999999999999999 / 25000000000000000) (1991325301148468661 / 200000000000000000) ((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) := bmul (lowGroupedE14W_hz97 hx hc) (lowGroupedE14W_hz64 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14W_hz99 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B 0 (1244578313217793 / 1000000000000000000) (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x) := bmul (lowGroupedE14W_hz98 hx hc) (lowGroupedE14W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14W_hz100 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B 0 (469233665511101 / 250000000000000000) ((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) := badd (lowGroupedE14W_hz95 hx hc) (lowGroupedE14W_hz99 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14W_hz101 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B (249999999999999999 / 250000000000000000) (6478377358333473 / 6250000000000000) ((neb x (1/2+√23*x))^2) := bsq (lowGroupedE14W_hz64 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE14W_hz102 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B 0 (5602022762493909 / 125000000000000000) ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2)) := bmul (lowGroupedE14W_hz93 hx hc) (lowGroupedE14W_hz101 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14W_hz103 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B 0 (11673279190498919 / 250000000000000000) (((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) + ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2))) := badd (lowGroupedE14W_hz100 hx hc) (lowGroupedE14W_hz102 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14W_hz104 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B (339099689048497161 / 500000000000000000) (393048999689334227 / 500000000000000000) ((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bmul (bpoint (2 : ℝ)) (lowGroupedE14W_hz55 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14W_hz105 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B (759997142898251869 / 1000000000000000000) (792051051909895527 / 1000000000000000000) ((neb x (kdot (728962483 / 1000000000)/2+√23*x))^2) := bsq (lowGroupedE14W_hz69 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE14W_hz106 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B (1999999999999999997 / 1000000000000000000) (2522480094977037223 / 1000000000000000000) ((np1 x)^2) := bsq (lowGroupedE14W_hz75 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE14W_hz107 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B 0 (31531001187213 / 100000000000000000) (((np1 x)^2) * x) := bmul (lowGroupedE14W_hz106 hx hc) (lowGroupedE14W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14W_hz108 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B (759997142898251869 / 1000000000000000000) (792366361921767657 / 1000000000000000000) (((neb x (kdot (728962483 / 1000000000)/2+√23*x))^2) + (((np1 x)^2) * x)) := badd (lowGroupedE14W_hz105 hx hc) (lowGroupedE14W_hz107 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14W_hz109 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B (257714794834543471 / 500000000000000000) (124575522376331099 / 200000000000000000) (((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) * (((neb x (kdot (728962483 / 1000000000)/2+√23*x))^2) + (((np1 x)^2) * x))) := bmul (lowGroupedE14W_hz104 hx hc) (lowGroupedE14W_hz108 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14W_hz110 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B (257714794834543471 / 500000000000000000) (669570728643651171 / 1000000000000000000) ((((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) + ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2))) + (((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) * (((neb x (kdot (728962483 / 1000000000)/2+√23*x))^2) + (((np1 x)^2) * x)))) := badd (lowGroupedE14W_hz103 hx hc) (lowGroupedE14W_hz109 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14W_hz111 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) : B (257714794834543471 / 500000000000000000) (669570728643651171 / 1000000000000000000) (ne x (kdot (nc1 x c)/2+√23*x) (neb x (1/2+√23*x)) (neb x (kdot (728962483 / 1000000000)/2+√23*x)^2) (np1 x)) := by
    convert (lowGroupedE14W_hz110 hx hc) using 1 <;>
      norm_num [ne] <;> ring

theorem lowGroupedE14W {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (5923997 / 15625000) (728962483 / 1000000000) c) :
    ne x (kdot (nc1 x c)/2+√23*x) (neb x (1/2+√23*x))
      (neb x (kdot (728962483 / 1000000000)/2+√23*x)^2) (np1 x) ≤ (669570729 / 1000000000) :=
  (lowGroupedE14W_hz111 hx hc).2.trans (by norm_num)

theorem lowGroupedE14C_hz0 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B 0 (1 / 8000) x := hx

theorem lowGroupedE14C_hz1 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B (454387443 / 1000000000) (38838151 / 62500000) c := hc

theorem lowGroupedE14C_hz2 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B (6782329983125268139 / 500000000000000000) (13564659966250536279 / 1000000000000000000) (√(184 : ℝ)) := bsqrt (bpoint (184 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE14C_hz3 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE14C_hz4 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B (176776695296636881 / 125000000000000000) (1414213562373095049 / 1000000000000000000) (√(2 : ℝ)) := bsqrt (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE14C_hz5 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B 0 (847791247890659 / 500000000000000000) ((√(184 : ℝ)) * x) := bmul (lowGroupedE14C_hz2 hx hc) (lowGroupedE14C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14C_hz6 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B 1 (500847791247890659 / 500000000000000000) ((1 : ℝ) + ((√(184 : ℝ)) * x)) := badd (bpoint (1 : ℝ)) (lowGroupedE14C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14C_hz7 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B 1 (500847791247890659 / 500000000000000000) (nap x) := by
    convert (lowGroupedE14C_hz6 hx hc) using 1 <;>
      norm_num [nap] <;> ring

theorem lowGroupedE14C_hz8 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B 0 (1 / 64000000) (x^2) := bsq (lowGroupedE14C_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE14C_hz9 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B 0 (1 / 32000000) ((2 : ℝ) * (x^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE14C_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14C_hz10 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B (31999999 / 32000000) 1 ((1 : ℝ) - ((2 : ℝ) * (x^2))) := bsub (bpoint (1 : ℝ)) (lowGroupedE14C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14C_hz11 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B (999999984374999877 / 1000000000000000000) 1 (√((1 : ℝ) - ((2 : ℝ) * (x^2)))) := bsqrt (lowGroupedE14C_hz10 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE14C_hz12 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B (998304401879218559 / 1000000000000000000) 1 ((√((1 : ℝ) - ((2 : ℝ) * (x^2)))) - ((√(184 : ℝ)) * x)) := bsub (lowGroupedE14C_hz11 hx hc) (lowGroupedE14C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14C_hz13 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B (998304401879218559 / 1000000000000000000) 1 (nam x) := by
    convert (lowGroupedE14C_hz12 hx hc) using 1 <;>
      norm_num [nam] <;> ring

theorem lowGroupedE14C_hz14 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B (650141823104965217 / 1000000000000000000) (650141823105926207 / 1000000000000000000) (kdot ((454387443 / 1000000000))) := by
    constructor
    · apply bkdot_lower (q := (1914044991035629 / 3125000000000000)) (a := (274777969582939903 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (612494397131401279 / 1000000000000000000)) (a := (34347246197773143 / 62500000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE14C_hz15 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B (206467948356078249 / 1000000000000000000) (206467948356078249 / 1000000000000000000) (((454387443 / 1000000000) : ℝ)^2) := bsq (bpoint ((454387443 / 1000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE14C_hz16 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B (793532051643921751 / 1000000000000000000) (793532051643921751 / 1000000000000000000) ((1 : ℝ) - (((454387443 / 1000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowGroupedE14C_hz15 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14C_hz17 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B (890804160095765241 / 1000000000000000000) (445402080047882621 / 500000000000000000) (√((1 : ℝ) - (((454387443 / 1000000000) : ℝ)^2))) := bsqrt (lowGroupedE14C_hz16 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE14C_hz18 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B (283551770812130277 / 1000000000000000000) (283551770812130279 / 1000000000000000000) ((√((1 : ℝ) - (((454387443 / 1000000000) : ℝ)^2))) / Real.pi) := bdiv (lowGroupedE14C_hz17 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE14C_hz19 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B (59083256117604693 / 200000000000000000) (9231758768389379 / 31250000000000000) (((454387443 / 1000000000) : ℝ) * (kdot ((454387443 / 1000000000)))) := bmul (bpoint ((454387443 / 1000000000) : ℝ)) (lowGroupedE14C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14C_hz20 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B (289484025700076871 / 500000000000000000) (578968051400590407 / 1000000000000000000) (((√((1 : ℝ) - (((454387443 / 1000000000) : ℝ)^2))) / Real.pi) + (((454387443 / 1000000000) : ℝ) * (kdot ((454387443 / 1000000000))))) := badd (lowGroupedE14C_hz18 hx hc) (lowGroupedE14C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14C_hz21 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B (289484025700076871 / 500000000000000000) (578968051400590407 / 1000000000000000000) (kappa ((454387443 / 1000000000))) := by rw [kappa_eq]; exact (lowGroupedE14C_hz20 hx hc)

theorem lowGroupedE14C_hz22 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B (713440021290409267 / 1000000000000000000) (356720010645204639 / 500000000000000000) (kdot ((38838151 / 62500000))) := by
    constructor
    · apply bkdot_lower (q := (483212156165824897 / 1000000000000000000)) (a := (225063680981724451 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (3775094970045507 / 7812500000000000)) (a := (225063680981724443 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE14C_hz23 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B (1508401973098801 / 3906250000000000) (1508401973098801 / 3906250000000000) (((38838151 / 62500000) : ℝ)^2) := bsq (bpoint ((38838151 / 62500000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE14C_hz24 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B (2397848026901199 / 3906250000000000) (2397848026901199 / 3906250000000000) ((1 : ℝ) - (((38838151 / 62500000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowGroupedE14C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14C_hz25 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B (78348522314508711 / 100000000000000000) (783485223145087111 / 1000000000000000000) (√((1 : ℝ) - (((38838151 / 62500000) : ℝ)^2))) := bsqrt (lowGroupedE14C_hz24 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE14C_hz26 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B (124695546102997257 / 500000000000000000) (62347773051498629 / 250000000000000000) ((√((1 : ℝ) - (((38838151 / 62500000) : ℝ)^2))) / Real.pi) := bdiv (lowGroupedE14C_hz25 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE14C_hz27 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B (443339060421122079 / 1000000000000000000) (443339060421122087 / 1000000000000000000) (((38838151 / 62500000) : ℝ) * (kdot ((38838151 / 62500000)))) := bmul (bpoint ((38838151 / 62500000) : ℝ)) (lowGroupedE14C_hz22 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14C_hz28 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B (692730152627116593 / 1000000000000000000) (692730152627116603 / 1000000000000000000) (((√((1 : ℝ) - (((38838151 / 62500000) : ℝ)^2))) / Real.pi) + (((38838151 / 62500000) : ℝ) * (kdot ((38838151 / 62500000))))) := badd (lowGroupedE14C_hz26 hx hc) (lowGroupedE14C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14C_hz29 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B (692730152627116593 / 1000000000000000000) (692730152627116603 / 1000000000000000000) (kappa ((38838151 / 62500000))) := by rw [kappa_eq]; exact (lowGroupedE14C_hz28 hx hc)

theorem lowGroupedE14C_hz30 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B (289484025700076871 / 500000000000000000) (692730152627116603 / 1000000000000000000) (kappa c) := bkappa (lowGroupedE14C_hz1 hx hc) (by norm_num) (by norm_num) (lowGroupedE14C_hz21 hx hc).1 (lowGroupedE14C_hz29 hx hc).2

theorem lowGroupedE14C_hz31 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B (307269847372883397 / 1000000000000000000) (210515974299923129 / 500000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (lowGroupedE14C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14C_hz32 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B (307269847372883397 / 500000000000000000) (210515974299923129 / 250000000000000000) ((2 : ℝ) * ((1 : ℝ) - (kappa c))) := bmul (bpoint (2 : ℝ)) (lowGroupedE14C_hz31 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14C_hz33 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B 0 (1 / 8000000) ((8 : ℝ) * (x^2)) := bmul (bpoint (8 : ℝ)) (lowGroupedE14C_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14C_hz34 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B (307269784872883397 / 500000000000000000) (210515974299923129 / 250000000000000000) (((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2))) := bsub (lowGroupedE14C_hz32 hx hc) (lowGroupedE14C_hz33 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14C_hz35 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B (391962871247318141 / 500000000000000000) (917640396451514397 / 1000000000000000000) (√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) := bsqrt (lowGroupedE14C_hz34 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE14C_hz36 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B (6782329983125268139 / 250000000000000000) (13564659966250536279 / 500000000000000000) ((2 : ℝ) * (√(184 : ℝ))) := bmul (bpoint (2 : ℝ)) (lowGroupedE14C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14C_hz37 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B 0 (678232998312527 / 200000000000000000) (((2 : ℝ) * (√(184 : ℝ))) * x) := bmul (lowGroupedE14C_hz36 hx hc) (lowGroupedE14C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14C_hz38 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B (780534577503073647 / 1000000000000000000) (917640396451514397 / 1000000000000000000) ((√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) - (((2 : ℝ) * (√(184 : ℝ))) * x)) := bsub (lowGroupedE14C_hz35 hx hc) (lowGroupedE14C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14C_hz39 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B (780534577503073647 / 1000000000000000000) (917640396451514397 / 1000000000000000000) (ndm x c) := by
    convert (lowGroupedE14C_hz38 hx hc) using 1 <;>
      norm_num [ndm] <;> ring

theorem lowGroupedE14C_hz40 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B 1 (1003394039991562637 / 1000000000000000000) ((nap x)^2) := bsq (lowGroupedE14C_hz7 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE14C_hz41 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B 2 (1003394039991562637 / 500000000000000000) ((2 : ℝ) * ((nap x)^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE14C_hz40 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14C_hz42 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B (609234226677901681 / 1000000000000000000) (842063897199692517 / 1000000000000000000) ((ndm x c)^2) := bsq (lowGroupedE14C_hz39 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE14C_hz43 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B (1157936102800307483 / 1000000000000000000) (1397553853305223593 / 1000000000000000000) (((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) := bsub (lowGroupedE14C_hz41 hx hc) (lowGroupedE14C_hz42 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14C_hz44 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B (199322335762284863 / 200000000000000000) 1 ((nam x)^2) := bsq (lowGroupedE14C_hz13 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE14C_hz45 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B (199322335762284863 / 100000000000000000) 2 ((2 : ℝ) * ((nam x)^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE14C_hz44 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14C_hz46 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B (578968051400153741 / 1000000000000000000) (701152657056943981 / 1000000000000000000) ((((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) / ((2 : ℝ) * ((nam x)^2))) := bdiv (lowGroupedE14C_hz43 hx hc) (lowGroupedE14C_hz45 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE14C_hz47 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B (578968051400153741 / 1000000000000000000) (701152657056943981 / 1000000000000000000) (nc1 x c) := by
    convert (lowGroupedE14C_hz46 hx hc) using 1 <;>
      norm_num [nc1] <;> ring

theorem lowGroupedE14C_hz48 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B (696544408667653197 / 1000000000000000000) (696544408667653423 / 1000000000000000000) (kdot ((578968051400153741 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (516381713985452759 / 1000000000000000000)) (a := (238333464105111813 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (258190856992726379 / 500000000000000000)) (a := (59583366026277909 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE14C_hz49 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B (149466172384996517 / 200000000000000000) (747330861924982587 / 1000000000000000000) (kdot ((701152657056943981 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (209567078868840083 / 500000000000000000)) (a := (396891753982669911 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (83826831547536033 / 200000000000000000)) (a := (396891753982669909 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE14C_hz50 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B (696544408667653197 / 1000000000000000000) (747330861924982587 / 1000000000000000000) (kdot (nc1 x c)) := bkdot (lowGroupedE14C_hz47 hx hc) (lowGroupedE14C_hz48 hx hc).1 (lowGroupedE14C_hz49 hx hc).2

theorem lowGroupedE14C_hz51 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE14C_hz52 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B 0 (59947894041409 / 100000000000000000) ((√(23 : ℝ)) * x) := bmul (lowGroupedE14C_hz51 hx hc) (lowGroupedE14C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14C_hz53 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B (1 / 2) (50059947894041409 / 100000000000000000) (((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)) := badd (bpoint ((1 / 2) : ℝ)) (lowGroupedE14C_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14C_hz54 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B (174136102166913299 / 500000000000000000) (186832715481245647 / 500000000000000000) ((kdot (nc1 x c)) / (2 : ℝ)) := bdiv (lowGroupedE14C_hz50 hx hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE14C_hz55 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B (174136102166913299 / 500000000000000000) (46783113737863173 / 125000000000000000) (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)) := badd (lowGroupedE14C_hz54 hx hc) (lowGroupedE14C_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14C_hz56 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B (356720010645204633 / 1000000000000000000) (356720010645204639 / 1000000000000000000) ((kdot ((38838151 / 62500000))) / (2 : ℝ)) := bdiv (lowGroupedE14C_hz22 hx hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE14C_hz57 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B (356720010645204633 / 1000000000000000000) (357319489585618729 / 1000000000000000000) (((kdot ((38838151 / 62500000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x)) := badd (lowGroupedE14C_hz56 hx hc) (lowGroupedE14C_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14C_hz58 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B (176776695296636881 / 250000000000000000) (353765274914177413 / 500000000000000000) (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE14C_hz53 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE14C_hz59 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGroupedE14C_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE14C_hz60 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B (176776695296636881 / 250000000000000000) (28748435588634151 / 40000000000000000) ((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) := badd (lowGroupedE14C_hz58 hx hc) (lowGroupedE14C_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14C_hz61 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B 0 (59947894041409 / 50000000000000000) ((√(92 : ℝ)) * x) := bmul (lowGroupedE14C_hz3 hx hc) (lowGroupedE14C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14C_hz62 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B (176776695296636881 / 250000000000000000) (143981969519336391 / 200000000000000000) (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE14C_hz60 hx hc) (lowGroupedE14C_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14C_hz63 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B (499999999999999999 / 500000000000000000) (1018106270157175527 / 1000000000000000000) ((√(2 : ℝ)) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE14C_hz4 hx hc) (lowGroupedE14C_hz62 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14C_hz64 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B (499999999999999999 / 500000000000000000) (1018106270157175527 / 1000000000000000000) (neb x (1/2+√23*x)) := by
    convert (lowGroupedE14C_hz63 hx hc) using 1 <;>
      norm_num [neb] <;> ring

theorem lowGroupedE14C_hz65 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B (298630210563668789 / 500000000000000000) (149440516925970149 / 250000000000000000) (√(((kdot ((38838151 / 62500000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE14C_hz57 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE14C_hz66 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B (298630210563668789 / 500000000000000000) (121788481518275909 / 200000000000000000) ((√(((kdot ((38838151 / 62500000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) := badd (lowGroupedE14C_hz65 hx hc) (lowGroupedE14C_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14C_hz67 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B (298630210563668789 / 500000000000000000) (24405654618888309 / 40000000000000000) (((√(((kdot ((38838151 / 62500000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE14C_hz66 hx hc) (lowGroupedE14C_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14C_hz68 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B (844653787826947037 / 1000000000000000000) (431435097007817711 / 500000000000000000) ((√(2 : ℝ)) * (((√(((kdot ((38838151 / 62500000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE14C_hz4 hx hc) (lowGroupedE14C_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14C_hz69 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B (844653787826947037 / 1000000000000000000) (431435097007817711 / 500000000000000000) (neb x (kdot (38838151 / 62500000)/2+√23*x)) := by
    convert (lowGroupedE14C_hz68 hx hc) using 1 <;>
      norm_num [neb] <;> ring

theorem lowGroupedE14C_hz70 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B 0 (7905694150420949 / 500000000000000000) ((√(2 : ℝ)) * (√x)) := bmul (lowGroupedE14C_hz4 hx hc) (lowGroupedE14C_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14C_hz71 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B 1 (507905694150420949 / 500000000000000000) (((√(2 : ℝ)) * (√x)) + (1 : ℝ)) := badd (lowGroupedE14C_hz70 hx hc) (bpoint (1 : ℝ)) (by norm_num) (by norm_num)

theorem lowGroupedE14C_hz72 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B 0 (107238052947636089 / 1000000000000000000) ((√(92 : ℝ)) * (√x)) := bmul (lowGroupedE14C_hz3 hx hc) (lowGroupedE14C_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14C_hz73 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B 1 (1123049441248477987 / 1000000000000000000) ((((√(2 : ℝ)) * (√x)) + (1 : ℝ)) + ((√(92 : ℝ)) * (√x))) := badd (lowGroupedE14C_hz71 hx hc) (lowGroupedE14C_hz72 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14C_hz74 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B (176776695296636881 / 125000000000000000) (12408060554915031 / 7812500000000000) ((√(2 : ℝ)) * ((((√(2 : ℝ)) * (√x)) + (1 : ℝ)) + ((√(92 : ℝ)) * (√x)))) := bmul (lowGroupedE14C_hz4 hx hc) (lowGroupedE14C_hz73 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14C_hz75 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B (176776695296636881 / 125000000000000000) (12408060554915031 / 7812500000000000) (np1 x) := by
    convert (lowGroupedE14C_hz74 hx hc) using 1 <;>
      norm_num [np1] <;> ring

theorem lowGroupedE14C_hz76 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B (11005876608998534131 / 1000000000000000000) (11005876608998534133 / 1000000000000000000) ((√(2 : ℝ)) + (√(92 : ℝ))) := badd (lowGroupedE14C_hz4 hx hc) (lowGroupedE14C_hz3 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14C_hz77 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B 0 (1375734576124817 / 1000000000000000000) (((√(2 : ℝ)) + (√(92 : ℝ))) * x) := bmul (lowGroupedE14C_hz76 hx hc) (lowGroupedE14C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14C_hz78 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B 1 (1001375734576124817 / 1000000000000000000) ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x)) := badd (bpoint (1 : ℝ)) (lowGroupedE14C_hz77 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14C_hz79 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B (176776695296636881 / 125000000000000000) (1416159144868876367 / 1000000000000000000) ((√(2 : ℝ)) * ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x))) := bmul (lowGroupedE14C_hz4 hx hc) (lowGroupedE14C_hz78 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14C_hz80 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B (1999999999999999997 / 1000000000000000000) (140574307399437647 / 62500000000000000) (((√(2 : ℝ)) * ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x))) * (np1 x)) := bmul (lowGroupedE14C_hz79 hx hc) (lowGroupedE14C_hz75 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14C_hz81 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B (1999999999999999997 / 1000000000000000000) (140574307399437647 / 62500000000000000) (ntf x (np1 x)) := by
    convert (lowGroupedE14C_hz80 hx hc) using 1 <;>
      norm_num [ntf] <;> ring

theorem lowGroupedE14C_hz82 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B (176776695296636881 / 125000000000000000) (1430024950673936947 / 1000000000000000000) (((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) := badd (lowGroupedE14C_hz70 hx hc) (lowGroupedE14C_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14C_hz83 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B (176776695296636881 / 125000000000000000) (384315750905393259 / 250000000000000000) ((((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) + ((√(92 : ℝ)) * (√x))) := badd (lowGroupedE14C_hz82 hx hc) (lowGroupedE14C_hz72 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14C_hz84 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B (1999999999999999997 / 1000000000000000000) (2174018188656028919 / 1000000000000000000) ((√(2 : ℝ)) * ((((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) + ((√(92 : ℝ)) * (√x)))) := bmul (lowGroupedE14C_hz4 hx hc) (lowGroupedE14C_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14C_hz85 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B (1999999999999999997 / 1000000000000000000) (2174018188656028919 / 1000000000000000000) (nz x) := by
    convert (lowGroupedE14C_hz84 hx hc) using 1 <;>
      norm_num [nz] <;> ring

theorem lowGroupedE14C_hz86 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B (590145917832044821 / 1000000000000000000) (152942985680715631 / 250000000000000000) (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE14C_hz55 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE14C_hz87 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B (590145917832044821 / 500000000000000000) (152942985680715631 / 125000000000000000) ((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) := bmul (bpoint (2 : ℝ)) (lowGroupedE14C_hz86 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14C_hz88 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B 0 (8505173090835039 / 500000000000000000) (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE14C_hz70 hx hc) (lowGroupedE14C_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14C_hz89 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B 0 (20812905059897461 / 1000000000000000000) (((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE14C_hz87 hx hc) (lowGroupedE14C_hz88 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14C_hz90 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B 0 (144675938610129 / 500000000000000000) ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2) := bsq (lowGroupedE14C_hz88 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE14C_hz91 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B 0 (21102256937117719 / 1000000000000000000) ((((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) + ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2)) := badd (lowGroupedE14C_hz89 hx hc) (lowGroupedE14C_hz90 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14C_hz92 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B 0 (21102256937117719 / 500000000000000000) ((2 : ℝ) * ((((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) + ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2))) := bmul (bpoint (2 : ℝ)) (lowGroupedE14C_hz91 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14C_hz93 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B 0 (21102256937117719 / 500000000000000000) (nrad x (kdot (nc1 x c)/2+√23*x)) := by
    convert (lowGroupedE14C_hz92 hx hc) using 1 <;>
      norm_num [nrad] <;> ring

theorem lowGroupedE14C_hz94 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B (999999999999999997 / 250000000000000000) (5058850790612887039 / 1000000000000000000) ((ntf x (np1 x))^2) := bsq (lowGroupedE14C_hz81 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE14C_hz95 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B 0 (632356348826611 / 1000000000000000000) (((ntf x (np1 x))^2) * x) := bmul (lowGroupedE14C_hz94 hx hc) (lowGroupedE14C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14C_hz96 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B (1999999999999999997 / 500000000000000000) (140574307399437647 / 31250000000000000) ((2 : ℝ) * (ntf x (np1 x))) := bmul (bpoint (2 : ℝ)) (lowGroupedE14C_hz81 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14C_hz97 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B (999999999999999997 / 125000000000000000) (611222202288202473 / 62500000000000000) (((2 : ℝ) * (ntf x (np1 x))) * (nz x)) := bmul (lowGroupedE14C_hz96 hx hc) (lowGroupedE14C_hz85 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14C_hz98 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B (199999999999999999 / 25000000000000000) (1991325301148468661 / 200000000000000000) ((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) := bmul (lowGroupedE14C_hz97 hx hc) (lowGroupedE14C_hz64 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14C_hz99 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B 0 (1244578313217793 / 1000000000000000000) (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x) := bmul (lowGroupedE14C_hz98 hx hc) (lowGroupedE14C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14C_hz100 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B 0 (469233665511101 / 250000000000000000) ((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) := badd (lowGroupedE14C_hz95 hx hc) (lowGroupedE14C_hz99 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14C_hz101 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B (249999999999999999 / 250000000000000000) (6478377358333473 / 6250000000000000) ((neb x (1/2+√23*x))^2) := bsq (lowGroupedE14C_hz64 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE14C_hz102 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B 0 (21873341368185423 / 500000000000000000) ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2)) := bmul (lowGroupedE14C_hz93 hx hc) (lowGroupedE14C_hz101 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14C_hz103 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B 0 (182494469593661 / 4000000000000000) (((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) + ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2))) := badd (lowGroupedE14C_hz100 hx hc) (lowGroupedE14C_hz102 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14C_hz104 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B (174136102166913299 / 250000000000000000) (46783113737863173 / 62500000000000000) ((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bmul (bpoint (2 : ℝ)) (lowGroupedE14C_hz55 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14C_hz105 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B (356720010645204631 / 500000000000000000) (186136242930145079 / 250000000000000000) ((neb x (kdot (38838151 / 62500000)/2+√23*x))^2) := bsq (lowGroupedE14C_hz69 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE14C_hz106 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B (1999999999999999997 / 1000000000000000000) (2522480094977037223 / 1000000000000000000) ((np1 x)^2) := bsq (lowGroupedE14C_hz75 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE14C_hz107 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B 0 (31531001187213 / 100000000000000000) (((np1 x)^2) * x) := bmul (lowGroupedE14C_hz106 hx hc) (lowGroupedE14C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14C_hz108 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B (356720010645204631 / 500000000000000000) (372430140866226223 / 500000000000000000) (((neb x (kdot (38838151 / 62500000)/2+√23*x))^2) + (((np1 x)^2) * x)) := badd (lowGroupedE14C_hz105 hx hc) (lowGroupedE14C_hz107 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14C_hz109 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B (19877706309982641 / 40000000000000000) (69693766558212259 / 125000000000000000) (((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) * (((neb x (kdot (38838151 / 62500000)/2+√23*x))^2) + (((np1 x)^2) * x))) := bmul (lowGroupedE14C_hz104 hx hc) (lowGroupedE14C_hz108 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14C_hz110 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B (19877706309982641 / 40000000000000000) (301586874932056661 / 500000000000000000) ((((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) + ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2))) + (((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) * (((neb x (kdot (38838151 / 62500000)/2+√23*x))^2) + (((np1 x)^2) * x)))) := badd (lowGroupedE14C_hz103 hx hc) (lowGroupedE14C_hz109 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE14C_hz111 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) : B (19877706309982641 / 40000000000000000) (301586874932056661 / 500000000000000000) (ne x (kdot (nc1 x c)/2+√23*x) (neb x (1/2+√23*x)) (neb x (kdot (38838151 / 62500000)/2+√23*x)^2) (np1 x)) := by
    convert (lowGroupedE14C_hz110 hx hc) using 1 <;>
      norm_num [ne] <;> ring

theorem lowGroupedE14C {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (454387443 / 1000000000) (38838151 / 62500000) c) :
    ne x (kdot (nc1 x c)/2+√23*x) (neb x (1/2+√23*x))
      (neb x (kdot (38838151 / 62500000)/2+√23*x)^2) (np1 x) ≤ (482539 / 800000) :=
  (lowGroupedE14C_hz111 hx hc).2.trans (by norm_num)

theorem lowGroupedE16W_hz0 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B 0 (1 / 8000) x := hx

theorem lowGroupedE16W_hz1 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B (189056793 / 500000000) (728044459 / 1000000000) c := hc

theorem lowGroupedE16W_hz2 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B (6782329983125268139 / 500000000000000000) (13564659966250536279 / 1000000000000000000) (√(184 : ℝ)) := bsqrt (bpoint (184 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE16W_hz3 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE16W_hz4 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (1414213562373095049 / 1000000000000000000) (√(2 : ℝ)) := bsqrt (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE16W_hz5 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B 0 (847791247890659 / 500000000000000000) ((√(184 : ℝ)) * x) := bmul (lowGroupedE16W_hz2 hx hc) (lowGroupedE16W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16W_hz6 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B 1 (500847791247890659 / 500000000000000000) ((1 : ℝ) + ((√(184 : ℝ)) * x)) := badd (bpoint (1 : ℝ)) (lowGroupedE16W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16W_hz7 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B 1 (500847791247890659 / 500000000000000000) (nap x) := by
    convert (lowGroupedE16W_hz6 hx hc) using 1 <;>
      norm_num [nap] <;> ring

theorem lowGroupedE16W_hz8 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B 0 (1 / 64000000) (x^2) := bsq (lowGroupedE16W_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE16W_hz9 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B 0 (1 / 32000000) ((2 : ℝ) * (x^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE16W_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16W_hz10 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B (31999999 / 32000000) 1 ((1 : ℝ) - ((2 : ℝ) * (x^2))) := bsub (bpoint (1 : ℝ)) (lowGroupedE16W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16W_hz11 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B (999999984374999877 / 1000000000000000000) 1 (√((1 : ℝ) - ((2 : ℝ) * (x^2)))) := bsqrt (lowGroupedE16W_hz10 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE16W_hz12 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B (998304401879218559 / 1000000000000000000) 1 ((√((1 : ℝ) - ((2 : ℝ) * (x^2)))) - ((√(184 : ℝ)) * x)) := bsub (lowGroupedE16W_hz11 hx hc) (lowGroupedE16W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16W_hz13 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B (998304401879218559 / 1000000000000000000) 1 (nam x) := by
    convert (lowGroupedE16W_hz12 hx hc) using 1 <;>
      norm_num [nam] <;> ring

theorem lowGroupedE16W_hz14 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B (31171356300825151 / 50000000000000000) (623427126105249757 / 1000000000000000000) (kdot ((189056793 / 500000000))) := by
    constructor
    · apply bkdot_lower (q := (167939569721107353 / 250000000000000000)) (a := (118303857444774909 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (671758278884429411 / 1000000000000000000)) (a := (591519287084471497 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE16W_hz15 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B (35742470979444849 / 250000000000000000) (35742470979444849 / 250000000000000000) (((189056793 / 500000000) : ℝ)^2) := bsq (bpoint ((189056793 / 500000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE16W_hz16 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B (214257529020555151 / 250000000000000000) (214257529020555151 / 250000000000000000) ((1 : ℝ) - (((189056793 / 500000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowGroupedE16W_hz15 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16W_hz17 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B (185151842127721819 / 200000000000000000) (115719901329826137 / 125000000000000000) (√((1 : ℝ) - (((189056793 / 500000000) : ℝ)^2))) := bsqrt (lowGroupedE16W_hz16 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE16W_hz18 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B (58935661794394311 / 200000000000000000) (73669577242992889 / 250000000000000000) ((√((1 : ℝ) - (((189056793 / 500000000) : ℝ)^2))) / Real.pi) := bdiv (lowGroupedE16W_hz17 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE16W_hz19 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B (58931566556943463 / 250000000000000000) (1178631331306651 / 5000000000000000) (((189056793 / 500000000) : ℝ) * (kdot ((189056793 / 500000000)))) := bmul (bpoint ((189056793 / 500000000) : ℝ)) (lowGroupedE16W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16W_hz20 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B (530404575199745407 / 1000000000000000000) (132601143808325439 / 250000000000000000) (((√((1 : ℝ) - (((189056793 / 500000000) : ℝ)^2))) / Real.pi) + (((189056793 / 500000000) : ℝ) * (kdot ((189056793 / 500000000))))) := badd (lowGroupedE16W_hz18 hx hc) (lowGroupedE16W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16W_hz21 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B (530404575199745407 / 1000000000000000000) (132601143808325439 / 250000000000000000) (kappa ((189056793 / 500000000))) := by rw [kappa_eq]; exact (lowGroupedE16W_hz20 hx hc)

theorem lowGroupedE16W_hz22 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B (30382823044502669 / 40000000000000000) (94946322014070841 / 125000000000000000) (kdot ((728044459 / 1000000000))) := by
    constructor
    · apply bkdot_lower (q := (396708494634605617 / 1000000000000000000)) (a := (377665655895793361 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (24794280914662851 / 62500000000000000)) (a := (377665655895793359 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE16W_hz23 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B (530048734280602681 / 1000000000000000000) (530048734280602681 / 1000000000000000000) (((728044459 / 1000000000) : ℝ)^2) := bsq (bpoint ((728044459 / 1000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE16W_hz24 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B (469951265719397319 / 1000000000000000000) (469951265719397319 / 1000000000000000000) ((1 : ℝ) - (((728044459 / 1000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowGroupedE16W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16W_hz25 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B (85691239498945183 / 125000000000000000) (137105983198312293 / 200000000000000000) (√((1 : ℝ) - (((728044459 / 1000000000) : ℝ)^2))) := bsqrt (lowGroupedE16W_hz24 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE16W_hz26 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B (21821094953485751 / 100000000000000000) (218210949534857511 / 1000000000000000000) ((√((1 : ℝ) - (((728044459 / 1000000000) : ℝ)^2))) / Real.pi) := bdiv (lowGroupedE16W_hz25 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE16W_hz27 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B (138250287289547991 / 250000000000000000) (553001149158191967 / 1000000000000000000) (((728044459 / 1000000000) : ℝ) * (kdot ((728044459 / 1000000000)))) := bmul (bpoint ((728044459 / 1000000000) : ℝ)) (lowGroupedE16W_hz22 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16W_hz28 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B (385606049346524737 / 500000000000000000) (385606049346524739 / 500000000000000000) (((√((1 : ℝ) - (((728044459 / 1000000000) : ℝ)^2))) / Real.pi) + (((728044459 / 1000000000) : ℝ) * (kdot ((728044459 / 1000000000))))) := badd (lowGroupedE16W_hz26 hx hc) (lowGroupedE16W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16W_hz29 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B (385606049346524737 / 500000000000000000) (385606049346524739 / 500000000000000000) (kappa ((728044459 / 1000000000))) := by rw [kappa_eq]; exact (lowGroupedE16W_hz28 hx hc)

theorem lowGroupedE16W_hz30 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B (530404575199745407 / 1000000000000000000) (385606049346524739 / 500000000000000000) (kappa c) := bkappa (lowGroupedE16W_hz1 hx hc) (by norm_num) (by norm_num) (lowGroupedE16W_hz21 hx hc).1 (lowGroupedE16W_hz29 hx hc).2

theorem lowGroupedE16W_hz31 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B (114393950653475261 / 500000000000000000) (469595424800254593 / 1000000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (lowGroupedE16W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16W_hz32 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B (114393950653475261 / 250000000000000000) (469595424800254593 / 500000000000000000) ((2 : ℝ) * ((1 : ℝ) - (kappa c))) := bmul (bpoint (2 : ℝ)) (lowGroupedE16W_hz31 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16W_hz33 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B 0 (1 / 8000000) ((8 : ℝ) * (x^2)) := bmul (bpoint (8 : ℝ)) (lowGroupedE16W_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16W_hz34 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B (114393919403475261 / 250000000000000000) (469595424800254593 / 500000000000000000) (((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2))) := bsub (lowGroupedE16W_hz32 hx hc) (lowGroupedE16W_hz33 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16W_hz35 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B (676443403112116279 / 1000000000000000000) (30284956068368289 / 31250000000000000) (√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) := bsqrt (lowGroupedE16W_hz34 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE16W_hz36 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B (6782329983125268139 / 250000000000000000) (13564659966250536279 / 500000000000000000) ((2 : ℝ) * (√(184 : ℝ))) := bmul (bpoint (2 : ℝ)) (lowGroupedE16W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16W_hz37 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B 0 (678232998312527 / 200000000000000000) (((2 : ℝ) * (√(184 : ℝ))) * x) := bmul (lowGroupedE16W_hz36 hx hc) (lowGroupedE16W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16W_hz38 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B (168263059530138411 / 250000000000000000) (30284956068368289 / 31250000000000000) ((√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) - (((2 : ℝ) * (√(184 : ℝ))) * x)) := bsub (lowGroupedE16W_hz35 hx hc) (lowGroupedE16W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16W_hz39 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B (168263059530138411 / 250000000000000000) (30284956068368289 / 31250000000000000) (ndm x c) := by
    convert (lowGroupedE16W_hz38 hx hc) using 1 <;>
      norm_num [ndm] <;> ring

theorem lowGroupedE16W_hz40 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B 1 (1003394039991562637 / 1000000000000000000) ((nap x)^2) := bsq (lowGroupedE16W_hz7 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE16W_hz41 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B 2 (1003394039991562637 / 500000000000000000) ((2 : ℝ) * ((nap x)^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE16W_hz40 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16W_hz42 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B (452999315239086443 / 1000000000000000000) (234797712400127297 / 250000000000000000) ((ndm x c)^2) := bsq (lowGroupedE16W_hz39 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE16W_hz43 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B (265202287599872703 / 250000000000000000) (1553788764744038831 / 1000000000000000000) (((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) := bsub (lowGroupedE16W_hz41 hx hc) (lowGroupedE16W_hz42 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16W_hz44 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B (199322335762284863 / 200000000000000000) 1 ((nam x)^2) := bsq (lowGroupedE16W_hz13 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE16W_hz45 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B (199322335762284863 / 100000000000000000) 2 ((2 : ℝ) * ((nam x)^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE16W_hz44 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16W_hz46 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B (265202287599872703 / 500000000000000000) (380632665869417 / 488281250000000) ((((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) / ((2 : ℝ) * ((nam x)^2))) := bdiv (lowGroupedE16W_hz43 hx hc) (lowGroupedE16W_hz45 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE16W_hz47 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B (265202287599872703 / 500000000000000000) (380632665869417 / 488281250000000) (nc1 x c) := by
    convert (lowGroupedE16W_hz46 hx hc) using 1 <;>
      norm_num [nc1] <;> ring

theorem lowGroupedE16W_hz48 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B (169489992249423489 / 250000000000000000) (42372498062356309 / 62500000000000000) (kdot ((265202287599872703 / 500000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (553934992609682721 / 1000000000000000000)) (a := (252929648889668481 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (3462093703810517 / 6250000000000000)) (a := (505859297779325987 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE16W_hz49 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B (24517028496817617 / 31250000000000000) (392272455949081873 / 500000000000000000) (kdot ((380632665869417 / 488281250000000))) := by
    constructor
    · apply bkdot_lower (q := (351978215173690963 / 1000000000000000000)) (a := (13537442439185409 / 40000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (175989107586845481 / 500000000000000000)) (a := (338436060979635223 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE16W_hz50 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B (169489992249423489 / 250000000000000000) (392272455949081873 / 500000000000000000) (kdot (nc1 x c)) := bkdot (lowGroupedE16W_hz47 hx hc) (lowGroupedE16W_hz48 hx hc).1 (lowGroupedE16W_hz49 hx hc).2

theorem lowGroupedE16W_hz51 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE16W_hz52 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B 0 (59947894041409 / 100000000000000000) ((√(23 : ℝ)) * x) := bmul (lowGroupedE16W_hz51 hx hc) (lowGroupedE16W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16W_hz53 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B (1 / 2) (50059947894041409 / 100000000000000000) (((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)) := badd (bpoint ((1 / 2) : ℝ)) (lowGroupedE16W_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16W_hz54 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B (169489992249423489 / 500000000000000000) (392272455949081873 / 1000000000000000000) ((kdot (nc1 x c)) / (2 : ℝ)) := bdiv (lowGroupedE16W_hz50 hx hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE16W_hz55 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B (169489992249423489 / 500000000000000000) (392871934889495963 / 1000000000000000000) (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)) := badd (lowGroupedE16W_hz54 hx hc) (lowGroupedE16W_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16W_hz56 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B (189892644028141681 / 500000000000000000) (94946322014070841 / 250000000000000000) ((kdot ((728044459 / 1000000000))) / (2 : ℝ)) := bdiv (lowGroupedE16W_hz22 hx hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE16W_hz57 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B (189892644028141681 / 500000000000000000) (190192383498348727 / 500000000000000000) (((kdot ((728044459 / 1000000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x)) := badd (lowGroupedE16W_hz56 hx hc) (lowGroupedE16W_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16W_hz58 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B (176776695296636881 / 250000000000000000) (353765274914177413 / 500000000000000000) (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE16W_hz53 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE16W_hz59 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGroupedE16W_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE16W_hz60 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B (176776695296636881 / 250000000000000000) (28748435588634151 / 40000000000000000) ((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) := badd (lowGroupedE16W_hz58 hx hc) (lowGroupedE16W_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16W_hz61 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B 0 (59947894041409 / 50000000000000000) ((√(92 : ℝ)) * x) := bmul (lowGroupedE16W_hz3 hx hc) (lowGroupedE16W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16W_hz62 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B (176776695296636881 / 250000000000000000) (143981969519336391 / 200000000000000000) (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE16W_hz60 hx hc) (lowGroupedE16W_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16W_hz63 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B (499999999999999999 / 500000000000000000) (1018106270157175527 / 1000000000000000000) ((√(2 : ℝ)) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE16W_hz4 hx hc) (lowGroupedE16W_hz62 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16W_hz64 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B (499999999999999999 / 500000000000000000) (1018106270157175527 / 1000000000000000000) (neb x (1/2+√23*x)) := by
    convert (lowGroupedE16W_hz63 hx hc) using 1 <;>
      norm_num [neb] <;> ring

theorem lowGroupedE16W_hz65 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B (616267221306052721 / 1000000000000000000) (616753408581336869 / 1000000000000000000) (√(((kdot ((728044459 / 1000000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE16W_hz57 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE16W_hz66 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B (616267221306052721 / 1000000000000000000) (313966874234417909 / 500000000000000000) ((√(((kdot ((728044459 / 1000000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) := badd (lowGroupedE16W_hz65 hx hc) (lowGroupedE16W_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16W_hz67 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B (616267221306052721 / 1000000000000000000) (314566353174831999 / 500000000000000000) (((√(((kdot ((728044459 / 1000000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE16W_hz66 hx hc) (lowGroupedE16W_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16W_hz68 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B (871533462417001359 / 1000000000000000000) (889728005852184639 / 1000000000000000000) ((√(2 : ℝ)) * (((√(((kdot ((728044459 / 1000000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE16W_hz4 hx hc) (lowGroupedE16W_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16W_hz69 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B (871533462417001359 / 1000000000000000000) (889728005852184639 / 1000000000000000000) (neb x (kdot (728044459 / 1000000000)/2+√23*x)) := by
    convert (lowGroupedE16W_hz68 hx hc) using 1 <;>
      norm_num [neb] <;> ring

theorem lowGroupedE16W_hz70 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B 0 (7905694150420949 / 500000000000000000) ((√(2 : ℝ)) * (√x)) := bmul (lowGroupedE16W_hz4 hx hc) (lowGroupedE16W_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16W_hz71 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B 1 (507905694150420949 / 500000000000000000) (((√(2 : ℝ)) * (√x)) + (1 : ℝ)) := badd (lowGroupedE16W_hz70 hx hc) (bpoint (1 : ℝ)) (by norm_num) (by norm_num)

theorem lowGroupedE16W_hz72 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B 0 (107238052947636089 / 1000000000000000000) ((√(92 : ℝ)) * (√x)) := bmul (lowGroupedE16W_hz3 hx hc) (lowGroupedE16W_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16W_hz73 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B 1 (1123049441248477987 / 1000000000000000000) ((((√(2 : ℝ)) * (√x)) + (1 : ℝ)) + ((√(92 : ℝ)) * (√x))) := badd (lowGroupedE16W_hz71 hx hc) (lowGroupedE16W_hz72 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16W_hz74 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (12408060554915031 / 7812500000000000) ((√(2 : ℝ)) * ((((√(2 : ℝ)) * (√x)) + (1 : ℝ)) + ((√(92 : ℝ)) * (√x)))) := bmul (lowGroupedE16W_hz4 hx hc) (lowGroupedE16W_hz73 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16W_hz75 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (12408060554915031 / 7812500000000000) (np1 x) := by
    convert (lowGroupedE16W_hz74 hx hc) using 1 <;>
      norm_num [np1] <;> ring

theorem lowGroupedE16W_hz76 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B (11005876608998534131 / 1000000000000000000) (11005876608998534133 / 1000000000000000000) ((√(2 : ℝ)) + (√(92 : ℝ))) := badd (lowGroupedE16W_hz4 hx hc) (lowGroupedE16W_hz3 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16W_hz77 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B 0 (1375734576124817 / 1000000000000000000) (((√(2 : ℝ)) + (√(92 : ℝ))) * x) := bmul (lowGroupedE16W_hz76 hx hc) (lowGroupedE16W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16W_hz78 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B 1 (1001375734576124817 / 1000000000000000000) ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x)) := badd (bpoint (1 : ℝ)) (lowGroupedE16W_hz77 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16W_hz79 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (1416159144868876367 / 1000000000000000000) ((√(2 : ℝ)) * ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x))) := bmul (lowGroupedE16W_hz4 hx hc) (lowGroupedE16W_hz78 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16W_hz80 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B (1999999999999999997 / 1000000000000000000) (140574307399437647 / 62500000000000000) (((√(2 : ℝ)) * ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x))) * (np1 x)) := bmul (lowGroupedE16W_hz79 hx hc) (lowGroupedE16W_hz75 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16W_hz81 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B (1999999999999999997 / 1000000000000000000) (140574307399437647 / 62500000000000000) (ntf x (np1 x)) := by
    convert (lowGroupedE16W_hz80 hx hc) using 1 <;>
      norm_num [ntf] <;> ring

theorem lowGroupedE16W_hz82 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (1430024950673936947 / 1000000000000000000) (((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) := badd (lowGroupedE16W_hz70 hx hc) (lowGroupedE16W_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16W_hz83 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (384315750905393259 / 250000000000000000) ((((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) + ((√(92 : ℝ)) * (√x))) := badd (lowGroupedE16W_hz82 hx hc) (lowGroupedE16W_hz72 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16W_hz84 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B (1999999999999999997 / 1000000000000000000) (2174018188656028919 / 1000000000000000000) ((√(2 : ℝ)) * ((((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) + ((√(92 : ℝ)) * (√x)))) := bmul (lowGroupedE16W_hz4 hx hc) (lowGroupedE16W_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16W_hz85 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B (1999999999999999997 / 1000000000000000000) (2174018188656028919 / 1000000000000000000) (nz x) := by
    convert (lowGroupedE16W_hz84 hx hc) using 1 <;>
      norm_num [nz] <;> ring

theorem lowGroupedE16W_hz86 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B (582219876420280741 / 1000000000000000000) (31339748518833713 / 50000000000000000) (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE16W_hz55 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE16W_hz87 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B (582219876420280741 / 500000000000000000) (31339748518833713 / 25000000000000000) ((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) := bmul (bpoint (2 : ℝ)) (lowGroupedE16W_hz86 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16W_hz88 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B 0 (8505173090835039 / 500000000000000000) (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE16W_hz70 hx hc) (lowGroupedE16W_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16W_hz89 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B 0 (10661999431036871 / 500000000000000000) (((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE16W_hz87 hx hc) (lowGroupedE16W_hz88 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16W_hz90 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B 0 (144675938610129 / 500000000000000000) ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2) := bsq (lowGroupedE16W_hz88 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE16W_hz91 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B 0 (10806675369647 / 500000000000000) ((((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) + ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2)) := badd (lowGroupedE16W_hz89 hx hc) (lowGroupedE16W_hz90 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16W_hz92 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B 0 (10806675369647 / 250000000000000) ((2 : ℝ) * ((((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) + ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2))) := bmul (bpoint (2 : ℝ)) (lowGroupedE16W_hz91 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16W_hz93 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B 0 (10806675369647 / 250000000000000) (nrad x (kdot (nc1 x c)/2+√23*x)) := by
    convert (lowGroupedE16W_hz92 hx hc) using 1 <;>
      norm_num [nrad] <;> ring

theorem lowGroupedE16W_hz94 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B (999999999999999997 / 250000000000000000) (5058850790612887039 / 1000000000000000000) ((ntf x (np1 x))^2) := bsq (lowGroupedE16W_hz81 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE16W_hz95 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B 0 (632356348826611 / 1000000000000000000) (((ntf x (np1 x))^2) * x) := bmul (lowGroupedE16W_hz94 hx hc) (lowGroupedE16W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16W_hz96 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B (1999999999999999997 / 500000000000000000) (140574307399437647 / 31250000000000000) ((2 : ℝ) * (ntf x (np1 x))) := bmul (bpoint (2 : ℝ)) (lowGroupedE16W_hz81 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16W_hz97 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B (999999999999999997 / 125000000000000000) (611222202288202473 / 62500000000000000) (((2 : ℝ) * (ntf x (np1 x))) * (nz x)) := bmul (lowGroupedE16W_hz96 hx hc) (lowGroupedE16W_hz85 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16W_hz98 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B (199999999999999999 / 25000000000000000) (1991325301148468661 / 200000000000000000) ((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) := bmul (lowGroupedE16W_hz97 hx hc) (lowGroupedE16W_hz64 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16W_hz99 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B 0 (1244578313217793 / 1000000000000000000) (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x) := bmul (lowGroupedE16W_hz98 hx hc) (lowGroupedE16W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16W_hz100 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B 0 (469233665511101 / 250000000000000000) ((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) := badd (lowGroupedE16W_hz95 hx hc) (lowGroupedE16W_hz99 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16W_hz101 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B (249999999999999999 / 250000000000000000) (6478377358333473 / 6250000000000000) ((neb x (1/2+√23*x))^2) := bsq (lowGroupedE16W_hz64 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE16W_hz102 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B 0 (4480622146149193 / 100000000000000000) ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2)) := bmul (lowGroupedE16W_hz93 hx hc) (lowGroupedE16W_hz101 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16W_hz103 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B 0 (23341578061768167 / 500000000000000000) (((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) + ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2))) := badd (lowGroupedE16W_hz100 hx hc) (lowGroupedE16W_hz102 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16W_hz104 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B (169489992249423489 / 250000000000000000) (392871934889495963 / 500000000000000000) ((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bmul (bpoint (2 : ℝ)) (lowGroupedE16W_hz55 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16W_hz105 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B (2373658050351771 / 3125000000000000) (49475995274856569 / 62500000000000000) ((neb x (kdot (728044459 / 1000000000)/2+√23*x))^2) := bsq (lowGroupedE16W_hz69 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE16W_hz106 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B (1999999999999999997 / 1000000000000000000) (2522480094977037223 / 1000000000000000000) ((np1 x)^2) := bsq (lowGroupedE16W_hz75 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE16W_hz107 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B 0 (31531001187213 / 100000000000000000) (((np1 x)^2) * x) := bmul (lowGroupedE16W_hz106 hx hc) (lowGroupedE16W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16W_hz108 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B (2373658050351771 / 3125000000000000) (395965617204788617 / 500000000000000000) (((neb x (kdot (728044459 / 1000000000)/2+√23*x))^2) + (((np1 x)^2) * x)) := badd (lowGroupedE16W_hz105 hx hc) (lowGroupedE16W_hz107 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16W_hz109 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B (51495844423283627 / 100000000000000000) (124451022544767037 / 200000000000000000) (((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) * (((neb x (kdot (728044459 / 1000000000)/2+√23*x))^2) + (((np1 x)^2) * x))) := bmul (lowGroupedE16W_hz104 hx hc) (lowGroupedE16W_hz108 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16W_hz110 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B (51495844423283627 / 100000000000000000) (668938268847371519 / 1000000000000000000) ((((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) + ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2))) + (((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) * (((neb x (kdot (728044459 / 1000000000)/2+√23*x))^2) + (((np1 x)^2) * x)))) := badd (lowGroupedE16W_hz103 hx hc) (lowGroupedE16W_hz109 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16W_hz111 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) : B (51495844423283627 / 100000000000000000) (668938268847371519 / 1000000000000000000) (ne x (kdot (nc1 x c)/2+√23*x) (neb x (1/2+√23*x)) (neb x (kdot (728044459 / 1000000000)/2+√23*x)^2) (np1 x)) := by
    convert (lowGroupedE16W_hz110 hx hc) using 1 <;>
      norm_num [ne] <;> ring

theorem lowGroupedE16W {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (189056793 / 500000000) (728044459 / 1000000000) c) :
    ne x (kdot (nc1 x c)/2+√23*x) (neb x (1/2+√23*x))
      (neb x (kdot (728044459 / 1000000000)/2+√23*x)^2) (np1 x) ≤ (668938269 / 1000000000) :=
  (lowGroupedE16W_hz111 hx hc).2.trans (by norm_num)

theorem lowGroupedE16C_hz0 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B 0 (1 / 8000) x := hx

theorem lowGroupedE16C_hz1 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B (453378487 / 1000000000) (77554357 / 125000000) c := hc

theorem lowGroupedE16C_hz2 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B (6782329983125268139 / 500000000000000000) (13564659966250536279 / 1000000000000000000) (√(184 : ℝ)) := bsqrt (bpoint (184 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE16C_hz3 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE16C_hz4 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B (176776695296636881 / 125000000000000000) (1414213562373095049 / 1000000000000000000) (√(2 : ℝ)) := bsqrt (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE16C_hz5 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B 0 (847791247890659 / 500000000000000000) ((√(184 : ℝ)) * x) := bmul (lowGroupedE16C_hz2 hx hc) (lowGroupedE16C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16C_hz6 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B 1 (500847791247890659 / 500000000000000000) ((1 : ℝ) + ((√(184 : ℝ)) * x)) := badd (bpoint (1 : ℝ)) (lowGroupedE16C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16C_hz7 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B 1 (500847791247890659 / 500000000000000000) (nap x) := by
    convert (lowGroupedE16C_hz6 hx hc) using 1 <;>
      norm_num [nap] <;> ring

theorem lowGroupedE16C_hz8 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B 0 (1 / 64000000) (x^2) := bsq (lowGroupedE16C_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE16C_hz9 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B 0 (1 / 32000000) ((2 : ℝ) * (x^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE16C_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16C_hz10 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B (31999999 / 32000000) 1 ((1 : ℝ) - ((2 : ℝ) * (x^2))) := bsub (bpoint (1 : ℝ)) (lowGroupedE16C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16C_hz11 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B (999999984374999877 / 1000000000000000000) 1 (√((1 : ℝ) - ((2 : ℝ) * (x^2)))) := bsqrt (lowGroupedE16C_hz10 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE16C_hz12 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B (998304401879218559 / 1000000000000000000) 1 ((√((1 : ℝ) - ((2 : ℝ) * (x^2)))) - ((√(184 : ℝ)) * x)) := bsub (lowGroupedE16C_hz11 hx hc) (lowGroupedE16C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16C_hz13 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B (998304401879218559 / 1000000000000000000) 1 (nam x) := by
    convert (lowGroupedE16C_hz12 hx hc) using 1 <;>
      norm_num [nam] <;> ring

theorem lowGroupedE16C_hz14 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B (649781398185526109 / 1000000000000000000) (324890699093274419 / 500000000000000000) (kdot ((453378487 / 1000000000))) := by
    constructor
    · apply bkdot_lower (q := (306636606899792043 / 500000000000000000)) (a := (68765261663177513 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (122654642759916817 / 200000000000000000)) (a := (275061046651906803 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE16C_hz15 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B (205552052474409169 / 1000000000000000000) (205552052474409169 / 1000000000000000000) (((453378487 / 1000000000) : ℝ)^2) := bsq (bpoint ((453378487 / 1000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE16C_hz16 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B (794447947525590831 / 1000000000000000000) (794447947525590831 / 1000000000000000000) ((1 : ℝ) - (((453378487 / 1000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowGroupedE16C_hz15 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16C_hz17 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B (5570738097435419 / 6250000000000000) (891318095589667041 / 1000000000000000000) (√((1 : ℝ) - (((453378487 / 1000000000) : ℝ)^2))) := bsqrt (lowGroupedE16C_hz16 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE16C_hz18 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B (283715361560699969 / 1000000000000000000) (28371536156069997 / 100000000000000000) ((√((1 : ℝ) - (((453378487 / 1000000000) : ℝ)^2))) / Real.pi) := bdiv (lowGroupedE16C_hz17 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE16C_hz19 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B (73649226797524593 / 250000000000000000) (36824613398820257 / 125000000000000000) (((453378487 / 1000000000) : ℝ) * (kdot ((453378487 / 1000000000)))) := bmul (bpoint ((453378487 / 1000000000) : ℝ)) (lowGroupedE16C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16C_hz20 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B (578312268750798341 / 1000000000000000000) (289156134375631013 / 500000000000000000) (((√((1 : ℝ) - (((453378487 / 1000000000) : ℝ)^2))) / Real.pi) + (((453378487 / 1000000000) : ℝ) * (kdot ((453378487 / 1000000000))))) := badd (lowGroupedE16C_hz18 hx hc) (lowGroupedE16C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16C_hz21 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B (578312268750798341 / 1000000000000000000) (289156134375631013 / 500000000000000000) (kappa ((453378487 / 1000000000))) := by rw [kappa_eq]; exact (lowGroupedE16C_hz20 hx hc)

theorem lowGroupedE16C_hz22 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B (713043871779998631 / 1000000000000000000) (713043871779998643 / 1000000000000000000) (kdot ((77554357 / 125000000))) := by
    constructor
    · apply bkdot_lower (q := (241989976839096461 / 500000000000000000)) (a := (225374816079631763 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (483979953678192921 / 1000000000000000000)) (a := (450749632159263509 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE16C_hz23 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B (6014678289683449 / 15625000000000000) (6014678289683449 / 15625000000000000) (((77554357 / 125000000) : ℝ)^2) := bsq (bpoint ((77554357 / 125000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE16C_hz24 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B (9610321710316551 / 15625000000000000) (9610321710316551 / 15625000000000000) ((1 : ℝ) - (((77554357 / 125000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowGroupedE16C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16C_hz25 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B (12254031039772019 / 15625000000000000) (784257986545409217 / 1000000000000000000) (√((1 : ℝ) - (((77554357 / 125000000) : ℝ)^2))) := bsqrt (lowGroupedE16C_hz24 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE16C_hz26 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B (249637070435998043 / 1000000000000000000) (62409267608999511 / 250000000000000000) ((√((1 : ℝ) - (((77554357 / 125000000) : ℝ)^2))) / Real.pi) := bdiv (lowGroupedE16C_hz25 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE16C_hz27 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B (221198635954752957 / 500000000000000000) (221198635954752961 / 500000000000000000) (((77554357 / 125000000) : ℝ) * (kdot ((77554357 / 125000000)))) := bmul (bpoint ((77554357 / 125000000) : ℝ)) (lowGroupedE16C_hz22 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16C_hz28 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B (692034342345503957 / 1000000000000000000) (346017171172751983 / 500000000000000000) (((√((1 : ℝ) - (((77554357 / 125000000) : ℝ)^2))) / Real.pi) + (((77554357 / 125000000) : ℝ) * (kdot ((77554357 / 125000000))))) := badd (lowGroupedE16C_hz26 hx hc) (lowGroupedE16C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16C_hz29 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B (692034342345503957 / 1000000000000000000) (346017171172751983 / 500000000000000000) (kappa ((77554357 / 125000000))) := by rw [kappa_eq]; exact (lowGroupedE16C_hz28 hx hc)

theorem lowGroupedE16C_hz30 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B (578312268750798341 / 1000000000000000000) (346017171172751983 / 500000000000000000) (kappa c) := bkappa (lowGroupedE16C_hz1 hx hc) (by norm_num) (by norm_num) (lowGroupedE16C_hz21 hx hc).1 (lowGroupedE16C_hz29 hx hc).2

theorem lowGroupedE16C_hz31 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B (153982828827248017 / 500000000000000000) (421687731249201659 / 1000000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (lowGroupedE16C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16C_hz32 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B (153982828827248017 / 250000000000000000) (421687731249201659 / 500000000000000000) ((2 : ℝ) * ((1 : ℝ) - (kappa c))) := bmul (bpoint (2 : ℝ)) (lowGroupedE16C_hz31 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16C_hz33 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B 0 (1 / 8000000) ((8 : ℝ) * (x^2)) := bmul (bpoint (8 : ℝ)) (lowGroupedE16C_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16C_hz34 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B (153982797577248017 / 250000000000000000) (421687731249201659 / 500000000000000000) (((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2))) := bsub (lowGroupedE16C_hz32 hx hc) (lowGroupedE16C_hz33 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16C_hz35 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B (784812837757507677 / 1000000000000000000) (918354758521130177 / 1000000000000000000) (√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) := bsqrt (lowGroupedE16C_hz34 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE16C_hz36 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B (6782329983125268139 / 250000000000000000) (13564659966250536279 / 500000000000000000) ((2 : ℝ) * (√(184 : ℝ))) := bmul (bpoint (2 : ℝ)) (lowGroupedE16C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16C_hz37 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B 0 (678232998312527 / 200000000000000000) (((2 : ℝ) * (√(184 : ℝ))) * x) := bmul (lowGroupedE16C_hz36 hx hc) (lowGroupedE16C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16C_hz38 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B (390710836382972521 / 500000000000000000) (918354758521130177 / 1000000000000000000) ((√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) - (((2 : ℝ) * (√(184 : ℝ))) * x)) := bsub (lowGroupedE16C_hz35 hx hc) (lowGroupedE16C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16C_hz39 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B (390710836382972521 / 500000000000000000) (918354758521130177 / 1000000000000000000) (ndm x c) := by
    convert (lowGroupedE16C_hz38 hx hc) using 1 <;>
      norm_num [ndm] <;> ring

theorem lowGroupedE16C_hz40 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B 1 (1003394039991562637 / 1000000000000000000) ((nap x)^2) := bsq (lowGroupedE16C_hz7 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE16C_hz41 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B 2 (1003394039991562637 / 500000000000000000) ((2 : ℝ) * ((nap x)^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE16C_hz40 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16C_hz42 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B (122123966133665539 / 200000000000000000) (21084386562460083 / 25000000000000000) ((ndm x c)^2) := bsq (lowGroupedE16C_hz39 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE16C_hz43 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B (28915613437539917 / 25000000000000000) (1396168249314797579 / 1000000000000000000) (((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) := bsub (lowGroupedE16C_hz41 hx hc) (lowGroupedE16C_hz42 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16C_hz44 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B (199322335762284863 / 200000000000000000) 1 ((nam x)^2) := bsq (lowGroupedE16C_hz13 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE16C_hz45 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B (199322335762284863 / 100000000000000000) 2 ((2 : ℝ) * ((nam x)^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE16C_hz44 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16C_hz46 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B (28915613437539917 / 50000000000000000) (350228749822571587 / 500000000000000000) ((((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) / ((2 : ℝ) * ((nam x)^2))) := bdiv (lowGroupedE16C_hz43 hx hc) (lowGroupedE16C_hz45 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE16C_hz47 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B (28915613437539917 / 50000000000000000) (350228749822571587 / 500000000000000000) (nc1 x c) := by
    convert (lowGroupedE16C_hz46 hx hc) using 1 <;>
      norm_num [nc1] <;> ring

theorem lowGroupedE16C_hz48 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B (696288466446259801 / 1000000000000000000) (348144233223130019 / 500000000000000000) (kdot ((28915613437539917 / 50000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (103378211002206841 / 200000000000000000)) (a := (477068961311460099 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (129222763752758551 / 250000000000000000)) (a := (29816810081966233 / 62500000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE16C_hz49 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B (747020671083473721 / 1000000000000000000) (747020671083473723 / 1000000000000000000) (kdot ((350228749822571587 / 500000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (419707117721801363 / 1000000000000000000)) (a := (99344750154279363 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (209853558860900681 / 500000000000000000)) (a := (7947580012342349 / 20000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE16C_hz50 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B (696288466446259801 / 1000000000000000000) (747020671083473723 / 1000000000000000000) (kdot (nc1 x c)) := bkdot (lowGroupedE16C_hz47 hx hc) (lowGroupedE16C_hz48 hx hc).1 (lowGroupedE16C_hz49 hx hc).2

theorem lowGroupedE16C_hz51 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE16C_hz52 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B 0 (59947894041409 / 100000000000000000) ((√(23 : ℝ)) * x) := bmul (lowGroupedE16C_hz51 hx hc) (lowGroupedE16C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16C_hz53 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B (1 / 2) (50059947894041409 / 100000000000000000) (((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)) := badd (bpoint ((1 / 2) : ℝ)) (lowGroupedE16C_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16C_hz54 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B (3481442332231299 / 10000000000000000) (186755167770868431 / 500000000000000000) ((kdot (nc1 x c)) / (2 : ℝ)) := bdiv (lowGroupedE16C_hz50 hx hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE16C_hz55 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B (3481442332231299 / 10000000000000000) (46763726810268869 / 125000000000000000) (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)) := badd (lowGroupedE16C_hz54 hx hc) (lowGroupedE16C_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16C_hz56 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B (71304387177999863 / 200000000000000000) (178260967944999661 / 500000000000000000) ((kdot ((77554357 / 125000000))) / (2 : ℝ)) := bdiv (lowGroupedE16C_hz22 hx hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE16C_hz57 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B (71304387177999863 / 200000000000000000) (89280353707603353 / 250000000000000000) (((kdot ((77554357 / 125000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x)) := badd (lowGroupedE16C_hz56 hx hc) (lowGroupedE16C_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16C_hz58 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B (176776695296636881 / 250000000000000000) (353765274914177413 / 500000000000000000) (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE16C_hz53 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE16C_hz59 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGroupedE16C_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE16C_hz60 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B (176776695296636881 / 250000000000000000) (28748435588634151 / 40000000000000000) ((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) := badd (lowGroupedE16C_hz58 hx hc) (lowGroupedE16C_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16C_hz61 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B 0 (59947894041409 / 50000000000000000) ((√(92 : ℝ)) * x) := bmul (lowGroupedE16C_hz3 hx hc) (lowGroupedE16C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16C_hz62 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B (176776695296636881 / 250000000000000000) (143981969519336391 / 200000000000000000) (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE16C_hz60 hx hc) (lowGroupedE16C_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16C_hz63 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B (499999999999999999 / 500000000000000000) (1018106270157175527 / 1000000000000000000) ((√(2 : ℝ)) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE16C_hz4 hx hc) (lowGroupedE16C_hz62 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16C_hz64 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B (499999999999999999 / 500000000000000000) (1018106270157175527 / 1000000000000000000) (neb x (1/2+√23*x)) := by
    convert (lowGroupedE16C_hz63 hx hc) using 1 <;>
      norm_num [neb] <;> ring

theorem lowGroupedE16C_hz65 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B (597094578680797699 / 1000000000000000000) (597596364472219169 / 1000000000000000000) (√(((kdot ((77554357 / 125000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE16C_hz57 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE16C_hz66 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B (597094578680797699 / 1000000000000000000) (304388352179859059 / 500000000000000000) ((√(((kdot ((77554357 / 125000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) := badd (lowGroupedE16C_hz65 hx hc) (lowGroupedE16C_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16C_hz67 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B (597094578680797699 / 1000000000000000000) (304987831120273149 / 500000000000000000) (((√(((kdot ((77554357 / 125000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE16C_hz66 hx hc) (lowGroupedE16C_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16C_hz68 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B (168883850237966641 / 200000000000000000) (862635854258090781 / 1000000000000000000) ((√(2 : ℝ)) * (((√(((kdot ((77554357 / 125000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE16C_hz4 hx hc) (lowGroupedE16C_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16C_hz69 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B (168883850237966641 / 200000000000000000) (862635854258090781 / 1000000000000000000) (neb x (kdot (77554357 / 125000000)/2+√23*x)) := by
    convert (lowGroupedE16C_hz68 hx hc) using 1 <;>
      norm_num [neb] <;> ring

theorem lowGroupedE16C_hz70 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B 0 (7905694150420949 / 500000000000000000) ((√(2 : ℝ)) * (√x)) := bmul (lowGroupedE16C_hz4 hx hc) (lowGroupedE16C_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16C_hz71 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B 1 (507905694150420949 / 500000000000000000) (((√(2 : ℝ)) * (√x)) + (1 : ℝ)) := badd (lowGroupedE16C_hz70 hx hc) (bpoint (1 : ℝ)) (by norm_num) (by norm_num)

theorem lowGroupedE16C_hz72 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B 0 (107238052947636089 / 1000000000000000000) ((√(92 : ℝ)) * (√x)) := bmul (lowGroupedE16C_hz3 hx hc) (lowGroupedE16C_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16C_hz73 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B 1 (1123049441248477987 / 1000000000000000000) ((((√(2 : ℝ)) * (√x)) + (1 : ℝ)) + ((√(92 : ℝ)) * (√x))) := badd (lowGroupedE16C_hz71 hx hc) (lowGroupedE16C_hz72 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16C_hz74 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B (176776695296636881 / 125000000000000000) (12408060554915031 / 7812500000000000) ((√(2 : ℝ)) * ((((√(2 : ℝ)) * (√x)) + (1 : ℝ)) + ((√(92 : ℝ)) * (√x)))) := bmul (lowGroupedE16C_hz4 hx hc) (lowGroupedE16C_hz73 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16C_hz75 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B (176776695296636881 / 125000000000000000) (12408060554915031 / 7812500000000000) (np1 x) := by
    convert (lowGroupedE16C_hz74 hx hc) using 1 <;>
      norm_num [np1] <;> ring

theorem lowGroupedE16C_hz76 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B (11005876608998534131 / 1000000000000000000) (11005876608998534133 / 1000000000000000000) ((√(2 : ℝ)) + (√(92 : ℝ))) := badd (lowGroupedE16C_hz4 hx hc) (lowGroupedE16C_hz3 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16C_hz77 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B 0 (1375734576124817 / 1000000000000000000) (((√(2 : ℝ)) + (√(92 : ℝ))) * x) := bmul (lowGroupedE16C_hz76 hx hc) (lowGroupedE16C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16C_hz78 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B 1 (1001375734576124817 / 1000000000000000000) ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x)) := badd (bpoint (1 : ℝ)) (lowGroupedE16C_hz77 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16C_hz79 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B (176776695296636881 / 125000000000000000) (1416159144868876367 / 1000000000000000000) ((√(2 : ℝ)) * ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x))) := bmul (lowGroupedE16C_hz4 hx hc) (lowGroupedE16C_hz78 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16C_hz80 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B (1999999999999999997 / 1000000000000000000) (140574307399437647 / 62500000000000000) (((√(2 : ℝ)) * ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x))) * (np1 x)) := bmul (lowGroupedE16C_hz79 hx hc) (lowGroupedE16C_hz75 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16C_hz81 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B (1999999999999999997 / 1000000000000000000) (140574307399437647 / 62500000000000000) (ntf x (np1 x)) := by
    convert (lowGroupedE16C_hz80 hx hc) using 1 <;>
      norm_num [ntf] <;> ring

theorem lowGroupedE16C_hz82 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B (176776695296636881 / 125000000000000000) (1430024950673936947 / 1000000000000000000) (((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) := badd (lowGroupedE16C_hz70 hx hc) (lowGroupedE16C_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16C_hz83 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B (176776695296636881 / 125000000000000000) (384315750905393259 / 250000000000000000) ((((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) + ((√(92 : ℝ)) * (√x))) := badd (lowGroupedE16C_hz82 hx hc) (lowGroupedE16C_hz72 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16C_hz84 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B (1999999999999999997 / 1000000000000000000) (2174018188656028919 / 1000000000000000000) ((√(2 : ℝ)) * ((((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) + ((√(92 : ℝ)) * (√x)))) := bmul (lowGroupedE16C_hz4 hx hc) (lowGroupedE16C_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16C_hz85 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B (1999999999999999997 / 1000000000000000000) (2174018188656028919 / 1000000000000000000) (nz x) := by
    convert (lowGroupedE16C_hz84 hx hc) using 1 <;>
      norm_num [nz] <;> ring

theorem lowGroupedE16C_hz86 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B (118007496918311067 / 200000000000000000) (61164517040695331 / 100000000000000000) (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE16C_hz55 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE16C_hz87 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B (118007496918311067 / 100000000000000000) (61164517040695331 / 50000000000000000) ((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) := bmul (bpoint (2 : ℝ)) (lowGroupedE16C_hz86 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16C_hz88 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B 0 (8505173090835039 / 500000000000000000) (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE16C_hz70 hx hc) (lowGroupedE16C_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16C_hz89 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B 0 (832343687117509 / 40000000000000000) (((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE16C_hz87 hx hc) (lowGroupedE16C_hz88 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16C_hz90 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B 0 (144675938610129 / 500000000000000000) ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2) := bsq (lowGroupedE16C_hz88 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE16C_hz91 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B 0 (21097944055157983 / 1000000000000000000) ((((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) + ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2)) := badd (lowGroupedE16C_hz89 hx hc) (lowGroupedE16C_hz90 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16C_hz92 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B 0 (21097944055157983 / 500000000000000000) ((2 : ℝ) * ((((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) + ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2))) := bmul (bpoint (2 : ℝ)) (lowGroupedE16C_hz91 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16C_hz93 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B 0 (21097944055157983 / 500000000000000000) (nrad x (kdot (nc1 x c)/2+√23*x)) := by
    convert (lowGroupedE16C_hz92 hx hc) using 1 <;>
      norm_num [nrad] <;> ring

theorem lowGroupedE16C_hz94 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B (999999999999999997 / 250000000000000000) (5058850790612887039 / 1000000000000000000) ((ntf x (np1 x))^2) := bsq (lowGroupedE16C_hz81 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE16C_hz95 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B 0 (632356348826611 / 1000000000000000000) (((ntf x (np1 x))^2) * x) := bmul (lowGroupedE16C_hz94 hx hc) (lowGroupedE16C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16C_hz96 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B (1999999999999999997 / 500000000000000000) (140574307399437647 / 31250000000000000) ((2 : ℝ) * (ntf x (np1 x))) := bmul (bpoint (2 : ℝ)) (lowGroupedE16C_hz81 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16C_hz97 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B (999999999999999997 / 125000000000000000) (611222202288202473 / 62500000000000000) (((2 : ℝ) * (ntf x (np1 x))) * (nz x)) := bmul (lowGroupedE16C_hz96 hx hc) (lowGroupedE16C_hz85 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16C_hz98 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B (199999999999999999 / 25000000000000000) (1991325301148468661 / 200000000000000000) ((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) := bmul (lowGroupedE16C_hz97 hx hc) (lowGroupedE16C_hz64 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16C_hz99 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B 0 (1244578313217793 / 1000000000000000000) (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x) := bmul (lowGroupedE16C_hz98 hx hc) (lowGroupedE16C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16C_hz100 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B 0 (469233665511101 / 250000000000000000) ((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) := badd (lowGroupedE16C_hz95 hx hc) (lowGroupedE16C_hz99 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16C_hz101 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B (249999999999999999 / 250000000000000000) (6478377358333473 / 6250000000000000) ((neb x (1/2+√23*x))^2) := bsq (lowGroupedE16C_hz64 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE16C_hz102 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B 0 (5467217722972871 / 125000000000000000) ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2)) := bmul (lowGroupedE16C_hz93 hx hc) (lowGroupedE16C_hz101 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16C_hz103 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B 0 (11403669111456843 / 250000000000000000) (((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) + ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2))) := badd (lowGroupedE16C_hz100 hx hc) (lowGroupedE16C_hz102 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16C_hz104 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B (3481442332231299 / 5000000000000000) (46763726810268869 / 62500000000000000) ((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bmul (bpoint (2 : ℝ)) (lowGroupedE16C_hz55 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16C_hz105 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B (356521935889999313 / 500000000000000000) (744140617051586039 / 1000000000000000000) ((neb x (kdot (77554357 / 125000000)/2+√23*x))^2) := bsq (lowGroupedE16C_hz69 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE16C_hz106 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B (1999999999999999997 / 1000000000000000000) (2522480094977037223 / 1000000000000000000) ((np1 x)^2) := bsq (lowGroupedE16C_hz75 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE16C_hz107 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B 0 (31531001187213 / 100000000000000000) (((np1 x)^2) * x) := bmul (lowGroupedE16C_hz106 hx hc) (lowGroupedE16C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16C_hz108 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B (356521935889999313 / 500000000000000000) (744455927063458169 / 1000000000000000000) (((neb x (kdot (77554357 / 125000000)/2+√23*x))^2) + (((np1 x)^2) * x)) := badd (lowGroupedE16C_hz105 hx hc) (lowGroupedE16C_hz107 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16C_hz109 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B (124121055997649687 / 250000000000000000) (69627067190962009 / 125000000000000000) (((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) * (((neb x (kdot (77554357 / 125000000)/2+√23*x))^2) + (((np1 x)^2) * x))) := bmul (lowGroupedE16C_hz104 hx hc) (lowGroupedE16C_hz108 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16C_hz110 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B (124121055997649687 / 250000000000000000) (150657803493380861 / 250000000000000000) ((((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) + ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2))) + (((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) * (((neb x (kdot (77554357 / 125000000)/2+√23*x))^2) + (((np1 x)^2) * x)))) := badd (lowGroupedE16C_hz103 hx hc) (lowGroupedE16C_hz109 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE16C_hz111 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) : B (124121055997649687 / 250000000000000000) (150657803493380861 / 250000000000000000) (ne x (kdot (nc1 x c)/2+√23*x) (neb x (1/2+√23*x)) (neb x (kdot (77554357 / 125000000)/2+√23*x)^2) (np1 x)) := by
    convert (lowGroupedE16C_hz110 hx hc) using 1 <;>
      norm_num [ne] <;> ring

theorem lowGroupedE16C {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (453378487 / 1000000000) (77554357 / 125000000) c) :
    ne x (kdot (nc1 x c)/2+√23*x) (neb x (1/2+√23*x))
      (neb x (kdot (77554357 / 125000000)/2+√23*x)^2) (np1 x) ≤ (301315607 / 500000000) :=
  (lowGroupedE16C_hz111 hx hc).2.trans (by norm_num)

theorem lowGroupedE18W_hz0 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B 0 (1 / 8000) x := hx

theorem lowGroupedE18W_hz1 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B (75418381 / 200000000) (727125683 / 1000000000) c := hc

theorem lowGroupedE18W_hz2 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B (6782329983125268139 / 500000000000000000) (13564659966250536279 / 1000000000000000000) (√(184 : ℝ)) := bsqrt (bpoint (184 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE18W_hz3 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE18W_hz4 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (1414213562373095049 / 1000000000000000000) (√(2 : ℝ)) := bsqrt (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE18W_hz5 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B 0 (847791247890659 / 500000000000000000) ((√(184 : ℝ)) * x) := bmul (lowGroupedE18W_hz2 hx hc) (lowGroupedE18W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18W_hz6 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B 1 (500847791247890659 / 500000000000000000) ((1 : ℝ) + ((√(184 : ℝ)) * x)) := badd (bpoint (1 : ℝ)) (lowGroupedE18W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18W_hz7 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B 1 (500847791247890659 / 500000000000000000) (nap x) := by
    convert (lowGroupedE18W_hz6 hx hc) using 1 <;>
      norm_num [nap] <;> ring

theorem lowGroupedE18W_hz8 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B 0 (1 / 64000000) (x^2) := bsq (lowGroupedE18W_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE18W_hz9 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B 0 (1 / 32000000) ((2 : ℝ) * (x^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE18W_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18W_hz10 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B (31999999 / 32000000) 1 ((1 : ℝ) - ((2 : ℝ) * (x^2))) := bsub (bpoint (1 : ℝ)) (lowGroupedE18W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18W_hz11 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B (999999984374999877 / 1000000000000000000) 1 (√((1 : ℝ) - ((2 : ℝ) * (x^2)))) := bsqrt (lowGroupedE18W_hz10 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE18W_hz12 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B (998304401879218559 / 1000000000000000000) 1 ((√((1 : ℝ) - ((2 : ℝ) * (x^2)))) - ((√(184 : ℝ)) * x)) := bsub (lowGroupedE18W_hz11 hx hc) (lowGroupedE18W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18W_hz13 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B (998304401879218559 / 1000000000000000000) 1 (nam x) := by
    convert (lowGroupedE18W_hz12 hx hc) using 1 <;>
      norm_num [nam] <;> ring

theorem lowGroupedE18W_hz14 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B (311537956887682679 / 500000000000000000) (77884489233681007 / 125000000000000000) (kdot ((75418381 / 200000000))) := by
    constructor
    · apply bkdot_lower (q := (672559210660658517 / 1000000000000000000)) (a := (592070970122178987 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (168139802665164629 / 250000000000000000)) (a := (592070969974394233 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE18W_hz15 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B (5687932192661161 / 40000000000000000) (5687932192661161 / 40000000000000000) (((75418381 / 200000000) : ℝ)^2) := bsq (bpoint ((75418381 / 200000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE18W_hz16 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B (34312067807338839 / 40000000000000000) (34312067807338839 / 40000000000000000) ((1 : ℝ) - (((75418381 / 200000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowGroupedE18W_hz15 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18W_hz17 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B (185235168926796509 / 200000000000000000) (463087922316991273 / 500000000000000000) (√((1 : ℝ) - (((75418381 / 200000000) : ℝ)^2))) := bsqrt (lowGroupedE18W_hz16 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE18W_hz18 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B (36851365961452397 / 125000000000000000) (294810927691619177 / 1000000000000000000) ((√((1 : ℝ) - (((75418381 / 200000000) : ℝ)^2))) / Real.pi) := bdiv (lowGroupedE18W_hz17 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE18W_hz19 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B (29369610410646033 / 125000000000000000) (234956883320646089 / 1000000000000000000) (((75418381 / 200000000) : ℝ) * (kdot ((75418381 / 200000000)))) := bmul (bpoint ((75418381 / 200000000) : ℝ)) (lowGroupedE18W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18W_hz20 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B (6622097637209843 / 12500000000000000) (264883905506132633 / 500000000000000000) (((√((1 : ℝ) - (((75418381 / 200000000) : ℝ)^2))) / Real.pi) + (((75418381 / 200000000) : ℝ) * (kdot ((75418381 / 200000000))))) := badd (lowGroupedE18W_hz18 hx hc) (lowGroupedE18W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18W_hz21 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B (6622097637209843 / 12500000000000000) (264883905506132633 / 500000000000000000) (kappa ((75418381 / 200000000))) := by rw [kappa_eq]; exact (lowGroupedE18W_hz20 hx hc)

theorem lowGroupedE18W_hz22 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B (759144266880148171 / 1000000000000000000) (759144266880148173 / 1000000000000000000) (kdot ((727125683 / 1000000000))) := by
    constructor
    · apply bkdot_lower (q := (49685466601372897 / 125000000000000000)) (a := (189167650436077589 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (15899349312439327 / 40000000000000000)) (a := (47291912609019397 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE18W_hz23 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B (528711758878216489 / 1000000000000000000) (528711758878216489 / 1000000000000000000) (((727125683 / 1000000000) : ℝ)^2) := bsq (bpoint ((727125683 / 1000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE18W_hz24 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B (471288241121783511 / 1000000000000000000) (471288241121783511 / 1000000000000000000) ((1 : ℝ) - (((727125683 / 1000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowGroupedE18W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18W_hz25 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B (343252181756279413 / 500000000000000000) (686504363512558827 / 1000000000000000000) (√((1 : ℝ) - (((727125683 / 1000000000) : ℝ)^2))) := bsqrt (lowGroupedE18W_hz24 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE18W_hz26 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B (218521125814358257 / 1000000000000000000) (109260562907179129 / 500000000000000000) ((√((1 : ℝ) - (((727125683 / 1000000000) : ℝ)^2))) / Real.pi) := bdiv (lowGroupedE18W_hz25 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE18W_hz27 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B (551993293550762017 / 1000000000000000000) (27599664677538101 / 50000000000000000) (((727125683 / 1000000000) : ℝ) * (kdot ((727125683 / 1000000000)))) := bmul (bpoint ((727125683 / 1000000000) : ℝ)) (lowGroupedE18W_hz22 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18W_hz28 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B (385257209682560137 / 500000000000000000) (385257209682560139 / 500000000000000000) (((√((1 : ℝ) - (((727125683 / 1000000000) : ℝ)^2))) / Real.pi) + (((727125683 / 1000000000) : ℝ) * (kdot ((727125683 / 1000000000))))) := badd (lowGroupedE18W_hz26 hx hc) (lowGroupedE18W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18W_hz29 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B (385257209682560137 / 500000000000000000) (385257209682560139 / 500000000000000000) (kappa ((727125683 / 1000000000))) := by rw [kappa_eq]; exact (lowGroupedE18W_hz28 hx hc)

theorem lowGroupedE18W_hz30 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B (6622097637209843 / 12500000000000000) (385257209682560139 / 500000000000000000) (kappa c) := bkappa (lowGroupedE18W_hz1 hx hc) (by norm_num) (by norm_num) (lowGroupedE18W_hz21 hx hc).1 (lowGroupedE18W_hz29 hx hc).2

theorem lowGroupedE18W_hz31 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B (114742790317439861 / 500000000000000000) (5877902362790157 / 12500000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (lowGroupedE18W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18W_hz32 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B (114742790317439861 / 250000000000000000) (5877902362790157 / 6250000000000000) ((2 : ℝ) * ((1 : ℝ) - (kappa c))) := bmul (bpoint (2 : ℝ)) (lowGroupedE18W_hz31 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18W_hz33 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B 0 (1 / 8000000) ((8 : ℝ) * (x^2)) := bmul (bpoint (8 : ℝ)) (lowGroupedE18W_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18W_hz34 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B (114742759067439861 / 250000000000000000) (5877902362790157 / 6250000000000000) (((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2))) := bsub (lowGroupedE18W_hz32 hx hc) (lowGroupedE18W_hz33 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18W_hz35 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B (677474011508751119 / 1000000000000000000) (484887713302375069 / 500000000000000000) (√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) := bsqrt (lowGroupedE18W_hz34 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE18W_hz36 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B (6782329983125268139 / 250000000000000000) (13564659966250536279 / 500000000000000000) ((2 : ℝ) * (√(184 : ℝ))) := bmul (bpoint (2 : ℝ)) (lowGroupedE18W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18W_hz37 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B 0 (678232998312527 / 200000000000000000) (((2 : ℝ) * (√(184 : ℝ))) * x) := bmul (lowGroupedE18W_hz36 hx hc) (lowGroupedE18W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18W_hz38 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B (168520711629297121 / 250000000000000000) (484887713302375069 / 500000000000000000) ((√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) - (((2 : ℝ) * (√(184 : ℝ))) * x)) := bsub (lowGroupedE18W_hz35 hx hc) (lowGroupedE18W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18W_hz39 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B (168520711629297121 / 250000000000000000) (484887713302375069 / 500000000000000000) (ndm x c) := by
    convert (lowGroupedE18W_hz38 hx hc) using 1 <;>
      norm_num [ndm] <;> ring

theorem lowGroupedE18W_hz40 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B 1 (1003394039991562637 / 1000000000000000000) ((nap x)^2) := bsq (lowGroupedE18W_hz7 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE18W_hz41 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B 2 (1003394039991562637 / 500000000000000000) ((2 : ℝ) * ((nap x)^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE18W_hz40 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18W_hz42 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B (227193841984357743 / 500000000000000000) (470232189023212561 / 500000000000000000) ((ndm x c)^2) := bsq (lowGroupedE18W_hz39 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE18W_hz43 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B (529767810976787439 / 500000000000000000) (388100099003602447 / 250000000000000000) (((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) := bsub (lowGroupedE18W_hz41 hx hc) (lowGroupedE18W_hz42 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18W_hz44 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B (199322335762284863 / 200000000000000000) 1 ((nam x)^2) := bsq (lowGroupedE18W_hz13 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE18W_hz45 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B (199322335762284863 / 100000000000000000) 2 ((2 : ℝ) * ((nam x)^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE18W_hz44 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18W_hz46 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B (529767810976787439 / 1000000000000000000) (778839155219326927 / 1000000000000000000) ((((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) / ((2 : ℝ) * ((nam x)^2))) := bdiv (lowGroupedE18W_hz43 hx hc) (lowGroupedE18W_hz45 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE18W_hz47 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B (529767810976787439 / 1000000000000000000) (778839155219326927 / 1000000000000000000) (nc1 x c) := by
    convert (lowGroupedE18W_hz46 hx hc) using 1 <;>
      norm_num [nc1] <;> ring

theorem lowGroupedE18W_hz48 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B (677720933856275897 / 1000000000000000000) (338860466928141597 / 500000000000000000) (kdot ((529767810976787439 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (34651611414744581 / 62500000000000000)) (a := (126558693325362837 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (110885156527182659 / 200000000000000000)) (a := (506234773301439887 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE18W_hz49 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B (392095589130477599 / 500000000000000000) (490119486413097 / 625000000000000) (kdot ((778839155219326927 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (352602818823052489 / 1000000000000000000)) (a := (10593490764925819 / 31250000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (44075352352881561 / 125000000000000000)) (a := (169495852238813103 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE18W_hz50 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B (677720933856275897 / 1000000000000000000) (490119486413097 / 625000000000000) (kdot (nc1 x c)) := bkdot (lowGroupedE18W_hz47 hx hc) (lowGroupedE18W_hz48 hx hc).1 (lowGroupedE18W_hz49 hx hc).2

theorem lowGroupedE18W_hz51 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE18W_hz52 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B 0 (59947894041409 / 100000000000000000) ((√(23 : ℝ)) * x) := bmul (lowGroupedE18W_hz51 hx hc) (lowGroupedE18W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18W_hz53 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B (1 / 2) (50059947894041409 / 100000000000000000) (((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)) := badd (bpoint ((1 / 2) : ℝ)) (lowGroupedE18W_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18W_hz54 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B (84715116732034487 / 250000000000000000) (490119486413097 / 1250000000000000) ((kdot (nc1 x c)) / (2 : ℝ)) := bdiv (lowGroupedE18W_hz50 hx hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE18W_hz55 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B (84715116732034487 / 250000000000000000) (39269506807089169 / 100000000000000000) (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)) := badd (lowGroupedE18W_hz54 hx hc) (lowGroupedE18W_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18W_hz56 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B (75914426688014817 / 200000000000000000) (379572133440074087 / 1000000000000000000) ((kdot ((727125683 / 1000000000))) / (2 : ℝ)) := bdiv (lowGroupedE18W_hz22 hx hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE18W_hz57 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B (75914426688014817 / 200000000000000000) (380171612380488177 / 1000000000000000000) (((kdot ((727125683 / 1000000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x)) := badd (lowGroupedE18W_hz56 hx hc) (lowGroupedE18W_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18W_hz58 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B (176776695296636881 / 250000000000000000) (353765274914177413 / 500000000000000000) (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE18W_hz53 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE18W_hz59 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGroupedE18W_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE18W_hz60 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B (176776695296636881 / 250000000000000000) (28748435588634151 / 40000000000000000) ((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) := badd (lowGroupedE18W_hz58 hx hc) (lowGroupedE18W_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18W_hz61 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B 0 (59947894041409 / 50000000000000000) ((√(92 : ℝ)) * x) := bmul (lowGroupedE18W_hz3 hx hc) (lowGroupedE18W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18W_hz62 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B (176776695296636881 / 250000000000000000) (143981969519336391 / 200000000000000000) (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE18W_hz60 hx hc) (lowGroupedE18W_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18W_hz63 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B (499999999999999999 / 500000000000000000) (1018106270157175527 / 1000000000000000000) ((√(2 : ℝ)) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE18W_hz4 hx hc) (lowGroupedE18W_hz62 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18W_hz64 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B (499999999999999999 / 500000000000000000) (1018106270157175527 / 1000000000000000000) (neb x (1/2+√23*x)) := by
    convert (lowGroupedE18W_hz63 hx hc) using 1 <;>
      norm_num [neb] <;> ring

theorem lowGroupedE18W_hz65 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B (308047128472281853 / 500000000000000000) (9634071571969461 / 15625000000000000) (√(((kdot ((727125683 / 1000000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE18W_hz57 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE18W_hz66 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B (308047128472281853 / 500000000000000000) (627760920493544453 / 1000000000000000000) ((√(((kdot ((727125683 / 1000000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) := badd (lowGroupedE18W_hz65 hx hc) (lowGroupedE18W_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18W_hz67 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B (308047128472281853 / 500000000000000000) (628959878374372633 / 1000000000000000000) (((√(((kdot ((727125683 / 1000000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE18W_hz66 hx hc) (lowGroupedE18W_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18W_hz68 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B (871288853871176391 / 1000000000000000000) (222370897546392527 / 250000000000000000) ((√(2 : ℝ)) * (((√(((kdot ((727125683 / 1000000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE18W_hz4 hx hc) (lowGroupedE18W_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18W_hz69 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B (871288853871176391 / 1000000000000000000) (222370897546392527 / 250000000000000000) (neb x (kdot (727125683 / 1000000000)/2+√23*x)) := by
    convert (lowGroupedE18W_hz68 hx hc) using 1 <;>
      norm_num [neb] <;> ring

theorem lowGroupedE18W_hz70 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B 0 (7905694150420949 / 500000000000000000) ((√(2 : ℝ)) * (√x)) := bmul (lowGroupedE18W_hz4 hx hc) (lowGroupedE18W_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18W_hz71 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B 1 (507905694150420949 / 500000000000000000) (((√(2 : ℝ)) * (√x)) + (1 : ℝ)) := badd (lowGroupedE18W_hz70 hx hc) (bpoint (1 : ℝ)) (by norm_num) (by norm_num)

theorem lowGroupedE18W_hz72 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B 0 (107238052947636089 / 1000000000000000000) ((√(92 : ℝ)) * (√x)) := bmul (lowGroupedE18W_hz3 hx hc) (lowGroupedE18W_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18W_hz73 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B 1 (1123049441248477987 / 1000000000000000000) ((((√(2 : ℝ)) * (√x)) + (1 : ℝ)) + ((√(92 : ℝ)) * (√x))) := badd (lowGroupedE18W_hz71 hx hc) (lowGroupedE18W_hz72 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18W_hz74 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (12408060554915031 / 7812500000000000) ((√(2 : ℝ)) * ((((√(2 : ℝ)) * (√x)) + (1 : ℝ)) + ((√(92 : ℝ)) * (√x)))) := bmul (lowGroupedE18W_hz4 hx hc) (lowGroupedE18W_hz73 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18W_hz75 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (12408060554915031 / 7812500000000000) (np1 x) := by
    convert (lowGroupedE18W_hz74 hx hc) using 1 <;>
      norm_num [np1] <;> ring

theorem lowGroupedE18W_hz76 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B (11005876608998534131 / 1000000000000000000) (11005876608998534133 / 1000000000000000000) ((√(2 : ℝ)) + (√(92 : ℝ))) := badd (lowGroupedE18W_hz4 hx hc) (lowGroupedE18W_hz3 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18W_hz77 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B 0 (1375734576124817 / 1000000000000000000) (((√(2 : ℝ)) + (√(92 : ℝ))) * x) := bmul (lowGroupedE18W_hz76 hx hc) (lowGroupedE18W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18W_hz78 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B 1 (1001375734576124817 / 1000000000000000000) ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x)) := badd (bpoint (1 : ℝ)) (lowGroupedE18W_hz77 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18W_hz79 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (1416159144868876367 / 1000000000000000000) ((√(2 : ℝ)) * ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x))) := bmul (lowGroupedE18W_hz4 hx hc) (lowGroupedE18W_hz78 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18W_hz80 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B (1999999999999999997 / 1000000000000000000) (140574307399437647 / 62500000000000000) (((√(2 : ℝ)) * ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x))) * (np1 x)) := bmul (lowGroupedE18W_hz79 hx hc) (lowGroupedE18W_hz75 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18W_hz81 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B (1999999999999999997 / 1000000000000000000) (140574307399437647 / 62500000000000000) (ntf x (np1 x)) := by
    convert (lowGroupedE18W_hz80 hx hc) using 1 <;>
      norm_num [ntf] <;> ring

theorem lowGroupedE18W_hz82 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (1430024950673936947 / 1000000000000000000) (((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) := badd (lowGroupedE18W_hz70 hx hc) (lowGroupedE18W_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18W_hz83 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (384315750905393259 / 250000000000000000) ((((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) + ((√(92 : ℝ)) * (√x))) := badd (lowGroupedE18W_hz82 hx hc) (lowGroupedE18W_hz72 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18W_hz84 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B (1999999999999999997 / 1000000000000000000) (2174018188656028919 / 1000000000000000000) ((√(2 : ℝ)) * ((((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) + ((√(92 : ℝ)) * (√x)))) := bmul (lowGroupedE18W_hz4 hx hc) (lowGroupedE18W_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18W_hz85 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B (1999999999999999997 / 1000000000000000000) (2174018188656028919 / 1000000000000000000) (nz x) := by
    convert (lowGroupedE18W_hz84 hx hc) using 1 <;>
      norm_num [nz] <;> ring

theorem lowGroupedE18W_hz86 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B (582117227822831187 / 1000000000000000000) (313326933118943547 / 500000000000000000) (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE18W_hz55 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE18W_hz87 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B (582117227822831187 / 500000000000000000) (313326933118943547 / 250000000000000000) ((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) := bmul (bpoint (2 : ℝ)) (lowGroupedE18W_hz86 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18W_hz88 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B 0 (8505173090835039 / 500000000000000000) (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE18W_hz70 hx hc) (lowGroupedE18W_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18W_hz89 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B 0 (2131919840157687 / 100000000000000000) (((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE18W_hz87 hx hc) (lowGroupedE18W_hz88 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18W_hz90 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B 0 (144675938610129 / 500000000000000000) ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2) := bsq (lowGroupedE18W_hz88 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE18W_hz91 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B 0 (2701068784849641 / 125000000000000000) ((((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) + ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2)) := badd (lowGroupedE18W_hz89 hx hc) (lowGroupedE18W_hz90 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18W_hz92 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B 0 (2701068784849641 / 62500000000000000) ((2 : ℝ) * ((((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) + ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2))) := bmul (bpoint (2 : ℝ)) (lowGroupedE18W_hz91 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18W_hz93 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B 0 (2701068784849641 / 62500000000000000) (nrad x (kdot (nc1 x c)/2+√23*x)) := by
    convert (lowGroupedE18W_hz92 hx hc) using 1 <;>
      norm_num [nrad] <;> ring

theorem lowGroupedE18W_hz94 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B (999999999999999997 / 250000000000000000) (5058850790612887039 / 1000000000000000000) ((ntf x (np1 x))^2) := bsq (lowGroupedE18W_hz81 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE18W_hz95 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B 0 (632356348826611 / 1000000000000000000) (((ntf x (np1 x))^2) * x) := bmul (lowGroupedE18W_hz94 hx hc) (lowGroupedE18W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18W_hz96 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B (1999999999999999997 / 500000000000000000) (140574307399437647 / 31250000000000000) ((2 : ℝ) * (ntf x (np1 x))) := bmul (bpoint (2 : ℝ)) (lowGroupedE18W_hz81 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18W_hz97 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B (999999999999999997 / 125000000000000000) (611222202288202473 / 62500000000000000) (((2 : ℝ) * (ntf x (np1 x))) * (nz x)) := bmul (lowGroupedE18W_hz96 hx hc) (lowGroupedE18W_hz85 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18W_hz98 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B (199999999999999999 / 25000000000000000) (1991325301148468661 / 200000000000000000) ((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) := bmul (lowGroupedE18W_hz97 hx hc) (lowGroupedE18W_hz64 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18W_hz99 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B 0 (1244578313217793 / 1000000000000000000) (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x) := bmul (lowGroupedE18W_hz98 hx hc) (lowGroupedE18W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18W_hz100 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B 0 (469233665511101 / 250000000000000000) ((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) := badd (lowGroupedE18W_hz95 hx hc) (lowGroupedE18W_hz99 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18W_hz101 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B (249999999999999999 / 250000000000000000) (6478377358333473 / 6250000000000000) ((neb x (1/2+√23*x))^2) := bsq (lowGroupedE18W_hz64 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE18W_hz102 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B 0 (44796269719222327 / 1000000000000000000) ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2)) := bmul (lowGroupedE18W_hz93 hx hc) (lowGroupedE18W_hz101 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18W_hz103 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B 0 (46673204381266731 / 1000000000000000000) (((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) + ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2))) := badd (lowGroupedE18W_hz100 hx hc) (lowGroupedE18W_hz102 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18W_hz104 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B (84715116732034487 / 125000000000000000) (39269506807089169 / 50000000000000000) ((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bmul (bpoint (2 : ℝ)) (lowGroupedE18W_hz55 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18W_hz105 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B (379572133440074083 / 500000000000000000) (24724408037794101 / 31250000000000000) ((neb x (kdot (727125683 / 1000000000)/2+√23*x))^2) := bsq (lowGroupedE18W_hz69 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE18W_hz106 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B (1999999999999999997 / 1000000000000000000) (2522480094977037223 / 1000000000000000000) ((np1 x)^2) := bsq (lowGroupedE18W_hz75 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE18W_hz107 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B 0 (31531001187213 / 100000000000000000) (((np1 x)^2) * x) := bmul (lowGroupedE18W_hz106 hx hc) (lowGroupedE18W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18W_hz108 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B (379572133440074083 / 500000000000000000) (395748183610641681 / 500000000000000000) (((neb x (kdot (727125683 / 1000000000)/2+√23*x))^2) + (((np1 x)^2) * x)) := badd (lowGroupedE18W_hz105 hx hc) (lowGroupedE18W_hz107 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18W_hz109 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B (514487961481651951 / 1000000000000000000) (77704179950956339 / 125000000000000000) (((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) * (((neb x (kdot (727125683 / 1000000000)/2+√23*x))^2) + (((np1 x)^2) * x))) := bmul (lowGroupedE18W_hz104 hx hc) (lowGroupedE18W_hz108 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18W_hz110 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B (514487961481651951 / 1000000000000000000) (668306643988917443 / 1000000000000000000) ((((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) + ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2))) + (((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) * (((neb x (kdot (727125683 / 1000000000)/2+√23*x))^2) + (((np1 x)^2) * x)))) := badd (lowGroupedE18W_hz103 hx hc) (lowGroupedE18W_hz109 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18W_hz111 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) : B (514487961481651951 / 1000000000000000000) (668306643988917443 / 1000000000000000000) (ne x (kdot (nc1 x c)/2+√23*x) (neb x (1/2+√23*x)) (neb x (kdot (727125683 / 1000000000)/2+√23*x)^2) (np1 x)) := by
    convert (lowGroupedE18W_hz110 hx hc) using 1 <;>
      norm_num [ne] <;> ring

theorem lowGroupedE18W {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (75418381 / 200000000) (727125683 / 1000000000) c) :
    ne x (kdot (nc1 x c)/2+√23*x) (neb x (1/2+√23*x))
      (neb x (kdot (727125683 / 1000000000)/2+√23*x)^2) (np1 x) ≤ (167076661 / 250000000) :=
  (lowGroupedE18W_hz111 hx hc).2.trans (by norm_num)

theorem lowGroupedE18C_hz0 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B 0 (1 / 8000) x := hx

theorem lowGroupedE18C_hz1 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B (452369839 / 1000000000) (309729467 / 500000000) c := hc

theorem lowGroupedE18C_hz2 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B (6782329983125268139 / 500000000000000000) (13564659966250536279 / 1000000000000000000) (√(184 : ℝ)) := bsqrt (bpoint (184 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE18C_hz3 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE18C_hz4 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B (176776695296636881 / 125000000000000000) (1414213562373095049 / 1000000000000000000) (√(2 : ℝ)) := bsqrt (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE18C_hz5 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B 0 (847791247890659 / 500000000000000000) ((√(184 : ℝ)) * x) := bmul (lowGroupedE18C_hz2 hx hc) (lowGroupedE18C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18C_hz6 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B 1 (500847791247890659 / 500000000000000000) ((1 : ℝ) + ((√(184 : ℝ)) * x)) := badd (bpoint (1 : ℝ)) (lowGroupedE18C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18C_hz7 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B 1 (500847791247890659 / 500000000000000000) (nap x) := by
    convert (lowGroupedE18C_hz6 hx hc) using 1 <;>
      norm_num [nap] <;> ring

theorem lowGroupedE18C_hz8 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B 0 (1 / 64000000) (x^2) := bsq (lowGroupedE18C_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE18C_hz9 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B 0 (1 / 32000000) ((2 : ℝ) * (x^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE18C_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18C_hz10 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B (31999999 / 32000000) 1 ((1 : ℝ) - ((2 : ℝ) * (x^2))) := bsub (bpoint (1 : ℝ)) (lowGroupedE18C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18C_hz11 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B (999999984374999877 / 1000000000000000000) 1 (√((1 : ℝ) - ((2 : ℝ) * (x^2)))) := bsqrt (lowGroupedE18C_hz10 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE18C_hz12 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B (998304401879218559 / 1000000000000000000) 1 ((√((1 : ℝ) - ((2 : ℝ) * (x^2)))) - ((√(184 : ℝ)) * x)) := bsub (lowGroupedE18C_hz11 hx hc) (lowGroupedE18C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18C_hz13 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B (998304401879218559 / 1000000000000000000) 1 (nam x) := by
    convert (lowGroupedE18C_hz12 hx hc) using 1 <;>
      norm_num [nam] <;> ring

theorem lowGroupedE18C_hz14 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B (649421290667912383 / 1000000000000000000) (8117766133362509 / 12500000000000000) (kdot ((452369839 / 1000000000))) := by
    constructor
    · apply bkdot_lower (q := (153512971227816491 / 250000000000000000)) (a := (137671937217834743 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (614051884911265963 / 1000000000000000000)) (a := (550687748869629419 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE18C_hz15 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B (204638471236885921 / 1000000000000000000) (204638471236885921 / 1000000000000000000) (((452369839 / 1000000000) : ℝ)^2) := bsq (bpoint ((452369839 / 1000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE18C_hz16 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B (795361528763114079 / 1000000000000000000) (795361528763114079 / 1000000000000000000) ((1 : ℝ) - (((452369839 / 1000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowGroupedE18C_hz15 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18C_hz17 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B (222957609306555469 / 250000000000000000) (891830437226221877 / 1000000000000000000) (√((1 : ℝ) - (((452369839 / 1000000000) : ℝ)^2))) := bsqrt (lowGroupedE18C_hz16 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE18C_hz18 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B (70969611242179739 / 250000000000000000) (283878444968718957 / 1000000000000000000) ((√((1 : ℝ) - (((452369839 / 1000000000) : ℝ)^2))) / Real.pi) := bdiv (lowGroupedE18C_hz17 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE18C_hz19 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B (293778604702615727 / 1000000000000000000) (146889302351554029 / 500000000000000000) (((452369839 / 1000000000) : ℝ) * (kdot ((452369839 / 1000000000)))) := bmul (bpoint ((452369839 / 1000000000) : ℝ)) (lowGroupedE18C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18C_hz20 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B (577657049671334683 / 1000000000000000000) (115531409934365403 / 200000000000000000) (((√((1 : ℝ) - (((452369839 / 1000000000) : ℝ)^2))) / Real.pi) + (((452369839 / 1000000000) : ℝ) * (kdot ((452369839 / 1000000000))))) := badd (lowGroupedE18C_hz18 hx hc) (lowGroupedE18C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18C_hz21 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B (577657049671334683 / 1000000000000000000) (115531409934365403 / 200000000000000000) (kappa ((452369839 / 1000000000))) := by rw [kappa_eq]; exact (lowGroupedE18C_hz20 hx hc)

theorem lowGroupedE18C_hz22 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B (142529593028180469 / 200000000000000000) (356323982570451179 / 500000000000000000) (kdot ((309729467 / 500000000))) := by
    constructor
    · apply bkdot_lower (q := (121186935663156437 / 250000000000000000)) (a := (112842880213427421 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (484747742652625747 / 1000000000000000000)) (a := (225685760426854833 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE18C_hz23 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B (95932342728104089 / 250000000000000000) (95932342728104089 / 250000000000000000) (((309729467 / 500000000) : ℝ)^2) := bsq (bpoint ((309729467 / 500000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE18C_hz24 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B (154067657271895911 / 250000000000000000) (154067657271895911 / 250000000000000000) ((1 : ℝ) - (((309729467 / 500000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowGroupedE18C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18C_hz25 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B (98128632821890953 / 125000000000000000) (6280232500601021 / 8000000000000000) (√((1 : ℝ) - (((309729467 / 500000000) : ℝ)^2))) := bsqrt (lowGroupedE18C_hz24 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE18C_hz26 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B (249882511559256759 / 1000000000000000000) (6247062788981419 / 25000000000000000) ((√((1 : ℝ) - (((309729467 / 500000000) : ℝ)^2))) / Real.pi) := bdiv (lowGroupedE18C_hz25 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE18C_hz27 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B (220728074401726263 / 500000000000000000) (88291229760690507 / 200000000000000000) (((309729467 / 500000000) : ℝ) * (kdot ((309729467 / 500000000)))) := bmul (bpoint ((309729467 / 500000000) : ℝ)) (lowGroupedE18C_hz22 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18C_hz28 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B (138267732072541857 / 200000000000000000) (138267732072541859 / 200000000000000000) (((√((1 : ℝ) - (((309729467 / 500000000) : ℝ)^2))) / Real.pi) + (((309729467 / 500000000) : ℝ) * (kdot ((309729467 / 500000000))))) := badd (lowGroupedE18C_hz26 hx hc) (lowGroupedE18C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18C_hz29 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B (138267732072541857 / 200000000000000000) (138267732072541859 / 200000000000000000) (kappa ((309729467 / 500000000))) := by rw [kappa_eq]; exact (lowGroupedE18C_hz28 hx hc)

theorem lowGroupedE18C_hz30 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B (577657049671334683 / 1000000000000000000) (138267732072541859 / 200000000000000000) (kappa c) := bkappa (lowGroupedE18C_hz1 hx hc) (by norm_num) (by norm_num) (lowGroupedE18C_hz21 hx hc).1 (lowGroupedE18C_hz29 hx hc).2

theorem lowGroupedE18C_hz31 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B (61732267927458141 / 200000000000000000) (422342950328665317 / 1000000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (lowGroupedE18C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18C_hz32 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B (61732267927458141 / 100000000000000000) (422342950328665317 / 500000000000000000) ((2 : ℝ) * ((1 : ℝ) - (kappa c))) := bmul (bpoint (2 : ℝ)) (lowGroupedE18C_hz31 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18C_hz33 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B 0 (1 / 8000000) ((8 : ℝ) * (x^2)) := bmul (bpoint (8 : ℝ)) (lowGroupedE18C_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18C_hz34 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B (61732255427458141 / 100000000000000000) (422342950328665317 / 500000000000000000) (((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2))) := bsub (lowGroupedE18C_hz32 hx hc) (lowGroupedE18C_hz33 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18C_hz35 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B (392849384075685363 / 500000000000000000) (183813590428709121 / 200000000000000000) (√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) := bsqrt (lowGroupedE18C_hz34 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE18C_hz36 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B (6782329983125268139 / 250000000000000000) (13564659966250536279 / 500000000000000000) ((2 : ℝ) * (√(184 : ℝ))) := bmul (bpoint (2 : ℝ)) (lowGroupedE18C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18C_hz37 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B 0 (678232998312527 / 200000000000000000) (((2 : ℝ) * (√(184 : ℝ))) * x) := bmul (lowGroupedE18C_hz36 hx hc) (lowGroupedE18C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18C_hz38 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B (782307603159808091 / 1000000000000000000) (183813590428709121 / 200000000000000000) ((√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) - (((2 : ℝ) * (√(184 : ℝ))) * x)) := bsub (lowGroupedE18C_hz35 hx hc) (lowGroupedE18C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18C_hz39 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B (782307603159808091 / 1000000000000000000) (183813590428709121 / 200000000000000000) (ndm x c) := by
    convert (lowGroupedE18C_hz38 hx hc) using 1 <;>
      norm_num [ndm] <;> ring

theorem lowGroupedE18C_hz40 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B 1 (1003394039991562637 / 1000000000000000000) ((nap x)^2) := bsq (lowGroupedE18C_hz7 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE18C_hz41 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B 2 (1003394039991562637 / 500000000000000000) ((2 : ℝ) * ((nap x)^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE18C_hz40 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18C_hz42 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B (306002592980821889 / 500000000000000000) (168937180131466127 / 200000000000000000) ((ndm x c)^2) := bsq (lowGroupedE18C_hz39 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE18C_hz43 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B (231062819868533873 / 200000000000000000) (174347861752685187 / 125000000000000000) (((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) := bsub (lowGroupedE18C_hz41 hx hc) (lowGroupedE18C_hz42 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18C_hz44 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B (199322335762284863 / 200000000000000000) 1 ((nam x)^2) := bsq (lowGroupedE18C_hz13 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE18C_hz45 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B (199322335762284863 / 100000000000000000) 2 ((2 : ℝ) * ((nam x)^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE18C_hz44 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18C_hz46 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B (288828524835667341 / 500000000000000000) (699762467004662641 / 1000000000000000000) ((((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) / ((2 : ℝ) * ((nam x)^2))) := bdiv (lowGroupedE18C_hz43 hx hc) (lowGroupedE18C_hz45 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE18C_hz47 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B (288828524835667341 / 500000000000000000) (699762467004662641 / 1000000000000000000) (nc1 x c) := by
    convert (lowGroupedE18C_hz46 hx hc) using 1 <;>
      norm_num [nc1] <;> ring

theorem lowGroupedE18C_hz48 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B (696032889789840187 / 1000000000000000000) (696032889789840437 / 1000000000000000000) (kdot ((288828524835667341 / 500000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (517399879819492611 / 1000000000000000000)) (a := (477470420184578549 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (51739987981949261 / 100000000000000000)) (a := (477470420184578159 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE18C_hz49 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B (746710832226701297 / 1000000000000000000) (746710832226701299 / 1000000000000000000) (kdot ((699762467004662641 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (420279661538194221 / 1000000000000000000)) (a := (198932847177616953 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (21013983076909711 / 50000000000000000)) (a := (24866605897202119 / 62500000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE18C_hz50 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B (696032889789840187 / 1000000000000000000) (746710832226701299 / 1000000000000000000) (kdot (nc1 x c)) := bkdot (lowGroupedE18C_hz47 hx hc) (lowGroupedE18C_hz48 hx hc).1 (lowGroupedE18C_hz49 hx hc).2

theorem lowGroupedE18C_hz51 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE18C_hz52 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B 0 (59947894041409 / 100000000000000000) ((√(23 : ℝ)) * x) := bmul (lowGroupedE18C_hz51 hx hc) (lowGroupedE18C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18C_hz53 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B (1 / 2) (50059947894041409 / 100000000000000000) (((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)) := badd (bpoint ((1 / 2) : ℝ)) (lowGroupedE18C_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18C_hz54 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B (348016444894920093 / 1000000000000000000) (7467108322267013 / 20000000000000000) ((kdot (nc1 x c)) / (2 : ℝ)) := bdiv (lowGroupedE18C_hz50 hx hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE18C_hz55 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B (348016444894920093 / 1000000000000000000) (18697744752688237 / 50000000000000000) (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)) := badd (lowGroupedE18C_hz54 hx hc) (lowGroupedE18C_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18C_hz56 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B (89080995642612793 / 250000000000000000) (356323982570451179 / 1000000000000000000) ((kdot ((309729467 / 500000000))) / (2 : ℝ)) := bdiv (lowGroupedE18C_hz22 hx hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE18C_hz57 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B (89080995642612793 / 250000000000000000) (356923461510865269 / 1000000000000000000) (((kdot ((309729467 / 500000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x)) := badd (lowGroupedE18C_hz56 hx hc) (lowGroupedE18C_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18C_hz58 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B (176776695296636881 / 250000000000000000) (353765274914177413 / 500000000000000000) (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE18C_hz53 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE18C_hz59 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGroupedE18C_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE18C_hz60 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B (176776695296636881 / 250000000000000000) (28748435588634151 / 40000000000000000) ((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) := badd (lowGroupedE18C_hz58 hx hc) (lowGroupedE18C_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18C_hz61 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B 0 (59947894041409 / 50000000000000000) ((√(92 : ℝ)) * x) := bmul (lowGroupedE18C_hz3 hx hc) (lowGroupedE18C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18C_hz62 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B (176776695296636881 / 250000000000000000) (143981969519336391 / 200000000000000000) (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE18C_hz60 hx hc) (lowGroupedE18C_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18C_hz63 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B (499999999999999999 / 500000000000000000) (1018106270157175527 / 1000000000000000000) ((√(2 : ℝ)) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE18C_hz4 hx hc) (lowGroupedE18C_hz62 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18C_hz64 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B (499999999999999999 / 500000000000000000) (1018106270157175527 / 1000000000000000000) (neb x (1/2+√23*x)) := by
    convert (lowGroupedE18C_hz63 hx hc) using 1 <;>
      norm_num [neb] <;> ring

theorem lowGroupedE18C_hz65 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B (298464395937962411 / 500000000000000000) (597430716912735639 / 1000000000000000000) (√(((kdot ((309729467 / 500000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE18C_hz57 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE18C_hz66 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B (298464395937962411 / 500000000000000000) (152152764200058647 / 250000000000000000) ((√(((kdot ((309729467 / 500000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) := badd (lowGroupedE18C_hz65 hx hc) (lowGroupedE18C_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18C_hz67 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B (298464395937962411 / 500000000000000000) (38113125917566423 / 62500000000000000) (((√(((kdot ((309729467 / 500000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE18C_hz66 hx hc) (lowGroupedE18C_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18C_hz68 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B (21104619831047987 / 25000000000000000) (862401593232895169 / 1000000000000000000) ((√(2 : ℝ)) * (((√(((kdot ((309729467 / 500000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE18C_hz4 hx hc) (lowGroupedE18C_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18C_hz69 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B (21104619831047987 / 25000000000000000) (862401593232895169 / 1000000000000000000) (neb x (kdot (309729467 / 500000000)/2+√23*x)) := by
    convert (lowGroupedE18C_hz68 hx hc) using 1 <;>
      norm_num [neb] <;> ring

theorem lowGroupedE18C_hz70 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B 0 (7905694150420949 / 500000000000000000) ((√(2 : ℝ)) * (√x)) := bmul (lowGroupedE18C_hz4 hx hc) (lowGroupedE18C_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18C_hz71 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B 1 (507905694150420949 / 500000000000000000) (((√(2 : ℝ)) * (√x)) + (1 : ℝ)) := badd (lowGroupedE18C_hz70 hx hc) (bpoint (1 : ℝ)) (by norm_num) (by norm_num)

theorem lowGroupedE18C_hz72 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B 0 (107238052947636089 / 1000000000000000000) ((√(92 : ℝ)) * (√x)) := bmul (lowGroupedE18C_hz3 hx hc) (lowGroupedE18C_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18C_hz73 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B 1 (1123049441248477987 / 1000000000000000000) ((((√(2 : ℝ)) * (√x)) + (1 : ℝ)) + ((√(92 : ℝ)) * (√x))) := badd (lowGroupedE18C_hz71 hx hc) (lowGroupedE18C_hz72 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18C_hz74 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B (176776695296636881 / 125000000000000000) (12408060554915031 / 7812500000000000) ((√(2 : ℝ)) * ((((√(2 : ℝ)) * (√x)) + (1 : ℝ)) + ((√(92 : ℝ)) * (√x)))) := bmul (lowGroupedE18C_hz4 hx hc) (lowGroupedE18C_hz73 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18C_hz75 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B (176776695296636881 / 125000000000000000) (12408060554915031 / 7812500000000000) (np1 x) := by
    convert (lowGroupedE18C_hz74 hx hc) using 1 <;>
      norm_num [np1] <;> ring

theorem lowGroupedE18C_hz76 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B (11005876608998534131 / 1000000000000000000) (11005876608998534133 / 1000000000000000000) ((√(2 : ℝ)) + (√(92 : ℝ))) := badd (lowGroupedE18C_hz4 hx hc) (lowGroupedE18C_hz3 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18C_hz77 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B 0 (1375734576124817 / 1000000000000000000) (((√(2 : ℝ)) + (√(92 : ℝ))) * x) := bmul (lowGroupedE18C_hz76 hx hc) (lowGroupedE18C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18C_hz78 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B 1 (1001375734576124817 / 1000000000000000000) ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x)) := badd (bpoint (1 : ℝ)) (lowGroupedE18C_hz77 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18C_hz79 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B (176776695296636881 / 125000000000000000) (1416159144868876367 / 1000000000000000000) ((√(2 : ℝ)) * ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x))) := bmul (lowGroupedE18C_hz4 hx hc) (lowGroupedE18C_hz78 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18C_hz80 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B (1999999999999999997 / 1000000000000000000) (140574307399437647 / 62500000000000000) (((√(2 : ℝ)) * ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x))) * (np1 x)) := bmul (lowGroupedE18C_hz79 hx hc) (lowGroupedE18C_hz75 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18C_hz81 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B (1999999999999999997 / 1000000000000000000) (140574307399437647 / 62500000000000000) (ntf x (np1 x)) := by
    convert (lowGroupedE18C_hz80 hx hc) using 1 <;>
      norm_num [ntf] <;> ring

theorem lowGroupedE18C_hz82 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B (176776695296636881 / 125000000000000000) (1430024950673936947 / 1000000000000000000) (((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) := badd (lowGroupedE18C_hz70 hx hc) (lowGroupedE18C_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18C_hz83 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B (176776695296636881 / 125000000000000000) (384315750905393259 / 250000000000000000) ((((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) + ((√(92 : ℝ)) * (√x))) := badd (lowGroupedE18C_hz82 hx hc) (lowGroupedE18C_hz72 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18C_hz84 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B (1999999999999999997 / 1000000000000000000) (2174018188656028919 / 1000000000000000000) ((√(2 : ℝ)) * ((((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) + ((√(92 : ℝ)) * (√x)))) := bmul (lowGroupedE18C_hz4 hx hc) (lowGroupedE18C_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18C_hz85 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B (1999999999999999997 / 1000000000000000000) (2174018188656028919 / 1000000000000000000) (nz x) := by
    convert (lowGroupedE18C_hz84 hx hc) using 1 <;>
      norm_num [nz] <;> ring

theorem lowGroupedE18C_hz86 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B (36870574146204743 / 62500000000000000) (152879628927010077 / 250000000000000000) (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE18C_hz55 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE18C_hz87 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B (36870574146204743 / 31250000000000000) (152879628927010077 / 125000000000000000) ((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) := bmul (bpoint (2 : ℝ)) (lowGroupedE18C_hz86 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18C_hz88 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B 0 (8505173090835039 / 500000000000000000) (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE18C_hz70 hx hc) (lowGroupedE18C_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18C_hz89 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B 0 (4160856659477927 / 200000000000000000) (((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE18C_hz87 hx hc) (lowGroupedE18C_hz88 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18C_hz90 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B 0 (144675938610129 / 500000000000000000) ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2) := bsq (lowGroupedE18C_hz88 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE18C_hz91 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B 0 (21093635174609893 / 1000000000000000000) ((((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) + ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2)) := badd (lowGroupedE18C_hz89 hx hc) (lowGroupedE18C_hz90 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18C_hz92 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B 0 (21093635174609893 / 500000000000000000) ((2 : ℝ) * ((((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) + ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2))) := bmul (bpoint (2 : ℝ)) (lowGroupedE18C_hz91 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18C_hz93 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B 0 (21093635174609893 / 500000000000000000) (nrad x (kdot (nc1 x c)/2+√23*x)) := by
    convert (lowGroupedE18C_hz92 hx hc) using 1 <;>
      norm_num [nrad] <;> ring

theorem lowGroupedE18C_hz94 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B (999999999999999997 / 250000000000000000) (5058850790612887039 / 1000000000000000000) ((ntf x (np1 x))^2) := bsq (lowGroupedE18C_hz81 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE18C_hz95 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B 0 (632356348826611 / 1000000000000000000) (((ntf x (np1 x))^2) * x) := bmul (lowGroupedE18C_hz94 hx hc) (lowGroupedE18C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18C_hz96 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B (1999999999999999997 / 500000000000000000) (140574307399437647 / 31250000000000000) ((2 : ℝ) * (ntf x (np1 x))) := bmul (bpoint (2 : ℝ)) (lowGroupedE18C_hz81 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18C_hz97 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B (999999999999999997 / 125000000000000000) (611222202288202473 / 62500000000000000) (((2 : ℝ) * (ntf x (np1 x))) * (nz x)) := bmul (lowGroupedE18C_hz96 hx hc) (lowGroupedE18C_hz85 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18C_hz98 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B (199999999999999999 / 25000000000000000) (1991325301148468661 / 200000000000000000) ((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) := bmul (lowGroupedE18C_hz97 hx hc) (lowGroupedE18C_hz64 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18C_hz99 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B 0 (1244578313217793 / 1000000000000000000) (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x) := bmul (lowGroupedE18C_hz98 hx hc) (lowGroupedE18C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18C_hz100 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B 0 (469233665511101 / 250000000000000000) ((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) := badd (lowGroupedE18C_hz95 hx hc) (lowGroupedE18C_hz99 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18C_hz101 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B (249999999999999999 / 250000000000000000) (6478377358333473 / 6250000000000000) ((neb x (1/2+√23*x))^2) := bsq (lowGroupedE18C_hz64 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE18C_hz102 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B 0 (8745761825288913 / 200000000000000000) ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2)) := bmul (lowGroupedE18C_hz93 hx hc) (lowGroupedE18C_hz101 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18C_hz103 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B 0 (45605743788488969 / 1000000000000000000) (((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) + ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2))) := badd (lowGroupedE18C_hz100 hx hc) (lowGroupedE18C_hz102 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18C_hz104 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B (348016444894920093 / 500000000000000000) (18697744752688237 / 25000000000000000) ((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bmul (bpoint (2 : ℝ)) (lowGroupedE18C_hz55 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18C_hz105 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B (712647965140902341 / 1000000000000000000) (743736508010635979 / 1000000000000000000) ((neb x (kdot (309729467 / 500000000)/2+√23*x))^2) := bsq (lowGroupedE18C_hz69 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE18C_hz106 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B (1999999999999999997 / 1000000000000000000) (2522480094977037223 / 1000000000000000000) ((np1 x)^2) := bsq (lowGroupedE18C_hz75 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE18C_hz107 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B 0 (31531001187213 / 100000000000000000) (((np1 x)^2) * x) := bmul (lowGroupedE18C_hz106 hx hc) (lowGroupedE18C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18C_hz108 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B (712647965140902341 / 1000000000000000000) (744051818022508109 / 1000000000000000000) (((neb x (kdot (309729467 / 500000000)/2+√23*x))^2) + (((np1 x)^2) * x)) := badd (lowGroupedE18C_hz105 hx hc) (lowGroupedE18C_hz107 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18C_hz109 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B (496026422579871549 / 1000000000000000000) (556483639046339761 / 1000000000000000000) (((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) * (((neb x (kdot (309729467 / 500000000)/2+√23*x))^2) + (((np1 x)^2) * x))) := bmul (lowGroupedE18C_hz104 hx hc) (lowGroupedE18C_hz108 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18C_hz110 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B (496026422579871549 / 1000000000000000000) (60208938283482873 / 100000000000000000) ((((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) + ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2))) + (((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) * (((neb x (kdot (309729467 / 500000000)/2+√23*x))^2) + (((np1 x)^2) * x)))) := badd (lowGroupedE18C_hz103 hx hc) (lowGroupedE18C_hz109 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE18C_hz111 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) : B (496026422579871549 / 1000000000000000000) (60208938283482873 / 100000000000000000) (ne x (kdot (nc1 x c)/2+√23*x) (neb x (1/2+√23*x)) (neb x (kdot (309729467 / 500000000)/2+√23*x)^2) (np1 x)) := by
    convert (lowGroupedE18C_hz110 hx hc) using 1 <;>
      norm_num [ne] <;> ring

theorem lowGroupedE18C {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (452369839 / 1000000000) (309729467 / 500000000) c) :
    ne x (kdot (nc1 x c)/2+√23*x) (neb x (1/2+√23*x))
      (neb x (kdot (309729467 / 500000000)/2+√23*x)^2) (np1 x) ≤ (602089383 / 1000000000) :=
  (lowGroupedE18C_hz111 hx hc).2.trans (by norm_num)

theorem lowGroupedE20W_hz0 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B 0 (1 / 8000) x := hx

theorem lowGroupedE20W_hz1 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B (366904611 / 1000000000) (726206157 / 1000000000) c := hc

theorem lowGroupedE20W_hz2 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B (6782329983125268139 / 500000000000000000) (13564659966250536279 / 1000000000000000000) (√(184 : ℝ)) := bsqrt (bpoint (184 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE20W_hz3 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE20W_hz4 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (1414213562373095049 / 1000000000000000000) (√(2 : ℝ)) := bsqrt (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE20W_hz5 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B 0 (847791247890659 / 500000000000000000) ((√(184 : ℝ)) * x) := bmul (lowGroupedE20W_hz2 hx hc) (lowGroupedE20W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20W_hz6 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B 1 (500847791247890659 / 500000000000000000) ((1 : ℝ) + ((√(184 : ℝ)) * x)) := badd (bpoint (1 : ℝ)) (lowGroupedE20W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20W_hz7 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B 1 (500847791247890659 / 500000000000000000) (nap x) := by
    convert (lowGroupedE20W_hz6 hx hc) using 1 <;>
      norm_num [nap] <;> ring

theorem lowGroupedE20W_hz8 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B 0 (1 / 64000000) (x^2) := bsq (lowGroupedE20W_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE20W_hz9 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B 0 (1 / 32000000) ((2 : ℝ) * (x^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE20W_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20W_hz10 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B (31999999 / 32000000) 1 ((1 : ℝ) - ((2 : ℝ) * (x^2))) := bsub (bpoint (1 : ℝ)) (lowGroupedE20W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20W_hz11 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B (999999984374999877 / 1000000000000000000) 1 (√((1 : ℝ) - ((2 : ℝ) * (x^2)))) := bsqrt (lowGroupedE20W_hz10 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE20W_hz12 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B (998304401879218559 / 1000000000000000000) 1 ((√((1 : ℝ) - ((2 : ℝ) * (x^2)))) - ((√(184 : ℝ)) * x)) := bsub (lowGroupedE20W_hz11 hx hc) (lowGroupedE20W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20W_hz13 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B (998304401879218559 / 1000000000000000000) 1 (nam x) := by
    convert (lowGroupedE20W_hz12 hx hc) using 1 <;>
      norm_num [nam] <;> ring

theorem lowGroupedE20W_hz14 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B (309791230027627001 / 500000000000000000) (619582460223181617 / 1000000000000000000) (kdot ((366904611 / 1000000000))) := by
    constructor
    · apply bkdot_lower (q := (136111702627152071 / 200000000000000000)) (a := (597558474393557873 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (340279256567880177 / 500000000000000000)) (a := (597558474129777793 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE20W_hz15 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B (134618993573061321 / 1000000000000000000) (134618993573061321 / 1000000000000000000) (((366904611 / 1000000000) : ℝ)^2) := bsq (bpoint ((366904611 / 1000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE20W_hz16 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B (865381006426938679 / 1000000000000000000) (865381006426938679 / 1000000000000000000) ((1 : ℝ) - (((366904611 / 1000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowGroupedE20W_hz15 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20W_hz17 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B (930258569660574897 / 1000000000000000000) (465129284830287449 / 500000000000000000) (√((1 : ℝ) - (((366904611 / 1000000000) : ℝ)^2))) := bsqrt (lowGroupedE20W_hz16 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE20W_hz18 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B (296110499430153501 / 1000000000000000000) (148055249715076751 / 500000000000000000) ((√((1 : ℝ) - (((366904611 / 1000000000) : ℝ)^2))) / Real.pi) := bdiv (lowGroupedE20W_hz17 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE20W_hz19 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B (28415957686124501 / 125000000000000000) (9093106462024377 / 40000000000000000) (((366904611 / 1000000000) : ℝ) * (kdot ((366904611 / 1000000000)))) := bmul (bpoint ((366904611 / 1000000000) : ℝ)) (lowGroupedE20W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20W_hz20 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B (523438160919149509 / 1000000000000000000) (523438160980762927 / 1000000000000000000) (((√((1 : ℝ) - (((366904611 / 1000000000) : ℝ)^2))) / Real.pi) + (((366904611 / 1000000000) : ℝ) * (kdot ((366904611 / 1000000000))))) := badd (lowGroupedE20W_hz18 hx hc) (lowGroupedE20W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20W_hz21 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B (523438160919149509 / 1000000000000000000) (523438160980762927 / 1000000000000000000) (kappa ((366904611 / 1000000000))) := by rw [kappa_eq]; exact (lowGroupedE20W_hz20 hx hc)

theorem lowGroupedE20W_hz22 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B (758718214268785951 / 1000000000000000000) (758718214268785953 / 1000000000000000000) (kdot ((726206157 / 1000000000))) := by
    constructor
    · apply bkdot_lower (q := (398258916757066803 / 1000000000000000000)) (a := (379004542749104327 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (199129458378533401 / 500000000000000000)) (a := (15160181709964173 / 40000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE20W_hz23 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B (527375382464708649 / 1000000000000000000) (527375382464708649 / 1000000000000000000) (((726206157 / 1000000000) : ℝ)^2) := bsq (bpoint ((726206157 / 1000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE20W_hz24 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B (472624617535291351 / 1000000000000000000) (472624617535291351 / 1000000000000000000) ((1 : ℝ) - (((726206157 / 1000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowGroupedE20W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20W_hz25 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B (687476994186199187 / 1000000000000000000) (171869248546549797 / 250000000000000000) (√((1 : ℝ) - (((726206157 / 1000000000) : ℝ)^2))) := bsqrt (lowGroupedE20W_hz24 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE20W_hz26 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B (6838460117918237 / 31250000000000000) (43766144754676717 / 200000000000000000) ((√((1 : ℝ) - (((726206157 / 1000000000) : ℝ)^2))) / Real.pi) := bdiv (lowGroupedE20W_hz25 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE20W_hz27 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B (55098583863003761 / 100000000000000000) (137746459657509403 / 250000000000000000) (((726206157 / 1000000000) : ℝ) * (kdot ((726206157 / 1000000000)))) := bmul (bpoint ((726206157 / 1000000000) : ℝ)) (lowGroupedE20W_hz22 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20W_hz28 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B (384908281201710597 / 500000000000000000) (769816562403421197 / 1000000000000000000) (((√((1 : ℝ) - (((726206157 / 1000000000) : ℝ)^2))) / Real.pi) + (((726206157 / 1000000000) : ℝ) * (kdot ((726206157 / 1000000000))))) := badd (lowGroupedE20W_hz26 hx hc) (lowGroupedE20W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20W_hz29 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B (384908281201710597 / 500000000000000000) (769816562403421197 / 1000000000000000000) (kappa ((726206157 / 1000000000))) := by rw [kappa_eq]; exact (lowGroupedE20W_hz28 hx hc)

theorem lowGroupedE20W_hz30 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B (523438160919149509 / 1000000000000000000) (769816562403421197 / 1000000000000000000) (kappa c) := bkappa (lowGroupedE20W_hz1 hx hc) (by norm_num) (by norm_num) (lowGroupedE20W_hz21 hx hc).1 (lowGroupedE20W_hz29 hx hc).2

theorem lowGroupedE20W_hz31 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B (230183437596578803 / 1000000000000000000) (476561839080850491 / 1000000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (lowGroupedE20W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20W_hz32 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B (230183437596578803 / 500000000000000000) (476561839080850491 / 500000000000000000) ((2 : ℝ) * ((1 : ℝ) - (kappa c))) := bmul (bpoint (2 : ℝ)) (lowGroupedE20W_hz31 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20W_hz33 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B 0 (1 / 8000000) ((8 : ℝ) * (x^2)) := bmul (bpoint (8 : ℝ)) (lowGroupedE20W_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20W_hz34 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B (230183375096578803 / 500000000000000000) (476561839080850491 / 500000000000000000) (((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2))) := bsub (lowGroupedE20W_hz32 hx hc) (lowGroupedE20W_hz33 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20W_hz35 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B (678503316272778143 / 1000000000000000000) (244070133127972689 / 250000000000000000) (√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) := bsqrt (lowGroupedE20W_hz34 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE20W_hz36 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B (6782329983125268139 / 250000000000000000) (13564659966250536279 / 500000000000000000) ((2 : ℝ) * (√(184 : ℝ))) := bmul (bpoint (2 : ℝ)) (lowGroupedE20W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20W_hz37 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B 0 (678232998312527 / 200000000000000000) (((2 : ℝ) * (√(184 : ℝ))) * x) := bmul (lowGroupedE20W_hz36 hx hc) (lowGroupedE20W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20W_hz38 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B (168778037820303877 / 250000000000000000) (244070133127972689 / 250000000000000000) ((√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) - (((2 : ℝ) * (√(184 : ℝ))) * x)) := bsub (lowGroupedE20W_hz35 hx hc) (lowGroupedE20W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20W_hz39 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B (168778037820303877 / 250000000000000000) (244070133127972689 / 250000000000000000) (ndm x c) := by
    convert (lowGroupedE20W_hz38 hx hc) using 1 <;>
      norm_num [ndm] <;> ring

theorem lowGroupedE20W_hz40 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B 1 (1003394039991562637 / 1000000000000000000) ((nap x)^2) := bsq (lowGroupedE20W_hz7 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE20W_hz41 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B 2 (1003394039991562637 / 500000000000000000) ((2 : ℝ) * ((nap x)^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE20W_hz40 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20W_hz42 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B (227888208403775407 / 500000000000000000) (119140459770212623 / 125000000000000000) ((ndm x c)^2) := bsq (lowGroupedE20W_hz39 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE20W_hz43 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B (130859540229787377 / 125000000000000000) (77550583158778723 / 50000000000000000) (((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) := bsub (lowGroupedE20W_hz41 hx hc) (lowGroupedE20W_hz42 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20W_hz44 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B (199322335762284863 / 200000000000000000) 1 ((nam x)^2) := bsq (lowGroupedE20W_hz13 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE20W_hz45 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B (199322335762284863 / 100000000000000000) 2 ((2 : ℝ) * ((nam x)^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE20W_hz44 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20W_hz46 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B (130859540229787377 / 250000000000000000) (778142428064528001 / 1000000000000000000) ((((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) / ((2 : ℝ) * ((nam x)^2))) := bdiv (lowGroupedE20W_hz43 hx hc) (lowGroupedE20W_hz45 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE20W_hz47 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B (130859540229787377 / 250000000000000000) (778142428064528001 / 1000000000000000000) (nc1 x c) := by
    convert (lowGroupedE20W_hz46 hx hc) using 1 <;>
      norm_num [nc1] <;> ring

theorem lowGroupedE20W_hz48 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B (67535089113405639 / 100000000000000000) (337675445567033799 / 500000000000000000) (kdot ((130859540229787377 / 250000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (27965154356557879 / 50000000000000000)) (a := (509957627703860727 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (559303087131157579 / 1000000000000000000)) (a := (127489406925960781 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE20W_hz49 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B (783837839495780537 / 1000000000000000000) (783837839495780539 / 1000000000000000000) (kdot ((778142428064528001 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (353226969613386019 / 1000000000000000000)) (a := (33954672771207681 / 100000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (176613484806693009 / 500000000000000000)) (a := (42443340964009601 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE20W_hz50 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B (67535089113405639 / 100000000000000000) (783837839495780539 / 1000000000000000000) (kdot (nc1 x c)) := bkdot (lowGroupedE20W_hz47 hx hc) (lowGroupedE20W_hz48 hx hc).1 (lowGroupedE20W_hz49 hx hc).2

theorem lowGroupedE20W_hz51 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE20W_hz52 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B 0 (59947894041409 / 100000000000000000) ((√(23 : ℝ)) * x) := bmul (lowGroupedE20W_hz51 hx hc) (lowGroupedE20W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20W_hz53 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B (1 / 2) (50059947894041409 / 100000000000000000) (((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)) := badd (bpoint ((1 / 2) : ℝ)) (lowGroupedE20W_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20W_hz54 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B (67535089113405639 / 200000000000000000) (39191891974789027 / 100000000000000000) ((kdot (nc1 x c)) / (2 : ℝ)) := bdiv (lowGroupedE20W_hz50 hx hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE20W_hz55 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B (67535089113405639 / 200000000000000000) (9812959967207609 / 25000000000000000) (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)) := badd (lowGroupedE20W_hz54 hx hc) (lowGroupedE20W_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20W_hz56 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B (15174364285375719 / 40000000000000000) (379359107134392977 / 1000000000000000000) ((kdot ((726206157 / 1000000000))) / (2 : ℝ)) := bdiv (lowGroupedE20W_hz22 hx hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE20W_hz57 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B (15174364285375719 / 40000000000000000) (379958586074807067 / 1000000000000000000) (((kdot ((726206157 / 1000000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x)) := badd (lowGroupedE20W_hz56 hx hc) (lowGroupedE20W_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20W_hz58 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B (176776695296636881 / 250000000000000000) (353765274914177413 / 500000000000000000) (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE20W_hz53 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE20W_hz59 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGroupedE20W_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE20W_hz60 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B (176776695296636881 / 250000000000000000) (28748435588634151 / 40000000000000000) ((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) := badd (lowGroupedE20W_hz58 hx hc) (lowGroupedE20W_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20W_hz61 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B 0 (59947894041409 / 50000000000000000) ((√(92 : ℝ)) * x) := bmul (lowGroupedE20W_hz3 hx hc) (lowGroupedE20W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20W_hz62 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B (176776695296636881 / 250000000000000000) (143981969519336391 / 200000000000000000) (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE20W_hz60 hx hc) (lowGroupedE20W_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20W_hz63 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B (499999999999999999 / 500000000000000000) (1018106270157175527 / 1000000000000000000) ((√(2 : ℝ)) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE20W_hz4 hx hc) (lowGroupedE20W_hz62 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20W_hz64 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B (499999999999999999 / 500000000000000000) (1018106270157175527 / 1000000000000000000) (neb x (1/2+√23*x)) := by
    convert (lowGroupedE20W_hz63 hx hc) using 1 <;>
      norm_num [neb] <;> ring

theorem lowGroupedE20W_hz65 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B (61592134817230761 / 100000000000000000) (616407808252626751 / 1000000000000000000) (√(((kdot ((726206157 / 1000000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE20W_hz57 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE20W_hz66 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B (61592134817230761 / 100000000000000000) (6275881481401257 / 10000000000000000) ((√(((kdot ((726206157 / 1000000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) := badd (lowGroupedE20W_hz65 hx hc) (lowGroupedE20W_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20W_hz67 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B (61592134817230761 / 100000000000000000) (15719677650523847 / 25000000000000000) (((√(((kdot ((726206157 / 1000000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE20W_hz66 hx hc) (lowGroupedE20W_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20W_hz68 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B (871044323940398539 / 1000000000000000000) (88923925318016219 / 100000000000000000) ((√(2 : ℝ)) * (((√(((kdot ((726206157 / 1000000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE20W_hz4 hx hc) (lowGroupedE20W_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20W_hz69 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B (871044323940398539 / 1000000000000000000) (88923925318016219 / 100000000000000000) (neb x (kdot (726206157 / 1000000000)/2+√23*x)) := by
    convert (lowGroupedE20W_hz68 hx hc) using 1 <;>
      norm_num [neb] <;> ring

theorem lowGroupedE20W_hz70 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B 0 (7905694150420949 / 500000000000000000) ((√(2 : ℝ)) * (√x)) := bmul (lowGroupedE20W_hz4 hx hc) (lowGroupedE20W_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20W_hz71 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B 1 (507905694150420949 / 500000000000000000) (((√(2 : ℝ)) * (√x)) + (1 : ℝ)) := badd (lowGroupedE20W_hz70 hx hc) (bpoint (1 : ℝ)) (by norm_num) (by norm_num)

theorem lowGroupedE20W_hz72 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B 0 (107238052947636089 / 1000000000000000000) ((√(92 : ℝ)) * (√x)) := bmul (lowGroupedE20W_hz3 hx hc) (lowGroupedE20W_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20W_hz73 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B 1 (1123049441248477987 / 1000000000000000000) ((((√(2 : ℝ)) * (√x)) + (1 : ℝ)) + ((√(92 : ℝ)) * (√x))) := badd (lowGroupedE20W_hz71 hx hc) (lowGroupedE20W_hz72 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20W_hz74 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (12408060554915031 / 7812500000000000) ((√(2 : ℝ)) * ((((√(2 : ℝ)) * (√x)) + (1 : ℝ)) + ((√(92 : ℝ)) * (√x)))) := bmul (lowGroupedE20W_hz4 hx hc) (lowGroupedE20W_hz73 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20W_hz75 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (12408060554915031 / 7812500000000000) (np1 x) := by
    convert (lowGroupedE20W_hz74 hx hc) using 1 <;>
      norm_num [np1] <;> ring

theorem lowGroupedE20W_hz76 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B (11005876608998534131 / 1000000000000000000) (11005876608998534133 / 1000000000000000000) ((√(2 : ℝ)) + (√(92 : ℝ))) := badd (lowGroupedE20W_hz4 hx hc) (lowGroupedE20W_hz3 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20W_hz77 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B 0 (1375734576124817 / 1000000000000000000) (((√(2 : ℝ)) + (√(92 : ℝ))) * x) := bmul (lowGroupedE20W_hz76 hx hc) (lowGroupedE20W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20W_hz78 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B 1 (1001375734576124817 / 1000000000000000000) ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x)) := badd (bpoint (1 : ℝ)) (lowGroupedE20W_hz77 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20W_hz79 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (1416159144868876367 / 1000000000000000000) ((√(2 : ℝ)) * ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x))) := bmul (lowGroupedE20W_hz4 hx hc) (lowGroupedE20W_hz78 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20W_hz80 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B (1999999999999999997 / 1000000000000000000) (140574307399437647 / 62500000000000000) (((√(2 : ℝ)) * ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x))) * (np1 x)) := bmul (lowGroupedE20W_hz79 hx hc) (lowGroupedE20W_hz75 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20W_hz81 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B (1999999999999999997 / 1000000000000000000) (140574307399437647 / 62500000000000000) (ntf x (np1 x)) := by
    convert (lowGroupedE20W_hz80 hx hc) using 1 <;>
      norm_num [ntf] <;> ring

theorem lowGroupedE20W_hz82 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (1430024950673936947 / 1000000000000000000) (((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) := badd (lowGroupedE20W_hz70 hx hc) (lowGroupedE20W_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20W_hz83 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (384315750905393259 / 250000000000000000) ((((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) + ((√(92 : ℝ)) * (√x))) := badd (lowGroupedE20W_hz82 hx hc) (lowGroupedE20W_hz72 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20W_hz84 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B (1999999999999999997 / 1000000000000000000) (2174018188656028919 / 1000000000000000000) ((√(2 : ℝ)) * ((((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) + ((√(92 : ℝ)) * (√x)))) := bmul (lowGroupedE20W_hz4 hx hc) (lowGroupedE20W_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20W_hz85 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B (1999999999999999997 / 1000000000000000000) (2174018188656028919 / 1000000000000000000) (nz x) := by
    convert (lowGroupedE20W_hz84 hx hc) using 1 <;>
      norm_num [nz] <;> ring

theorem lowGroupedE20W_hz86 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B (581098481814423771 / 1000000000000000000) (313256443943418489 / 500000000000000000) (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE20W_hz55 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE20W_hz87 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B (581098481814423771 / 500000000000000000) (313256443943418489 / 250000000000000000) ((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) := bmul (bpoint (2 : ℝ)) (lowGroupedE20W_hz86 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20W_hz88 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B 0 (8505173090835039 / 500000000000000000) (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE20W_hz70 hx hc) (lowGroupedE20W_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20W_hz89 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B 0 (21314402220465903 / 1000000000000000000) (((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE20W_hz87 hx hc) (lowGroupedE20W_hz88 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20W_hz90 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B 0 (144675938610129 / 500000000000000000) ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2) := bsq (lowGroupedE20W_hz88 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE20W_hz91 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B 0 (21603754097686161 / 1000000000000000000) ((((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) + ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2)) := badd (lowGroupedE20W_hz89 hx hc) (lowGroupedE20W_hz90 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20W_hz92 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B 0 (21603754097686161 / 500000000000000000) ((2 : ℝ) * ((((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) + ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2))) := bmul (bpoint (2 : ℝ)) (lowGroupedE20W_hz91 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20W_hz93 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B 0 (21603754097686161 / 500000000000000000) (nrad x (kdot (nc1 x c)/2+√23*x)) := by
    convert (lowGroupedE20W_hz92 hx hc) using 1 <;>
      norm_num [nrad] <;> ring

theorem lowGroupedE20W_hz94 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B (999999999999999997 / 250000000000000000) (5058850790612887039 / 1000000000000000000) ((ntf x (np1 x))^2) := bsq (lowGroupedE20W_hz81 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE20W_hz95 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B 0 (632356348826611 / 1000000000000000000) (((ntf x (np1 x))^2) * x) := bmul (lowGroupedE20W_hz94 hx hc) (lowGroupedE20W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20W_hz96 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B (1999999999999999997 / 500000000000000000) (140574307399437647 / 31250000000000000) ((2 : ℝ) * (ntf x (np1 x))) := bmul (bpoint (2 : ℝ)) (lowGroupedE20W_hz81 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20W_hz97 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B (999999999999999997 / 125000000000000000) (611222202288202473 / 62500000000000000) (((2 : ℝ) * (ntf x (np1 x))) * (nz x)) := bmul (lowGroupedE20W_hz96 hx hc) (lowGroupedE20W_hz85 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20W_hz98 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B (199999999999999999 / 25000000000000000) (1991325301148468661 / 200000000000000000) ((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) := bmul (lowGroupedE20W_hz97 hx hc) (lowGroupedE20W_hz64 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20W_hz99 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B 0 (1244578313217793 / 1000000000000000000) (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x) := bmul (lowGroupedE20W_hz98 hx hc) (lowGroupedE20W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20W_hz100 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B 0 (469233665511101 / 250000000000000000) ((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) := badd (lowGroupedE20W_hz95 hx hc) (lowGroupedE20W_hz99 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20W_hz101 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B (249999999999999999 / 250000000000000000) (6478377358333473 / 6250000000000000) ((neb x (1/2+√23*x))^2) := bsq (lowGroupedE20W_hz64 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE20W_hz102 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B 0 (8957265369693057 / 200000000000000000) ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2)) := bmul (lowGroupedE20W_hz93 hx hc) (lowGroupedE20W_hz101 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20W_hz103 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B 0 (46663261510509689 / 1000000000000000000) (((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) + ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2))) := badd (lowGroupedE20W_hz100 hx hc) (lowGroupedE20W_hz102 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20W_hz104 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B (67535089113405639 / 100000000000000000) (9812959967207609 / 12500000000000000) ((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bmul (bpoint (2 : ℝ)) (lowGroupedE20W_hz55 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20W_hz105 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B (758718214268785947 / 1000000000000000000) (49421653087275787 / 62500000000000000) ((neb x (kdot (726206157 / 1000000000)/2+√23*x))^2) := bsq (lowGroupedE20W_hz69 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE20W_hz106 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B (1999999999999999997 / 1000000000000000000) (2522480094977037223 / 1000000000000000000) ((np1 x)^2) := bsq (lowGroupedE20W_hz75 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE20W_hz107 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B 0 (31531001187213 / 100000000000000000) (((np1 x)^2) * x) := bmul (lowGroupedE20W_hz106 hx hc) (lowGroupedE20W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20W_hz108 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B (758718214268785947 / 1000000000000000000) (395530879704142361 / 500000000000000000) (((neb x (kdot (726206157 / 1000000000)/2+√23*x))^2) + (((np1 x)^2) * x)) := badd (lowGroupedE20W_hz105 hx hc) (lowGroupedE20W_hz107 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20W_hz109 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B (512401022126064527 / 1000000000000000000) (621012590132985211 / 1000000000000000000) (((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) * (((neb x (kdot (726206157 / 1000000000)/2+√23*x))^2) + (((np1 x)^2) * x))) := bmul (lowGroupedE20W_hz104 hx hc) (lowGroupedE20W_hz108 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20W_hz110 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B (512401022126064527 / 1000000000000000000) (6676758516434949 / 10000000000000000) ((((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) + ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2))) + (((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) * (((neb x (kdot (726206157 / 1000000000)/2+√23*x))^2) + (((np1 x)^2) * x)))) := badd (lowGroupedE20W_hz103 hx hc) (lowGroupedE20W_hz109 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20W_hz111 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) : B (512401022126064527 / 1000000000000000000) (6676758516434949 / 10000000000000000) (ne x (kdot (nc1 x c)/2+√23*x) (neb x (1/2+√23*x)) (neb x (kdot (726206157 / 1000000000)/2+√23*x)^2) (np1 x)) := by
    convert (lowGroupedE20W_hz110 hx hc) using 1 <;>
      norm_num [ne] <;> ring

theorem lowGroupedE20W {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (366904611 / 1000000000) (726206157 / 1000000000) c) :
    ne x (kdot (nc1 x c)/2+√23*x) (neb x (1/2+√23*x))
      (neb x (kdot (726206157 / 1000000000)/2+√23*x)^2) (np1 x) ≤ (166918963 / 250000000) :=
  (lowGroupedE20W_hz111 hx hc).2.trans (by norm_num)

theorem lowGroupedE20C_hz0 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B 0 (1 / 8000) x := hx

theorem lowGroupedE20C_hz1 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B (27643759 / 62500000) (12369653 / 20000000) c := hc

theorem lowGroupedE20C_hz2 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B (6782329983125268139 / 500000000000000000) (13564659966250536279 / 1000000000000000000) (√(184 : ℝ)) := bsqrt (bpoint (184 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE20C_hz3 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE20C_hz4 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B (176776695296636881 / 125000000000000000) (1414213562373095049 / 1000000000000000000) (√(2 : ℝ)) := bsqrt (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE20C_hz5 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B 0 (847791247890659 / 500000000000000000) ((√(184 : ℝ)) * x) := bmul (lowGroupedE20C_hz2 hx hc) (lowGroupedE20C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20C_hz6 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B 1 (500847791247890659 / 500000000000000000) ((1 : ℝ) + ((√(184 : ℝ)) * x)) := badd (bpoint (1 : ℝ)) (lowGroupedE20C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20C_hz7 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B 1 (500847791247890659 / 500000000000000000) (nap x) := by
    convert (lowGroupedE20C_hz6 hx hc) using 1 <;>
      norm_num [nap] <;> ring

theorem lowGroupedE20C_hz8 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B 0 (1 / 64000000) (x^2) := bsq (lowGroupedE20C_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE20C_hz9 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B 0 (1 / 32000000) ((2 : ℝ) * (x^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE20C_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20C_hz10 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B (31999999 / 32000000) 1 ((1 : ℝ) - ((2 : ℝ) * (x^2))) := bsub (bpoint (1 : ℝ)) (lowGroupedE20C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20C_hz11 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B (999999984374999877 / 1000000000000000000) 1 (√((1 : ℝ) - ((2 : ℝ) * (x^2)))) := bsqrt (lowGroupedE20C_hz10 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE20C_hz12 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B (998304401879218559 / 1000000000000000000) 1 ((√((1 : ℝ) - ((2 : ℝ) * (x^2)))) - ((√(184 : ℝ)) * x)) := bsub (lowGroupedE20C_hz11 hx hc) (lowGroupedE20C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20C_hz13 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B (998304401879218559 / 1000000000000000000) 1 (nam x) := by
    convert (lowGroupedE20C_hz12 hx hc) using 1 <;>
      norm_num [nam] <;> ring

theorem lowGroupedE20C_hz14 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B (645837398417255543 / 1000000000000000000) (645837398419272349 / 1000000000000000000) (kdot ((27643759 / 62500000))) := by
    constructor
    · apply bkdot_lower (q := (971611102404119 / 1562500000000000)) (a := (69539664206787429 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (621831105538636159 / 1000000000000000000)) (a := (278158656825565721 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE20C_hz15 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B (764177411650081 / 3906250000000000) (764177411650081 / 3906250000000000) (((27643759 / 62500000) : ℝ)^2) := bsq (bpoint ((27643759 / 62500000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE20C_hz16 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B (3142072588349919 / 3906250000000000) (3142072588349919 / 3906250000000000) ((1 : ℝ) - (((27643759 / 62500000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowGroupedE20C_hz15 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20C_hz17 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B (89686709306205413 / 100000000000000000) (896867093062054131 / 1000000000000000000) (√((1 : ℝ) - (((27643759 / 62500000) : ℝ)^2))) := bsqrt (lowGroupedE20C_hz16 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE20C_hz18 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B (142740831157284823 / 500000000000000000) (285481662314569647 / 1000000000000000000) ((√((1 : ℝ) - (((27643759 / 62500000) : ℝ)^2))) / Real.pi) := bdiv (lowGroupedE20C_hz17 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE20C_hz19 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B (142826987160268749 / 500000000000000000) (285653974321429533 / 1000000000000000000) (((27643759 / 62500000) : ℝ) * (kdot ((27643759 / 62500000)))) := bmul (bpoint ((27643759 / 62500000) : ℝ)) (lowGroupedE20C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20C_hz20 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B (71391954579388393 / 125000000000000000) (28556781831799959 / 50000000000000000) (((√((1 : ℝ) - (((27643759 / 62500000) : ℝ)^2))) / Real.pi) + (((27643759 / 62500000) : ℝ) * (kdot ((27643759 / 62500000))))) := badd (lowGroupedE20C_hz18 hx hc) (lowGroupedE20C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20C_hz21 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B (71391954579388393 / 125000000000000000) (28556781831799959 / 50000000000000000) (kappa ((27643759 / 62500000))) := by rw [kappa_eq]; exact (lowGroupedE20C_hz20 hx hc)

theorem lowGroupedE20C_hz22 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B (178063075011649293 / 250000000000000000) (142450460009319437 / 200000000000000000) (kdot ((12369653 / 20000000))) := by
    constructor
    · apply bkdot_lower (q := (485515525824608109 / 1000000000000000000)) (a := (225996515065242603 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (121378881456152027 / 250000000000000000)) (a := (451993030130485187 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE20C_hz23 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B (153008315340409 / 400000000000000) (153008315340409 / 400000000000000) (((12369653 / 20000000) : ℝ)^2) := bsq (bpoint ((12369653 / 20000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE20C_hz24 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B (246991684659591 / 400000000000000) (246991684659591 / 400000000000000) ((1 : ℝ) - (((12369653 / 20000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowGroupedE20C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20C_hz25 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B (392899227426377583 / 500000000000000000) (785798454852755167 / 1000000000000000000) (√((1 : ℝ) - (((12369653 / 20000000) : ℝ)^2))) := bsqrt (lowGroupedE20C_hz24 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE20C_hz26 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B (250127416727579069 / 1000000000000000000) (25012741672757907 / 100000000000000000) ((√((1 : ℝ) - (((12369653 / 20000000) : ℝ)^2))) / Real.pi) := bdiv (lowGroupedE20C_hz25 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE20C_hz27 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B (220257845000707271 / 500000000000000000) (440515690001414551 / 1000000000000000000) (((12369653 / 20000000) : ℝ) * (kdot ((12369653 / 20000000)))) := bmul (bpoint ((12369653 / 20000000) : ℝ)) (lowGroupedE20C_hz22 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20C_hz28 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B (690643106728993611 / 1000000000000000000) (690643106728993621 / 1000000000000000000) (((√((1 : ℝ) - (((12369653 / 20000000) : ℝ)^2))) / Real.pi) + (((12369653 / 20000000) : ℝ) * (kdot ((12369653 / 20000000))))) := badd (lowGroupedE20C_hz26 hx hc) (lowGroupedE20C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20C_hz29 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B (690643106728993611 / 1000000000000000000) (690643106728993621 / 1000000000000000000) (kappa ((12369653 / 20000000))) := by rw [kappa_eq]; exact (lowGroupedE20C_hz28 hx hc)

theorem lowGroupedE20C_hz30 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B (71391954579388393 / 125000000000000000) (690643106728993621 / 1000000000000000000) (kappa c) := bkappa (lowGroupedE20C_hz1 hx hc) (by norm_num) (by norm_num) (lowGroupedE20C_hz21 hx hc).1 (lowGroupedE20C_hz29 hx hc).2

theorem lowGroupedE20C_hz31 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B (309356893271006379 / 1000000000000000000) (53608045420611607 / 125000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (lowGroupedE20C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20C_hz32 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B (309356893271006379 / 500000000000000000) (53608045420611607 / 62500000000000000) ((2 : ℝ) * ((1 : ℝ) - (kappa c))) := bmul (bpoint (2 : ℝ)) (lowGroupedE20C_hz31 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20C_hz33 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B 0 (1 / 8000000) ((8 : ℝ) * (x^2)) := bmul (bpoint (8 : ℝ)) (lowGroupedE20C_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20C_hz34 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B (309356830771006379 / 500000000000000000) (53608045420611607 / 62500000000000000) (((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2))) := bsub (lowGroupedE20C_hz32 hx hc) (lowGroupedE20C_hz33 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20C_hz35 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B (786583537548309459 / 1000000000000000000) (926136451463706137 / 1000000000000000000) (√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) := bsqrt (lowGroupedE20C_hz34 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE20C_hz36 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B (6782329983125268139 / 250000000000000000) (13564659966250536279 / 500000000000000000) ((2 : ℝ) * (√(184 : ℝ))) := bmul (bpoint (2 : ℝ)) (lowGroupedE20C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20C_hz37 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B 0 (678232998312527 / 200000000000000000) (((2 : ℝ) * (√(184 : ℝ))) * x) := bmul (lowGroupedE20C_hz36 hx hc) (lowGroupedE20C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20C_hz38 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B (97899046569593353 / 125000000000000000) (926136451463706137 / 1000000000000000000) ((√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) - (((2 : ℝ) * (√(184 : ℝ))) * x)) := bsub (lowGroupedE20C_hz35 hx hc) (lowGroupedE20C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20C_hz39 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B (97899046569593353 / 125000000000000000) (926136451463706137 / 1000000000000000000) (ndm x c) := by
    convert (lowGroupedE20C_hz38 hx hc) using 1 <;>
      norm_num [ndm] <;> ring

theorem lowGroupedE20C_hz40 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B 1 (1003394039991562637 / 1000000000000000000) ((nap x)^2) := bsq (lowGroupedE20C_hz7 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE20C_hz41 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B 2 (1003394039991562637 / 500000000000000000) ((2 : ℝ) * ((nap x)^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE20C_hz40 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20C_hz42 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B (122678058486213223 / 200000000000000000) (428864363364892857 / 500000000000000000) ((ndm x c)^2) := bsq (lowGroupedE20C_hz39 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE20C_hz43 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B (571135636635107143 / 500000000000000000) (1393397787552059159 / 1000000000000000000) (((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) := bsub (lowGroupedE20C_hz41 hx hc) (lowGroupedE20C_hz42 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20C_hz44 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B (199322335762284863 / 200000000000000000) 1 ((nam x)^2) := bsq (lowGroupedE20C_hz13 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE20C_hz45 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B (199322335762284863 / 100000000000000000) 2 ((2 : ℝ) * ((nam x)^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE20C_hz44 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20C_hz46 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B (571135636635107143 / 1000000000000000000) (699067559199109811 / 1000000000000000000) ((((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) / ((2 : ℝ) * ((nam x)^2))) := bdiv (lowGroupedE20C_hz43 hx hc) (lowGroupedE20C_hz45 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE20C_hz47 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B (571135636635107143 / 1000000000000000000) (699067559199109811 / 1000000000000000000) (nc1 x c) := by
    convert (lowGroupedE20C_hz46 hx hc) using 1 <;>
      norm_num [nc1] <;> ring

theorem lowGroupedE20C_hz48 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B (346748486590424823 / 500000000000000000) (346748486590425023 / 500000000000000000) (kdot ((571135636635107143 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (52246011324864621 / 100000000000000000)) (a := (481453828679039061 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (522460113248646209 / 1000000000000000000)) (a := (96290765735807687 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE20C_hz49 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B (746401344083462981 / 1000000000000000000) (93300168010432873 / 125000000000000000) (kdot ((699067559199109811 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (420851791154384987 / 1000000000000000000)) (a := (15934073487752769 / 40000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (210425895577192493 / 500000000000000000)) (a := (398351837193819223 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE20C_hz50 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B (346748486590424823 / 500000000000000000) (93300168010432873 / 125000000000000000) (kdot (nc1 x c)) := bkdot (lowGroupedE20C_hz47 hx hc) (lowGroupedE20C_hz48 hx hc).1 (lowGroupedE20C_hz49 hx hc).2

theorem lowGroupedE20C_hz51 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE20C_hz52 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B 0 (59947894041409 / 100000000000000000) ((√(23 : ℝ)) * x) := bmul (lowGroupedE20C_hz51 hx hc) (lowGroupedE20C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20C_hz53 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B (1 / 2) (50059947894041409 / 100000000000000000) (((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)) := badd (bpoint ((1 / 2) : ℝ)) (lowGroupedE20C_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20C_hz54 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B (346748486590424823 / 1000000000000000000) (93300168010432873 / 250000000000000000) ((kdot (nc1 x c)) / (2 : ℝ)) := bdiv (lowGroupedE20C_hz50 hx hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE20C_hz55 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B (346748486590424823 / 1000000000000000000) (186900075491072791 / 500000000000000000) (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)) := badd (lowGroupedE20C_hz54 hx hc) (lowGroupedE20C_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20C_hz56 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B (178063075011649293 / 500000000000000000) (356126150023298593 / 1000000000000000000) ((kdot ((12369653 / 20000000))) / (2 : ℝ)) := bdiv (lowGroupedE20C_hz22 hx hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE20C_hz57 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B (178063075011649293 / 500000000000000000) (356725628963712683 / 1000000000000000000) (((kdot ((12369653 / 20000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x)) := badd (lowGroupedE20C_hz56 hx hc) (lowGroupedE20C_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20C_hz58 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B (176776695296636881 / 250000000000000000) (353765274914177413 / 500000000000000000) (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE20C_hz53 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE20C_hz59 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGroupedE20C_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE20C_hz60 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B (176776695296636881 / 250000000000000000) (28748435588634151 / 40000000000000000) ((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) := badd (lowGroupedE20C_hz58 hx hc) (lowGroupedE20C_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20C_hz61 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B 0 (59947894041409 / 50000000000000000) ((√(92 : ℝ)) * x) := bmul (lowGroupedE20C_hz3 hx hc) (lowGroupedE20C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20C_hz62 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B (176776695296636881 / 250000000000000000) (143981969519336391 / 200000000000000000) (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE20C_hz60 hx hc) (lowGroupedE20C_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20C_hz63 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B (499999999999999999 / 500000000000000000) (1018106270157175527 / 1000000000000000000) ((√(2 : ℝ)) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE20C_hz4 hx hc) (lowGroupedE20C_hz62 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20C_hz64 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B (499999999999999999 / 500000000000000000) (1018106270157175527 / 1000000000000000000) (neb x (1/2+√23*x)) := by
    convert (lowGroupedE20C_hz63 hx hc) using 1 <;>
      norm_num [neb] <;> ring

theorem lowGroupedE20C_hz65 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B (11935261204067527 / 20000000000000000) (298632562258251019 / 500000000000000000) (√(((kdot ((12369653 / 20000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE20C_hz57 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE20C_hz66 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B (11935261204067527 / 20000000000000000) (608445464404000987 / 1000000000000000000) ((√(((kdot ((12369653 / 20000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) := badd (lowGroupedE20C_hz65 hx hc) (lowGroupedE20C_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20C_hz67 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B (11935261204067527 / 20000000000000000) (609644422284829167 / 1000000000000000000) (((√(((kdot ((12369653 / 20000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE20C_hz66 hx hc) (lowGroupedE20C_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20C_hz68 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B (421975206631443327 / 500000000000000000) (862167410220315751 / 1000000000000000000) ((√(2 : ℝ)) * (((√(((kdot ((12369653 / 20000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE20C_hz4 hx hc) (lowGroupedE20C_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20C_hz69 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B (421975206631443327 / 500000000000000000) (862167410220315751 / 1000000000000000000) (neb x (kdot (12369653 / 20000000)/2+√23*x)) := by
    convert (lowGroupedE20C_hz68 hx hc) using 1 <;>
      norm_num [neb] <;> ring

theorem lowGroupedE20C_hz70 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B 0 (7905694150420949 / 500000000000000000) ((√(2 : ℝ)) * (√x)) := bmul (lowGroupedE20C_hz4 hx hc) (lowGroupedE20C_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20C_hz71 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B 1 (507905694150420949 / 500000000000000000) (((√(2 : ℝ)) * (√x)) + (1 : ℝ)) := badd (lowGroupedE20C_hz70 hx hc) (bpoint (1 : ℝ)) (by norm_num) (by norm_num)

theorem lowGroupedE20C_hz72 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B 0 (107238052947636089 / 1000000000000000000) ((√(92 : ℝ)) * (√x)) := bmul (lowGroupedE20C_hz3 hx hc) (lowGroupedE20C_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20C_hz73 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B 1 (1123049441248477987 / 1000000000000000000) ((((√(2 : ℝ)) * (√x)) + (1 : ℝ)) + ((√(92 : ℝ)) * (√x))) := badd (lowGroupedE20C_hz71 hx hc) (lowGroupedE20C_hz72 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20C_hz74 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B (176776695296636881 / 125000000000000000) (12408060554915031 / 7812500000000000) ((√(2 : ℝ)) * ((((√(2 : ℝ)) * (√x)) + (1 : ℝ)) + ((√(92 : ℝ)) * (√x)))) := bmul (lowGroupedE20C_hz4 hx hc) (lowGroupedE20C_hz73 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20C_hz75 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B (176776695296636881 / 125000000000000000) (12408060554915031 / 7812500000000000) (np1 x) := by
    convert (lowGroupedE20C_hz74 hx hc) using 1 <;>
      norm_num [np1] <;> ring

theorem lowGroupedE20C_hz76 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B (11005876608998534131 / 1000000000000000000) (11005876608998534133 / 1000000000000000000) ((√(2 : ℝ)) + (√(92 : ℝ))) := badd (lowGroupedE20C_hz4 hx hc) (lowGroupedE20C_hz3 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20C_hz77 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B 0 (1375734576124817 / 1000000000000000000) (((√(2 : ℝ)) + (√(92 : ℝ))) * x) := bmul (lowGroupedE20C_hz76 hx hc) (lowGroupedE20C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20C_hz78 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B 1 (1001375734576124817 / 1000000000000000000) ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x)) := badd (bpoint (1 : ℝ)) (lowGroupedE20C_hz77 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20C_hz79 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B (176776695296636881 / 125000000000000000) (1416159144868876367 / 1000000000000000000) ((√(2 : ℝ)) * ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x))) := bmul (lowGroupedE20C_hz4 hx hc) (lowGroupedE20C_hz78 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20C_hz80 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B (1999999999999999997 / 1000000000000000000) (140574307399437647 / 62500000000000000) (((√(2 : ℝ)) * ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x))) * (np1 x)) := bmul (lowGroupedE20C_hz79 hx hc) (lowGroupedE20C_hz75 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20C_hz81 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B (1999999999999999997 / 1000000000000000000) (140574307399437647 / 62500000000000000) (ntf x (np1 x)) := by
    convert (lowGroupedE20C_hz80 hx hc) using 1 <;>
      norm_num [ntf] <;> ring

theorem lowGroupedE20C_hz82 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B (176776695296636881 / 125000000000000000) (1430024950673936947 / 1000000000000000000) (((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) := badd (lowGroupedE20C_hz70 hx hc) (lowGroupedE20C_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20C_hz83 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B (176776695296636881 / 125000000000000000) (384315750905393259 / 250000000000000000) ((((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) + ((√(92 : ℝ)) * (√x))) := badd (lowGroupedE20C_hz82 hx hc) (lowGroupedE20C_hz72 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20C_hz84 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B (1999999999999999997 / 1000000000000000000) (2174018188656028919 / 1000000000000000000) ((√(2 : ℝ)) * ((((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) + ((√(92 : ℝ)) * (√x)))) := bmul (lowGroupedE20C_hz4 hx hc) (lowGroupedE20C_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20C_hz85 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B (1999999999999999997 / 1000000000000000000) (2174018188656028919 / 1000000000000000000) (nz x) := by
    convert (lowGroupedE20C_hz84 hx hc) using 1 <;>
      norm_num [nz] <;> ring

theorem lowGroupedE20C_hz86 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B (588853535771353607 / 1000000000000000000) (305695989089710491 / 500000000000000000) (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE20C_hz55 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE20C_hz87 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B (588853535771353607 / 500000000000000000) (305695989089710491 / 250000000000000000) ((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) := bmul (bpoint (2 : ℝ)) (lowGroupedE20C_hz86 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20C_hz88 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B 0 (8505173090835039 / 500000000000000000) (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE20C_hz70 hx hc) (lowGroupedE20C_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20C_hz89 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B 0 (20799978403056059 / 1000000000000000000) (((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE20C_hz87 hx hc) (lowGroupedE20C_hz88 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20C_hz90 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B 0 (144675938610129 / 500000000000000000) ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2) := bsq (lowGroupedE20C_hz88 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE20C_hz91 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B 0 (21089330280276317 / 1000000000000000000) ((((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) + ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2)) := badd (lowGroupedE20C_hz89 hx hc) (lowGroupedE20C_hz90 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20C_hz92 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B 0 (21089330280276317 / 500000000000000000) ((2 : ℝ) * ((((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) + ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2))) := bmul (bpoint (2 : ℝ)) (lowGroupedE20C_hz91 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20C_hz93 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B 0 (21089330280276317 / 500000000000000000) (nrad x (kdot (nc1 x c)/2+√23*x)) := by
    convert (lowGroupedE20C_hz92 hx hc) using 1 <;>
      norm_num [nrad] <;> ring

theorem lowGroupedE20C_hz94 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B (999999999999999997 / 250000000000000000) (5058850790612887039 / 1000000000000000000) ((ntf x (np1 x))^2) := bsq (lowGroupedE20C_hz81 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE20C_hz95 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B 0 (632356348826611 / 1000000000000000000) (((ntf x (np1 x))^2) * x) := bmul (lowGroupedE20C_hz94 hx hc) (lowGroupedE20C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20C_hz96 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B (1999999999999999997 / 500000000000000000) (140574307399437647 / 31250000000000000) ((2 : ℝ) * (ntf x (np1 x))) := bmul (bpoint (2 : ℝ)) (lowGroupedE20C_hz81 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20C_hz97 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B (999999999999999997 / 125000000000000000) (611222202288202473 / 62500000000000000) (((2 : ℝ) * (ntf x (np1 x))) * (nz x)) := bmul (lowGroupedE20C_hz96 hx hc) (lowGroupedE20C_hz85 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20C_hz98 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B (199999999999999999 / 25000000000000000) (1991325301148468661 / 200000000000000000) ((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) := bmul (lowGroupedE20C_hz97 hx hc) (lowGroupedE20C_hz64 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20C_hz99 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B 0 (1244578313217793 / 1000000000000000000) (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x) := bmul (lowGroupedE20C_hz98 hx hc) (lowGroupedE20C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20C_hz100 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B 0 (469233665511101 / 250000000000000000) ((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) := badd (lowGroupedE20C_hz95 hx hc) (lowGroupedE20C_hz99 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20C_hz101 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B (249999999999999999 / 250000000000000000) (6478377358333473 / 6250000000000000) ((neb x (1/2+√23*x))^2) := bsq (lowGroupedE20C_hz64 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE20C_hz102 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B 0 (8743976946570151 / 200000000000000000) ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2)) := bmul (lowGroupedE20C_hz93 hx hc) (lowGroupedE20C_hz101 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20C_hz103 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B 0 (45596819394895159 / 1000000000000000000) (((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) + ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2))) := badd (lowGroupedE20C_hz100 hx hc) (lowGroupedE20C_hz102 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20C_hz104 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B (346748486590424823 / 500000000000000000) (186900075491072791 / 250000000000000000) ((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bmul (bpoint (2 : ℝ)) (lowGroupedE20C_hz55 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20C_hz105 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B (712252300046597169 / 1000000000000000000) (743332643246006221 / 1000000000000000000) ((neb x (kdot (12369653 / 20000000)/2+√23*x))^2) := bsq (lowGroupedE20C_hz69 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE20C_hz106 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B (1999999999999999997 / 1000000000000000000) (2522480094977037223 / 1000000000000000000) ((np1 x)^2) := bsq (lowGroupedE20C_hz75 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE20C_hz107 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B 0 (31531001187213 / 100000000000000000) (((np1 x)^2) * x) := bmul (lowGroupedE20C_hz106 hx hc) (lowGroupedE20C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20C_hz108 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B (712252300046597169 / 1000000000000000000) (743647953257878351 / 1000000000000000000) (((neb x (kdot (12369653 / 20000000)/2+√23*x))^2) + (((np1 x)^2) * x)) := badd (lowGroupedE20C_hz105 hx hc) (lowGroupedE20C_hz107 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20C_hz109 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B (493944814223413471 / 1000000000000000000) (555951434410716937 / 1000000000000000000) (((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) * (((neb x (kdot (12369653 / 20000000)/2+√23*x))^2) + (((np1 x)^2) * x))) := bmul (lowGroupedE20C_hz104 hx hc) (lowGroupedE20C_hz108 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20C_hz110 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B (493944814223413471 / 1000000000000000000) (9399191465712689 / 15625000000000000) ((((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) + ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2))) + (((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) * (((neb x (kdot (12369653 / 20000000)/2+√23*x))^2) + (((np1 x)^2) * x)))) := badd (lowGroupedE20C_hz103 hx hc) (lowGroupedE20C_hz109 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE20C_hz111 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) : B (493944814223413471 / 1000000000000000000) (9399191465712689 / 15625000000000000) (ne x (kdot (nc1 x c)/2+√23*x) (neb x (1/2+√23*x)) (neb x (kdot (12369653 / 20000000)/2+√23*x)^2) (np1 x)) := by
    convert (lowGroupedE20C_hz110 hx hc) using 1 <;>
      norm_num [ne] <;> ring

theorem lowGroupedE20C {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27643759 / 62500000) (12369653 / 20000000) c) :
    ne x (kdot (nc1 x c)/2+√23*x) (neb x (1/2+√23*x))
      (neb x (kdot (12369653 / 20000000)/2+√23*x)^2) (np1 x) ≤ (300774127 / 500000000) :=
  (lowGroupedE20C_hz111 hx hc).2.trans (by norm_num)

theorem lowGroupedE40W_hz0 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B 0 (1 / 8000) x := hx

theorem lowGroupedE40W_hz1 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B (178385151 / 500000000) (716969799 / 1000000000) c := hc

theorem lowGroupedE40W_hz2 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B (6782329983125268139 / 500000000000000000) (13564659966250536279 / 1000000000000000000) (√(184 : ℝ)) := bsqrt (bpoint (184 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE40W_hz3 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE40W_hz4 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (1414213562373095049 / 1000000000000000000) (√(2 : ℝ)) := bsqrt (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE40W_hz5 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B 0 (847791247890659 / 500000000000000000) ((√(184 : ℝ)) * x) := bmul (lowGroupedE40W_hz2 hx hc) (lowGroupedE40W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40W_hz6 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B 1 (500847791247890659 / 500000000000000000) ((1 : ℝ) + ((√(184 : ℝ)) * x)) := badd (bpoint (1 : ℝ)) (lowGroupedE40W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40W_hz7 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B 1 (500847791247890659 / 500000000000000000) (nap x) := by
    convert (lowGroupedE40W_hz6 hx hc) using 1 <;>
      norm_num [nap] <;> ring

theorem lowGroupedE40W_hz8 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B 0 (1 / 64000000) (x^2) := bsq (lowGroupedE40W_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE40W_hz9 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B 0 (1 / 32000000) ((2 : ℝ) * (x^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE40W_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40W_hz10 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B (31999999 / 32000000) 1 ((1 : ℝ) - ((2 : ℝ) * (x^2))) := bsub (bpoint (1 : ℝ)) (lowGroupedE40W_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40W_hz11 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B (999999984374999877 / 1000000000000000000) 1 (√((1 : ℝ) - ((2 : ℝ) * (x^2)))) := bsqrt (lowGroupedE40W_hz10 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE40W_hz12 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B (998304401879218559 / 1000000000000000000) 1 ((√((1 : ℝ) - ((2 : ℝ) * (x^2)))) - ((√(184 : ℝ)) * x)) := bsub (lowGroupedE40W_hz11 hx hc) (lowGroupedE40W_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40W_hz13 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B (998304401879218559 / 1000000000000000000) 1 (nam x) := by
    convert (lowGroupedE40W_hz12 hx hc) using 1 <;>
      norm_num [nam] <;> ring

theorem lowGroupedE40W_hz14 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B (123224423514814933 / 200000000000000000) (616122117871431641 / 1000000000000000000) (kdot ((178385151 / 500000000))) := by
    constructor
    · apply bkdot_lower (q := (17213527910912261 / 25000000000000000)) (a := (301496983826223357 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (688541116436490439 / 1000000000000000000)) (a := (602993967185359469 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE40W_hz15 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B (31821262097292801 / 250000000000000000) (31821262097292801 / 250000000000000000) (((178385151 / 500000000) : ℝ)^2) := bsq (bpoint ((178385151 / 500000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE40W_hz16 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B (218178737902707199 / 250000000000000000) (218178737902707199 / 250000000000000000) ((1 : ℝ) - (((178385151 / 500000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowGroupedE40W_hz15 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40W_hz17 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B (934192138486954297 / 1000000000000000000) (467096069243477149 / 500000000000000000) (√((1 : ℝ) - (((178385151 / 500000000) : ℝ)^2))) := bsqrt (lowGroupedE40W_hz16 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE40W_hz18 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B (59472518655114887 / 200000000000000000) (74340648318893609 / 250000000000000000) ((√((1 : ℝ) - (((178385151 / 500000000) : ℝ)^2))) / Real.pi) := bdiv (lowGroupedE40W_hz17 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE40W_hz19 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B (1758512591646257 / 8000000000000000) (27476759257733783 / 125000000000000000) (((178385151 / 500000000) : ℝ) * (kdot ((178385151 / 500000000)))) := bmul (bpoint ((178385151 / 500000000) : ℝ)) (lowGroupedE40W_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40W_hz20 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B (6464708340391957 / 12500000000000000) (5171766673374447 / 10000000000000000) (((√((1 : ℝ) - (((178385151 / 500000000) : ℝ)^2))) / Real.pi) + (((178385151 / 500000000) : ℝ) * (kdot ((178385151 / 500000000))))) := badd (lowGroupedE40W_hz18 hx hc) (lowGroupedE40W_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40W_hz21 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B (6464708340391957 / 12500000000000000) (5171766673374447 / 10000000000000000) (kappa ((178385151 / 500000000))) := by rw [kappa_eq]; exact (lowGroupedE40W_hz20 hx hc)

theorem lowGroupedE40W_hz22 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B (150894294212315051 / 200000000000000000) (377235735530787629 / 500000000000000000) (kdot ((716969799 / 1000000000))) := by
    constructor
    · apply bkdot_lower (q := (406008440154170611 / 1000000000000000000)) (a := (192837655689916033 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (40600844015417061 / 100000000000000000)) (a := (1506544185077469 / 3906250000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE40W_hz23 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B (514045692678100401 / 1000000000000000000) (514045692678100401 / 1000000000000000000) (((716969799 / 1000000000) : ℝ)^2) := bsq (bpoint ((716969799 / 1000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE40W_hz24 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B (485954307321899599 / 1000000000000000000) (485954307321899599 / 1000000000000000000) ((1 : ℝ) - (((716969799 / 1000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowGroupedE40W_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40W_hz25 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B (348552114941904921 / 500000000000000000) (697104229883809843 / 1000000000000000000) (√((1 : ℝ) - (((716969799 / 1000000000) : ℝ)^2))) := bsqrt (lowGroupedE40W_hz24 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE40W_hz26 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B (110947584036277279 / 500000000000000000) (221895168072554559 / 1000000000000000000) ((√((1 : ℝ) - (((716969799 / 1000000000) : ℝ)^2))) / Real.pi) := bdiv (lowGroupedE40W_hz25 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE40W_hz27 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B (540933258958251927 / 1000000000000000000) (54093325895825193 / 100000000000000000) (((716969799 / 1000000000) : ℝ) * (kdot ((716969799 / 1000000000)))) := bmul (bpoint ((716969799 / 1000000000) : ℝ)) (lowGroupedE40W_hz22 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40W_hz28 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B (152565685406161297 / 200000000000000000) (762828427030806489 / 1000000000000000000) (((√((1 : ℝ) - (((716969799 / 1000000000) : ℝ)^2))) / Real.pi) + (((716969799 / 1000000000) : ℝ) * (kdot ((716969799 / 1000000000))))) := badd (lowGroupedE40W_hz26 hx hc) (lowGroupedE40W_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40W_hz29 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B (152565685406161297 / 200000000000000000) (762828427030806489 / 1000000000000000000) (kappa ((716969799 / 1000000000))) := by rw [kappa_eq]; exact (lowGroupedE40W_hz28 hx hc)

theorem lowGroupedE40W_hz30 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B (6464708340391957 / 12500000000000000) (762828427030806489 / 1000000000000000000) (kappa c) := bkappa (lowGroupedE40W_hz1 hx hc) (by norm_num) (by norm_num) (lowGroupedE40W_hz21 hx hc).1 (lowGroupedE40W_hz29 hx hc).2

theorem lowGroupedE40W_hz31 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B (237171572969193511 / 1000000000000000000) (6035291659608043 / 12500000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (lowGroupedE40W_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40W_hz32 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B (237171572969193511 / 500000000000000000) (6035291659608043 / 6250000000000000) ((2 : ℝ) * ((1 : ℝ) - (kappa c))) := bmul (bpoint (2 : ℝ)) (lowGroupedE40W_hz31 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40W_hz33 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B 0 (1 / 8000000) ((8 : ℝ) * (x^2)) := bmul (bpoint (8 : ℝ)) (lowGroupedE40W_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40W_hz34 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B (237171510469193511 / 500000000000000000) (6035291659608043 / 6250000000000000) (((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2))) := bsub (lowGroupedE40W_hz32 hx hc) (lowGroupedE40W_hz33 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40W_hz35 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B (344362824989278939 / 500000000000000000) (196534644837726957 / 200000000000000000) (√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) := bsqrt (lowGroupedE40W_hz34 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE40W_hz36 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B (6782329983125268139 / 250000000000000000) (13564659966250536279 / 500000000000000000) ((2 : ℝ) * (√(184 : ℝ))) := bmul (bpoint (2 : ℝ)) (lowGroupedE40W_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40W_hz37 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B 0 (678232998312527 / 200000000000000000) (((2 : ℝ) * (√(184 : ℝ))) * x) := bmul (lowGroupedE40W_hz36 hx hc) (lowGroupedE40W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40W_hz38 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B (685334484986995243 / 1000000000000000000) (196534644837726957 / 200000000000000000) ((√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) - (((2 : ℝ) * (√(184 : ℝ))) * x)) := bsub (lowGroupedE40W_hz35 hx hc) (lowGroupedE40W_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40W_hz39 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B (685334484986995243 / 1000000000000000000) (196534644837726957 / 200000000000000000) (ndm x c) := by
    convert (lowGroupedE40W_hz38 hx hc) using 1 <;>
      norm_num [ndm] <;> ring

theorem lowGroupedE40W_hz40 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B 1 (1003394039991562637 / 1000000000000000000) ((nap x)^2) := bsq (lowGroupedE40W_hz7 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE40W_hz41 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B 2 (1003394039991562637 / 500000000000000000) ((2 : ℝ) * ((nap x)^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE40W_hz40 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40W_hz42 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B (58710419539048751 / 125000000000000000) (965646665537286881 / 1000000000000000000) ((ndm x c)^2) := bsq (lowGroupedE40W_hz39 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE40W_hz43 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B (1034353334462713119 / 1000000000000000000) (768552361835367633 / 500000000000000000) (((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) := bsub (lowGroupedE40W_hz41 hx hc) (lowGroupedE40W_hz42 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40W_hz44 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B (199322335762284863 / 200000000000000000) 1 ((nam x)^2) := bsq (lowGroupedE40W_hz13 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE40W_hz45 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B (199322335762284863 / 100000000000000000) 2 ((2 : ℝ) * ((nam x)^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE40W_hz44 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40W_hz46 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B (517176667231356559 / 1000000000000000000) (385582658810478711 / 500000000000000000) ((((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) / ((2 : ℝ) * ((nam x)^2))) := bdiv (lowGroupedE40W_hz43 hx hc) (lowGroupedE40W_hz45 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE40W_hz47 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B (517176667231356559 / 1000000000000000000) (385582658810478711 / 500000000000000000) (nc1 x c) := by
    convert (lowGroupedE40W_hz46 hx hc) using 1 <;>
      norm_num [nc1] <;> ring

theorem lowGroupedE40W_hz48 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B (673016987496532661 / 1000000000000000000) (67301698749654973 / 100000000000000000) (kdot ((517176667231356559 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (112825182036819863 / 200000000000000000)) (a := (513623714964776249 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (282062955092049657 / 500000000000000000)) (a := (513623714964749439 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE40W_hz49 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B (195081456927149209 / 250000000000000000) (390162913854298419 / 500000000000000000) (kdot ((385582658810478711 / 500000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (71888822396567809 / 200000000000000000)) (a := (86265845731761337 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (89861027995709761 / 250000000000000000)) (a := (172531691463522673 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE40W_hz50 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B (673016987496532661 / 1000000000000000000) (390162913854298419 / 500000000000000000) (kdot (nc1 x c)) := bkdot (lowGroupedE40W_hz47 hx hc) (lowGroupedE40W_hz48 hx hc).1 (lowGroupedE40W_hz49 hx hc).2

theorem lowGroupedE40W_hz51 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE40W_hz52 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B 0 (59947894041409 / 100000000000000000) ((√(23 : ℝ)) * x) := bmul (lowGroupedE40W_hz51 hx hc) (lowGroupedE40W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40W_hz53 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B (1 / 2) (50059947894041409 / 100000000000000000) (((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)) := badd (bpoint ((1 / 2) : ℝ)) (lowGroupedE40W_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40W_hz54 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B (33650849374826633 / 100000000000000000) (390162913854298419 / 1000000000000000000) ((kdot (nc1 x c)) / (2 : ℝ)) := bdiv (lowGroupedE40W_hz50 hx hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE40W_hz55 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B (33650849374826633 / 100000000000000000) (390762392794712509 / 1000000000000000000) (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)) := badd (lowGroupedE40W_hz54 hx hc) (lowGroupedE40W_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40W_hz56 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B (377235735530787627 / 1000000000000000000) (377235735530787629 / 1000000000000000000) ((kdot ((716969799 / 1000000000))) / (2 : ℝ)) := bdiv (lowGroupedE40W_hz22 hx hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE40W_hz57 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B (377235735530787627 / 1000000000000000000) (377835214471201719 / 1000000000000000000) (((kdot ((716969799 / 1000000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x)) := badd (lowGroupedE40W_hz56 hx hc) (lowGroupedE40W_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40W_hz58 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B (176776695296636881 / 250000000000000000) (353765274914177413 / 500000000000000000) (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE40W_hz53 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE40W_hz59 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGroupedE40W_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE40W_hz60 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B (176776695296636881 / 250000000000000000) (28748435588634151 / 40000000000000000) ((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) := badd (lowGroupedE40W_hz58 hx hc) (lowGroupedE40W_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40W_hz61 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B 0 (59947894041409 / 50000000000000000) ((√(92 : ℝ)) * x) := bmul (lowGroupedE40W_hz3 hx hc) (lowGroupedE40W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40W_hz62 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B (176776695296636881 / 250000000000000000) (143981969519336391 / 200000000000000000) (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE40W_hz60 hx hc) (lowGroupedE40W_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40W_hz63 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B (499999999999999999 / 500000000000000000) (1018106270157175527 / 1000000000000000000) ((√(2 : ℝ)) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE40W_hz4 hx hc) (lowGroupedE40W_hz62 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40W_hz64 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B (499999999999999999 / 500000000000000000) (1018106270157175527 / 1000000000000000000) (neb x (1/2+√23*x)) := by
    convert (lowGroupedE40W_hz63 hx hc) using 1 <;>
      norm_num [neb] <;> ring

theorem lowGroupedE40W_hz65 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B (38387199584199147 / 62500000000000000) (76835377438472487 / 125000000000000000) (√(((kdot ((716969799 / 1000000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE40W_hz57 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE40W_hz66 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B (38387199584199147 / 62500000000000000) (125172671879055769 / 200000000000000000) ((√(((kdot ((716969799 / 1000000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) := badd (lowGroupedE40W_hz65 hx hc) (lowGroupedE40W_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40W_hz67 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B (38387199584199147 / 62500000000000000) (25082492691044281 / 40000000000000000) (((√(((kdot ((716969799 / 1000000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE40W_hz66 hx hc) (lowGroupedE40W_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40W_hz68 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B (434301586187978149 / 500000000000000000) (8868000335449713 / 10000000000000000) ((√(2 : ℝ)) * (((√(((kdot ((716969799 / 1000000000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE40W_hz4 hx hc) (lowGroupedE40W_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40W_hz69 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B (434301586187978149 / 500000000000000000) (8868000335449713 / 10000000000000000) (neb x (kdot (716969799 / 1000000000)/2+√23*x)) := by
    convert (lowGroupedE40W_hz68 hx hc) using 1 <;>
      norm_num [neb] <;> ring

theorem lowGroupedE40W_hz70 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B 0 (7905694150420949 / 500000000000000000) ((√(2 : ℝ)) * (√x)) := bmul (lowGroupedE40W_hz4 hx hc) (lowGroupedE40W_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40W_hz71 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B 1 (507905694150420949 / 500000000000000000) (((√(2 : ℝ)) * (√x)) + (1 : ℝ)) := badd (lowGroupedE40W_hz70 hx hc) (bpoint (1 : ℝ)) (by norm_num) (by norm_num)

theorem lowGroupedE40W_hz72 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B 0 (107238052947636089 / 1000000000000000000) ((√(92 : ℝ)) * (√x)) := bmul (lowGroupedE40W_hz3 hx hc) (lowGroupedE40W_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40W_hz73 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B 1 (1123049441248477987 / 1000000000000000000) ((((√(2 : ℝ)) * (√x)) + (1 : ℝ)) + ((√(92 : ℝ)) * (√x))) := badd (lowGroupedE40W_hz71 hx hc) (lowGroupedE40W_hz72 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40W_hz74 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (12408060554915031 / 7812500000000000) ((√(2 : ℝ)) * ((((√(2 : ℝ)) * (√x)) + (1 : ℝ)) + ((√(92 : ℝ)) * (√x)))) := bmul (lowGroupedE40W_hz4 hx hc) (lowGroupedE40W_hz73 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40W_hz75 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (12408060554915031 / 7812500000000000) (np1 x) := by
    convert (lowGroupedE40W_hz74 hx hc) using 1 <;>
      norm_num [np1] <;> ring

theorem lowGroupedE40W_hz76 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B (11005876608998534131 / 1000000000000000000) (11005876608998534133 / 1000000000000000000) ((√(2 : ℝ)) + (√(92 : ℝ))) := badd (lowGroupedE40W_hz4 hx hc) (lowGroupedE40W_hz3 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40W_hz77 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B 0 (1375734576124817 / 1000000000000000000) (((√(2 : ℝ)) + (√(92 : ℝ))) * x) := bmul (lowGroupedE40W_hz76 hx hc) (lowGroupedE40W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40W_hz78 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B 1 (1001375734576124817 / 1000000000000000000) ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x)) := badd (bpoint (1 : ℝ)) (lowGroupedE40W_hz77 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40W_hz79 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (1416159144868876367 / 1000000000000000000) ((√(2 : ℝ)) * ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x))) := bmul (lowGroupedE40W_hz4 hx hc) (lowGroupedE40W_hz78 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40W_hz80 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B (1999999999999999997 / 1000000000000000000) (140574307399437647 / 62500000000000000) (((√(2 : ℝ)) * ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x))) * (np1 x)) := bmul (lowGroupedE40W_hz79 hx hc) (lowGroupedE40W_hz75 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40W_hz81 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B (1999999999999999997 / 1000000000000000000) (140574307399437647 / 62500000000000000) (ntf x (np1 x)) := by
    convert (lowGroupedE40W_hz80 hx hc) using 1 <;>
      norm_num [ntf] <;> ring

theorem lowGroupedE40W_hz82 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (1430024950673936947 / 1000000000000000000) (((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) := badd (lowGroupedE40W_hz70 hx hc) (lowGroupedE40W_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40W_hz83 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B (176776695296636881 / 125000000000000000) (384315750905393259 / 250000000000000000) ((((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) + ((√(92 : ℝ)) * (√x))) := badd (lowGroupedE40W_hz82 hx hc) (lowGroupedE40W_hz72 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40W_hz84 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B (1999999999999999997 / 1000000000000000000) (2174018188656028919 / 1000000000000000000) ((√(2 : ℝ)) * ((((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) + ((√(92 : ℝ)) * (√x)))) := bmul (lowGroupedE40W_hz4 hx hc) (lowGroupedE40W_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40W_hz85 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B (1999999999999999997 / 1000000000000000000) (2174018188656028919 / 1000000000000000000) (nz x) := by
    convert (lowGroupedE40W_hz84 hx hc) using 1 <;>
      norm_num [nz] <;> ring

theorem lowGroupedE40W_hz86 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B (290046760776717833 / 500000000000000000) (4883671129473109 / 7812500000000000) (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE40W_hz55 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE40W_hz87 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B (290046760776717833 / 250000000000000000) (4883671129473109 / 3906250000000000) ((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) := bmul (bpoint (2 : ℝ)) (lowGroupedE40W_hz86 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40W_hz88 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B 0 (8505173090835039 / 500000000000000000) (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE40W_hz70 hx hc) (lowGroupedE40W_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40W_hz89 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B 0 (5316667939184979 / 250000000000000000) (((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE40W_hz87 hx hc) (lowGroupedE40W_hz88 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40W_hz90 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B 0 (144675938610129 / 500000000000000000) ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2) := bsq (lowGroupedE40W_hz88 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE40W_hz91 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B 0 (10778011816980087 / 500000000000000000) ((((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) + ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2)) := badd (lowGroupedE40W_hz89 hx hc) (lowGroupedE40W_hz90 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40W_hz92 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B 0 (10778011816980087 / 250000000000000000) ((2 : ℝ) * ((((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) + ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2))) := bmul (bpoint (2 : ℝ)) (lowGroupedE40W_hz91 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40W_hz93 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B 0 (10778011816980087 / 250000000000000000) (nrad x (kdot (nc1 x c)/2+√23*x)) := by
    convert (lowGroupedE40W_hz92 hx hc) using 1 <;>
      norm_num [nrad] <;> ring

theorem lowGroupedE40W_hz94 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B (999999999999999997 / 250000000000000000) (5058850790612887039 / 1000000000000000000) ((ntf x (np1 x))^2) := bsq (lowGroupedE40W_hz81 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE40W_hz95 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B 0 (632356348826611 / 1000000000000000000) (((ntf x (np1 x))^2) * x) := bmul (lowGroupedE40W_hz94 hx hc) (lowGroupedE40W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40W_hz96 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B (1999999999999999997 / 500000000000000000) (140574307399437647 / 31250000000000000) ((2 : ℝ) * (ntf x (np1 x))) := bmul (bpoint (2 : ℝ)) (lowGroupedE40W_hz81 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40W_hz97 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B (999999999999999997 / 125000000000000000) (611222202288202473 / 62500000000000000) (((2 : ℝ) * (ntf x (np1 x))) * (nz x)) := bmul (lowGroupedE40W_hz96 hx hc) (lowGroupedE40W_hz85 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40W_hz98 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B (199999999999999999 / 25000000000000000) (1991325301148468661 / 200000000000000000) ((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) := bmul (lowGroupedE40W_hz97 hx hc) (lowGroupedE40W_hz64 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40W_hz99 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B 0 (1244578313217793 / 1000000000000000000) (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x) := bmul (lowGroupedE40W_hz98 hx hc) (lowGroupedE40W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40W_hz100 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B 0 (469233665511101 / 250000000000000000) ((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) := badd (lowGroupedE40W_hz95 hx hc) (lowGroupedE40W_hz99 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40W_hz101 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B (249999999999999999 / 250000000000000000) (6478377358333473 / 6250000000000000) ((neb x (1/2+√23*x))^2) := bsq (lowGroupedE40W_hz64 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE40W_hz102 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B 0 (5585922217837953 / 125000000000000000) ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2)) := bmul (lowGroupedE40W_hz93 hx hc) (lowGroupedE40W_hz101 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40W_hz103 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B 0 (11641078101187007 / 250000000000000000) (((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) + ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2))) := badd (lowGroupedE40W_hz100 hx hc) (lowGroupedE40W_hz102 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40W_hz104 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B (33650849374826633 / 50000000000000000) (390762392794712509 / 500000000000000000) ((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bmul (bpoint (2 : ℝ)) (lowGroupedE40W_hz55 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40W_hz105 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B (3017885884246301 / 4000000000000000) (786414299495362223 / 1000000000000000000) ((neb x (kdot (716969799 / 1000000000)/2+√23*x))^2) := bsq (lowGroupedE40W_hz69 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE40W_hz106 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B (1999999999999999997 / 1000000000000000000) (2522480094977037223 / 1000000000000000000) ((np1 x)^2) := bsq (lowGroupedE40W_hz75 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE40W_hz107 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B 0 (31531001187213 / 100000000000000000) (((np1 x)^2) * x) := bmul (lowGroupedE40W_hz106 hx hc) (lowGroupedE40W_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40W_hz108 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B (3017885884246301 / 4000000000000000) (786729609507234353 / 1000000000000000000) (((neb x (kdot (716969799 / 1000000000)/2+√23*x))^2) + (((np1 x)^2) * x)) := badd (lowGroupedE40W_hz105 hx hc) (lowGroupedE40W_hz107 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40W_hz109 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B (63471514575742349 / 125000000000000000) (307424344693496699 / 500000000000000000) (((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) * (((neb x (kdot (716969799 / 1000000000)/2+√23*x))^2) + (((np1 x)^2) * x))) := bmul (lowGroupedE40W_hz104 hx hc) (lowGroupedE40W_hz108 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40W_hz110 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B (63471514575742349 / 125000000000000000) (330706500895870713 / 500000000000000000) ((((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) + ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2))) + (((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) * (((neb x (kdot (716969799 / 1000000000)/2+√23*x))^2) + (((np1 x)^2) * x)))) := badd (lowGroupedE40W_hz103 hx hc) (lowGroupedE40W_hz109 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40W_hz111 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) : B (63471514575742349 / 125000000000000000) (330706500895870713 / 500000000000000000) (ne x (kdot (nc1 x c)/2+√23*x) (neb x (1/2+√23*x)) (neb x (kdot (716969799 / 1000000000)/2+√23*x)^2) (np1 x)) := by
    convert (lowGroupedE40W_hz110 hx hc) using 1 <;>
      norm_num [ne] <;> ring

theorem lowGroupedE40W {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (178385151 / 500000000) (716969799 / 1000000000) c) :
    ne x (kdot (nc1 x c)/2+√23*x) (neb x (1/2+√23*x))
      (neb x (kdot (716969799 / 1000000000)/2+√23*x)^2) (np1 x) ≤ (330706501 / 500000000) :=
  (lowGroupedE40W_hz111 hx hc).2.trans (by norm_num)

theorem lowGroupedE40C_hz0 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B 0 (1 / 8000) x := hx

theorem lowGroupedE40C_hz1 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B (432260647 / 1000000000) (38043751 / 62500000) c := hc

theorem lowGroupedE40C_hz2 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B (6782329983125268139 / 500000000000000000) (13564659966250536279 / 1000000000000000000) (√(184 : ℝ)) := bsqrt (bpoint (184 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE40C_hz3 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE40C_hz4 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B (176776695296636881 / 125000000000000000) (1414213562373095049 / 1000000000000000000) (√(2 : ℝ)) := bsqrt (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE40C_hz5 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B 0 (847791247890659 / 500000000000000000) ((√(184 : ℝ)) * x) := bmul (lowGroupedE40C_hz2 hx hc) (lowGroupedE40C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40C_hz6 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B 1 (500847791247890659 / 500000000000000000) ((1 : ℝ) + ((√(184 : ℝ)) * x)) := badd (bpoint (1 : ℝ)) (lowGroupedE40C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40C_hz7 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B 1 (500847791247890659 / 500000000000000000) (nap x) := by
    convert (lowGroupedE40C_hz6 hx hc) using 1 <;>
      norm_num [nap] <;> ring

theorem lowGroupedE40C_hz8 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B 0 (1 / 64000000) (x^2) := bsq (lowGroupedE40C_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE40C_hz9 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B 0 (1 / 32000000) ((2 : ℝ) * (x^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE40C_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40C_hz10 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B (31999999 / 32000000) 1 ((1 : ℝ) - ((2 : ℝ) * (x^2))) := bsub (bpoint (1 : ℝ)) (lowGroupedE40C_hz9 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40C_hz11 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B (999999984374999877 / 1000000000000000000) 1 (√((1 : ℝ) - ((2 : ℝ) * (x^2)))) := bsqrt (lowGroupedE40C_hz10 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE40C_hz12 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B (998304401879218559 / 1000000000000000000) 1 ((√((1 : ℝ) - ((2 : ℝ) * (x^2)))) - ((√(184 : ℝ)) * x)) := bsub (lowGroupedE40C_hz11 hx hc) (lowGroupedE40C_hz5 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40C_hz13 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B (998304401879218559 / 1000000000000000000) 1 (nam x) := by
    convert (lowGroupedE40C_hz12 hx hc) using 1 <;>
      norm_num [nam] <;> ring

theorem lowGroupedE40C_hz14 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B (642283956979488543 / 1000000000000000000) (160570989245798463 / 250000000000000000) (kdot ((432260647 / 1000000000))) := by
    constructor
    · apply bkdot_lower (q := (629598188195234669 / 1000000000000000000)) (a := (561899046412224611 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (157399547048808667 / 250000000000000000)) (a := (70237380800800541 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE40C_hz15 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B (186849266944858609 / 1000000000000000000) (186849266944858609 / 1000000000000000000) (((432260647 / 1000000000) : ℝ)^2) := bsq (bpoint ((432260647 / 1000000000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE40C_hz16 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B (813150733055141391 / 1000000000000000000) (813150733055141391 / 1000000000000000000) ((1 : ℝ) - (((432260647 / 1000000000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowGroupedE40C_hz15 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40C_hz17 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B (112718588546816821 / 125000000000000000) (901748708374534569 / 1000000000000000000) (√((1 : ℝ) - (((432260647 / 1000000000) : ℝ)^2))) := bsqrt (lowGroupedE40C_hz16 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE40C_hz18 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B (35879441091134793 / 125000000000000000) (57407105745815669 / 200000000000000000) ((√((1 : ℝ) - (((432260647 / 1000000000) : ℝ)^2))) / Real.pi) := bdiv (lowGroupedE40C_hz17 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE40C_hz19 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B (277634078801673883 / 1000000000000000000) (277634078803275543 / 1000000000000000000) (((432260647 / 1000000000) : ℝ) * (kdot ((432260647 / 1000000000)))) := bmul (bpoint ((432260647 / 1000000000) : ℝ)) (lowGroupedE40C_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40C_hz20 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B (564669607530752227 / 1000000000000000000) (17645925235386059 / 31250000000000000) (((√((1 : ℝ) - (((432260647 / 1000000000) : ℝ)^2))) / Real.pi) + (((432260647 / 1000000000) : ℝ) * (kdot ((432260647 / 1000000000))))) := badd (lowGroupedE40C_hz18 hx hc) (lowGroupedE40C_hz19 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40C_hz21 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B (564669607530752227 / 1000000000000000000) (17645925235386059 / 31250000000000000) (kappa ((432260647 / 1000000000))) := by rw [kappa_eq]; exact (lowGroupedE40C_hz20 hx hc)

theorem lowGroupedE40C_hz22 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B (708308693886686831 / 1000000000000000000) (88538586735835857 / 125000000000000000) (kdot ((38043751 / 62500000))) := by
    constructor
    · apply bkdot_lower (q := (493193542912199787 / 1000000000000000000)) (a := (229093816100399049 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (246596771456099893 / 500000000000000000)) (a := (22909381610039903 / 50000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE40C_hz23 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B (1447326990150001 / 3906250000000000) (1447326990150001 / 3906250000000000) (((38043751 / 62500000) : ℝ)^2) := bsq (bpoint ((38043751 / 62500000) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE40C_hz24 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B (2458923009849999 / 3906250000000000) (2458923009849999 / 3906250000000000) ((1 : ℝ) - (((38043751 / 62500000) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowGroupedE40C_hz23 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40C_hz25 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B (396700230186976241 / 500000000000000000) (793400460373952483 / 1000000000000000000) (√((1 : ℝ) - (((38043751 / 62500000) : ℝ)^2))) := bsqrt (lowGroupedE40C_hz24 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE40C_hz26 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B (50509442047959987 / 200000000000000000) (1973025079998437 / 7812500000000000) ((√((1 : ℝ) - (((38043751 / 62500000) : ℝ)^2))) / Real.pi) := bdiv (lowGroupedE40C_hz25 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE40C_hz27 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B (1684169973835021 / 3906250000000000) (26946719581360337 / 62500000000000000) (((38043751 / 62500000) : ℝ) * (kdot ((38043751 / 62500000)))) := bmul (bpoint ((38043751 / 62500000) : ℝ)) (lowGroupedE40C_hz22 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40C_hz28 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B (683694723541565311 / 1000000000000000000) (42730920221347833 / 62500000000000000) (((√((1 : ℝ) - (((38043751 / 62500000) : ℝ)^2))) / Real.pi) + (((38043751 / 62500000) : ℝ) * (kdot ((38043751 / 62500000))))) := badd (lowGroupedE40C_hz26 hx hc) (lowGroupedE40C_hz27 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40C_hz29 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B (683694723541565311 / 1000000000000000000) (42730920221347833 / 62500000000000000) (kappa ((38043751 / 62500000))) := by rw [kappa_eq]; exact (lowGroupedE40C_hz28 hx hc)

theorem lowGroupedE40C_hz30 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B (564669607530752227 / 1000000000000000000) (42730920221347833 / 62500000000000000) (kappa c) := bkappa (lowGroupedE40C_hz1 hx hc) (by norm_num) (by norm_num) (lowGroupedE40C_hz21 hx hc).1 (lowGroupedE40C_hz29 hx hc).2

theorem lowGroupedE40C_hz31 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B (19769079778652167 / 62500000000000000) (435330392469247773 / 1000000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (lowGroupedE40C_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40C_hz32 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B (19769079778652167 / 31250000000000000) (435330392469247773 / 500000000000000000) ((2 : ℝ) * ((1 : ℝ) - (kappa c))) := bmul (bpoint (2 : ℝ)) (lowGroupedE40C_hz31 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40C_hz33 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B 0 (1 / 8000000) ((8 : ℝ) * (x^2)) := bmul (bpoint (8 : ℝ)) (lowGroupedE40C_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40C_hz34 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B (19769075872402167 / 31250000000000000) (435330392469247773 / 500000000000000000) (((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2))) := bsub (lowGroupedE40C_hz32 hx hc) (lowGroupedE40C_hz33 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40C_hz35 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B (397684054217939867 / 500000000000000000) (933092055982953671 / 1000000000000000000) (√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) := bsqrt (lowGroupedE40C_hz34 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE40C_hz36 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B (6782329983125268139 / 250000000000000000) (13564659966250536279 / 500000000000000000) ((2 : ℝ) * (√(184 : ℝ))) := bmul (bpoint (2 : ℝ)) (lowGroupedE40C_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40C_hz37 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B 0 (678232998312527 / 200000000000000000) (((2 : ℝ) * (√(184 : ℝ))) * x) := bmul (lowGroupedE40C_hz36 hx hc) (lowGroupedE40C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40C_hz38 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B (791976943444317099 / 1000000000000000000) (933092055982953671 / 1000000000000000000) ((√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) - (((2 : ℝ) * (√(184 : ℝ))) * x)) := bsub (lowGroupedE40C_hz35 hx hc) (lowGroupedE40C_hz37 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40C_hz39 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B (791976943444317099 / 1000000000000000000) (933092055982953671 / 1000000000000000000) (ndm x c) := by
    convert (lowGroupedE40C_hz38 hx hc) using 1 <;>
      norm_num [ndm] <;> ring

theorem lowGroupedE40C_hz40 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B 1 (1003394039991562637 / 1000000000000000000) ((nap x)^2) := bsq (lowGroupedE40C_hz7 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE40C_hz41 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B 2 (1003394039991562637 / 500000000000000000) ((2 : ℝ) * ((nap x)^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE40C_hz40 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40C_hz42 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B (156806869736850761 / 250000000000000000) (217665196234623887 / 250000000000000000) ((ndm x c)^2) := bsq (lowGroupedE40C_hz39 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE40C_hz43 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B (282334803765376113 / 250000000000000000) (137956060103572223 / 100000000000000000) (((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) := bsub (lowGroupedE40C_hz41 hx hc) (lowGroupedE40C_hz42 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40C_hz44 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B (199322335762284863 / 200000000000000000) 1 ((nam x)^2) := bsq (lowGroupedE40C_hz13 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE40C_hz45 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B (199322335762284863 / 100000000000000000) 2 ((2 : ℝ) * ((nam x)^2)) := bmul (bpoint (2 : ℝ)) (lowGroupedE40C_hz44 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40C_hz46 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B (282334803765376113 / 500000000000000000) (692125443824323421 / 1000000000000000000) ((((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) / ((2 : ℝ) * ((nam x)^2))) := bdiv (lowGroupedE40C_hz43 hx hc) (lowGroupedE40C_hz45 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE40C_hz47 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B (282334803765376113 / 500000000000000000) (692125443824323421 / 1000000000000000000) (nc1 x c) := by
    convert (lowGroupedE40C_hz46 hx hc) using 1 <;>
      norm_num [nc1] <;> ring

theorem lowGroupedE40C_hz48 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B (690996396738842017 / 1000000000000000000) (690996396738842653 / 1000000000000000000) (kdot ((282334803765376113 / 500000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (263735246988119783 / 500000000000000000)) (a := (485381724969014497 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (105494098795247913 / 200000000000000000)) (a := (485381724969013499 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE40C_hz49 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B (148665102828078849 / 200000000000000000) (743325514140394247 / 1000000000000000000) (kdot ((692125443824323421 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (426550663142306879 / 1000000000000000000)) (a := (50397917446279669 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (213275331571153439 / 500000000000000000)) (a := (8063666791404747 / 20000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowGroupedE40C_hz50 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B (690996396738842017 / 1000000000000000000) (743325514140394247 / 1000000000000000000) (kdot (nc1 x c)) := bkdot (lowGroupedE40C_hz47 hx hc) (lowGroupedE40C_hz48 hx hc).1 (lowGroupedE40C_hz49 hx hc).2

theorem lowGroupedE40C_hz51 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE40C_hz52 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B 0 (59947894041409 / 100000000000000000) ((√(23 : ℝ)) * x) := bmul (lowGroupedE40C_hz51 hx hc) (lowGroupedE40C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40C_hz53 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B (1 / 2) (50059947894041409 / 100000000000000000) (((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)) := badd (bpoint ((1 / 2) : ℝ)) (lowGroupedE40C_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40C_hz54 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B (21593637398088813 / 62500000000000000) (92915689267549281 / 250000000000000000) ((kdot (nc1 x c)) / (2 : ℝ)) := bdiv (lowGroupedE40C_hz50 hx hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE40C_hz55 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B (21593637398088813 / 62500000000000000) (186131118005305607 / 500000000000000000) (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)) := badd (lowGroupedE40C_hz54 hx hc) (lowGroupedE40C_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40C_hz56 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B (70830869388668683 / 200000000000000000) (88538586735835857 / 250000000000000000) ((kdot ((38043751 / 62500000))) / (2 : ℝ)) := bdiv (lowGroupedE40C_hz22 hx hc) (bpoint (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE40C_hz57 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B (70830869388668683 / 200000000000000000) (177376912941878759 / 500000000000000000) (((kdot ((38043751 / 62500000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x)) := badd (lowGroupedE40C_hz56 hx hc) (lowGroupedE40C_hz52 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40C_hz58 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B (176776695296636881 / 250000000000000000) (353765274914177413 / 500000000000000000) (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE40C_hz53 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE40C_hz59 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B 0 (11180339887498949 / 1000000000000000000) (√x) := bsqrt (lowGroupedE40C_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE40C_hz60 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B (176776695296636881 / 250000000000000000) (28748435588634151 / 40000000000000000) ((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) := badd (lowGroupedE40C_hz58 hx hc) (lowGroupedE40C_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40C_hz61 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B 0 (59947894041409 / 50000000000000000) ((√(92 : ℝ)) * x) := bmul (lowGroupedE40C_hz3 hx hc) (lowGroupedE40C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40C_hz62 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B (176776695296636881 / 250000000000000000) (143981969519336391 / 200000000000000000) (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE40C_hz60 hx hc) (lowGroupedE40C_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40C_hz63 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B (499999999999999999 / 500000000000000000) (1018106270157175527 / 1000000000000000000) ((√(2 : ℝ)) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE40C_hz4 hx hc) (lowGroupedE40C_hz62 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40C_hz64 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B (499999999999999999 / 500000000000000000) (1018106270157175527 / 1000000000000000000) (neb x (1/2+√23*x)) := by
    convert (lowGroupedE40C_hz63 hx hc) using 1 <;>
      norm_num [neb] <;> ring

theorem lowGroupedE40C_hz65 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B (595108684983964433 / 1000000000000000000) (297806071917513763 / 500000000000000000) (√(((kdot ((38043751 / 62500000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE40C_hz57 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE40C_hz66 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B (595108684983964433 / 1000000000000000000) (24271699348901059 / 40000000000000000) ((√(((kdot ((38043751 / 62500000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) := badd (lowGroupedE40C_hz65 hx hc) (lowGroupedE40C_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40C_hz67 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B (595108684983964433 / 1000000000000000000) (121598288320670931 / 200000000000000000) (((√(((kdot ((38043751 / 62500000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE40C_hz66 hx hc) (lowGroupedE40C_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40C_hz68 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B (841610773390340357 / 1000000000000000000) (34393189700889351 / 40000000000000000) ((√(2 : ℝ)) * (((√(((kdot ((38043751 / 62500000))) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) + (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE40C_hz4 hx hc) (lowGroupedE40C_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40C_hz69 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B (841610773390340357 / 1000000000000000000) (34393189700889351 / 40000000000000000) (neb x (kdot (38043751 / 62500000)/2+√23*x)) := by
    convert (lowGroupedE40C_hz68 hx hc) using 1 <;>
      norm_num [neb] <;> ring

theorem lowGroupedE40C_hz70 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B 0 (7905694150420949 / 500000000000000000) ((√(2 : ℝ)) * (√x)) := bmul (lowGroupedE40C_hz4 hx hc) (lowGroupedE40C_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40C_hz71 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B 1 (507905694150420949 / 500000000000000000) (((√(2 : ℝ)) * (√x)) + (1 : ℝ)) := badd (lowGroupedE40C_hz70 hx hc) (bpoint (1 : ℝ)) (by norm_num) (by norm_num)

theorem lowGroupedE40C_hz72 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B 0 (107238052947636089 / 1000000000000000000) ((√(92 : ℝ)) * (√x)) := bmul (lowGroupedE40C_hz3 hx hc) (lowGroupedE40C_hz59 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40C_hz73 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B 1 (1123049441248477987 / 1000000000000000000) ((((√(2 : ℝ)) * (√x)) + (1 : ℝ)) + ((√(92 : ℝ)) * (√x))) := badd (lowGroupedE40C_hz71 hx hc) (lowGroupedE40C_hz72 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40C_hz74 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B (176776695296636881 / 125000000000000000) (12408060554915031 / 7812500000000000) ((√(2 : ℝ)) * ((((√(2 : ℝ)) * (√x)) + (1 : ℝ)) + ((√(92 : ℝ)) * (√x)))) := bmul (lowGroupedE40C_hz4 hx hc) (lowGroupedE40C_hz73 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40C_hz75 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B (176776695296636881 / 125000000000000000) (12408060554915031 / 7812500000000000) (np1 x) := by
    convert (lowGroupedE40C_hz74 hx hc) using 1 <;>
      norm_num [np1] <;> ring

theorem lowGroupedE40C_hz76 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B (11005876608998534131 / 1000000000000000000) (11005876608998534133 / 1000000000000000000) ((√(2 : ℝ)) + (√(92 : ℝ))) := badd (lowGroupedE40C_hz4 hx hc) (lowGroupedE40C_hz3 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40C_hz77 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B 0 (1375734576124817 / 1000000000000000000) (((√(2 : ℝ)) + (√(92 : ℝ))) * x) := bmul (lowGroupedE40C_hz76 hx hc) (lowGroupedE40C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40C_hz78 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B 1 (1001375734576124817 / 1000000000000000000) ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x)) := badd (bpoint (1 : ℝ)) (lowGroupedE40C_hz77 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40C_hz79 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B (176776695296636881 / 125000000000000000) (1416159144868876367 / 1000000000000000000) ((√(2 : ℝ)) * ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x))) := bmul (lowGroupedE40C_hz4 hx hc) (lowGroupedE40C_hz78 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40C_hz80 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B (1999999999999999997 / 1000000000000000000) (140574307399437647 / 62500000000000000) (((√(2 : ℝ)) * ((1 : ℝ) + (((√(2 : ℝ)) + (√(92 : ℝ))) * x))) * (np1 x)) := bmul (lowGroupedE40C_hz79 hx hc) (lowGroupedE40C_hz75 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40C_hz81 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B (1999999999999999997 / 1000000000000000000) (140574307399437647 / 62500000000000000) (ntf x (np1 x)) := by
    convert (lowGroupedE40C_hz80 hx hc) using 1 <;>
      norm_num [ntf] <;> ring

theorem lowGroupedE40C_hz82 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B (176776695296636881 / 125000000000000000) (1430024950673936947 / 1000000000000000000) (((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) := badd (lowGroupedE40C_hz70 hx hc) (lowGroupedE40C_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40C_hz83 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B (176776695296636881 / 125000000000000000) (384315750905393259 / 250000000000000000) ((((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) + ((√(92 : ℝ)) * (√x))) := badd (lowGroupedE40C_hz82 hx hc) (lowGroupedE40C_hz72 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40C_hz84 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B (1999999999999999997 / 1000000000000000000) (2174018188656028919 / 1000000000000000000) ((√(2 : ℝ)) * ((((√(2 : ℝ)) * (√x)) + (√(2 : ℝ))) + ((√(92 : ℝ)) * (√x)))) := bmul (lowGroupedE40C_hz4 hx hc) (lowGroupedE40C_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40C_hz85 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B (1999999999999999997 / 1000000000000000000) (2174018188656028919 / 1000000000000000000) (nz x) := by
    convert (lowGroupedE40C_hz84 hx hc) using 1 <;>
      norm_num [nz] <;> ring

theorem lowGroupedE40C_hz86 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B (587790947845763449 / 1000000000000000000) (76266620730604029 / 125000000000000000) (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bsqrt (lowGroupedE40C_hz55 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE40C_hz87 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B (587790947845763449 / 500000000000000000) (76266620730604029 / 62500000000000000) ((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) := bmul (bpoint (2 : ℝ)) (lowGroupedE40C_hz86 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40C_hz88 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B 0 (8505173090835039 / 500000000000000000) (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x)) := badd (lowGroupedE40C_hz70 hx hc) (lowGroupedE40C_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40C_hz89 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B 0 (4151429186347873 / 200000000000000000) (((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) := bmul (lowGroupedE40C_hz87 hx hc) (lowGroupedE40C_hz88 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40C_hz90 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B 0 (144675938610129 / 500000000000000000) ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2) := bsq (lowGroupedE40C_hz88 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE40C_hz91 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B 0 (21046497808959623 / 1000000000000000000) ((((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) + ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2)) := badd (lowGroupedE40C_hz89 hx hc) (lowGroupedE40C_hz90 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40C_hz92 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B 0 (21046497808959623 / 500000000000000000) ((2 : ℝ) * ((((2 : ℝ) * (√(((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x)))) * (((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))) + ((((√(2 : ℝ)) * (√x)) + ((√(92 : ℝ)) * x))^2))) := bmul (bpoint (2 : ℝ)) (lowGroupedE40C_hz91 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40C_hz93 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B 0 (21046497808959623 / 500000000000000000) (nrad x (kdot (nc1 x c)/2+√23*x)) := by
    convert (lowGroupedE40C_hz92 hx hc) using 1 <;>
      norm_num [nrad] <;> ring

theorem lowGroupedE40C_hz94 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B (999999999999999997 / 250000000000000000) (5058850790612887039 / 1000000000000000000) ((ntf x (np1 x))^2) := bsq (lowGroupedE40C_hz81 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE40C_hz95 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B 0 (632356348826611 / 1000000000000000000) (((ntf x (np1 x))^2) * x) := bmul (lowGroupedE40C_hz94 hx hc) (lowGroupedE40C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40C_hz96 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B (1999999999999999997 / 500000000000000000) (140574307399437647 / 31250000000000000) ((2 : ℝ) * (ntf x (np1 x))) := bmul (bpoint (2 : ℝ)) (lowGroupedE40C_hz81 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40C_hz97 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B (999999999999999997 / 125000000000000000) (611222202288202473 / 62500000000000000) (((2 : ℝ) * (ntf x (np1 x))) * (nz x)) := bmul (lowGroupedE40C_hz96 hx hc) (lowGroupedE40C_hz85 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40C_hz98 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B (199999999999999999 / 25000000000000000) (1991325301148468661 / 200000000000000000) ((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) := bmul (lowGroupedE40C_hz97 hx hc) (lowGroupedE40C_hz64 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40C_hz99 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B 0 (1244578313217793 / 1000000000000000000) (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x) := bmul (lowGroupedE40C_hz98 hx hc) (lowGroupedE40C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40C_hz100 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B 0 (469233665511101 / 250000000000000000) ((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) := badd (lowGroupedE40C_hz95 hx hc) (lowGroupedE40C_hz99 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40C_hz101 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B (249999999999999999 / 250000000000000000) (6478377358333473 / 6250000000000000) ((neb x (1/2+√23*x))^2) := bsq (lowGroupedE40C_hz64 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE40C_hz102 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B 0 (43631089560889303 / 1000000000000000000) ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2)) := bmul (lowGroupedE40C_hz93 hx hc) (lowGroupedE40C_hz101 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40C_hz103 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B 0 (45508024222933707 / 1000000000000000000) (((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) + ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2))) := badd (lowGroupedE40C_hz100 hx hc) (lowGroupedE40C_hz102 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40C_hz104 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B (21593637398088813 / 31250000000000000) (186131118005305607 / 250000000000000000) ((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) := bmul (bpoint (2 : ℝ)) (lowGroupedE40C_hz55 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40C_hz105 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B (177077173471671707 / 250000000000000000) (739307186125850829 / 1000000000000000000) ((neb x (kdot (38043751 / 62500000)/2+√23*x))^2) := bsq (lowGroupedE40C_hz69 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE40C_hz106 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B (1999999999999999997 / 1000000000000000000) (2522480094977037223 / 1000000000000000000) ((np1 x)^2) := bsq (lowGroupedE40C_hz75 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowGroupedE40C_hz107 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B 0 (31531001187213 / 100000000000000000) (((np1 x)^2) * x) := bmul (lowGroupedE40C_hz106 hx hc) (lowGroupedE40C_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40C_hz108 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B (177077173471671707 / 250000000000000000) (739622496137722959 / 1000000000000000000) (((neb x (kdot (38043751 / 62500000)/2+√23*x))^2) + (((np1 x)^2) * x)) := badd (lowGroupedE40C_hz105 hx hc) (lowGroupedE40C_hz107 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40C_hz109 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B (489438755254496053 / 1000000000000000000) (550667048431956811 / 1000000000000000000) (((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) * (((neb x (kdot (38043751 / 62500000)/2+√23*x))^2) + (((np1 x)^2) * x))) := bmul (lowGroupedE40C_hz104 hx hc) (lowGroupedE40C_hz108 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40C_hz110 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B (489438755254496053 / 1000000000000000000) (298087536327445259 / 500000000000000000) ((((((ntf x (np1 x))^2) * x) + (((((2 : ℝ) * (ntf x (np1 x))) * (nz x)) * (neb x (1/2+√23*x))) * x)) + ((nrad x (kdot (nc1 x c)/2+√23*x)) * ((neb x (1/2+√23*x))^2))) + (((2 : ℝ) * (((kdot (nc1 x c)) / (2 : ℝ)) + ((√(23 : ℝ)) * x))) * (((neb x (kdot (38043751 / 62500000)/2+√23*x))^2) + (((np1 x)^2) * x)))) := badd (lowGroupedE40C_hz103 hx hc) (lowGroupedE40C_hz109 hx hc) (by norm_num) (by norm_num)

theorem lowGroupedE40C_hz111 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) : B (489438755254496053 / 1000000000000000000) (298087536327445259 / 500000000000000000) (ne x (kdot (nc1 x c)/2+√23*x) (neb x (1/2+√23*x)) (neb x (kdot (38043751 / 62500000)/2+√23*x)^2) (np1 x)) := by
    convert (lowGroupedE40C_hz110 hx hc) using 1 <;>
      norm_num [ne] <;> ring

theorem lowGroupedE40C {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (432260647 / 1000000000) (38043751 / 62500000) c) :
    ne x (kdot (nc1 x c)/2+√23*x) (neb x (1/2+√23*x))
      (neb x (kdot (38043751 / 62500000)/2+√23*x)^2) (np1 x) ≤ (596175073 / 1000000000) :=
  (lowGroupedE40C_hz111 hx hc).2.trans (by norm_num)

end BstLean.BlueprintLow
