import BstLean.Part264bNormalize
namespace BstLean.BlueprintLow
open Real BstLean.Part130 BstLean.Part182 BstLean.Part197 BstLean.Part246 BstLean.Part255
open BstLean.Part264b
theorem lowCoarseS24_hz0 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B 0 (1 / 8000) x := hx

theorem lowCoarseS24_hz1 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B (27 / 50) (11 / 20) c := hc

theorem lowCoarseS24_hz2 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B (6782329983125268139 / 500000000000000000) (13564659966250536279 / 1000000000000000000) (√(184 : ℝ)) := bsqrt (bpoint (184 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS24_hz3 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS24_hz4 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B 0 (847791247890659 / 500000000000000000) ((√(184 : ℝ)) * x) := bmul (lowCoarseS24_hz2 hx hc) (lowCoarseS24_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS24_hz5 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B 1 (500847791247890659 / 500000000000000000) ((1 : ℝ) + ((√(184 : ℝ)) * x)) := badd (bpoint (1 : ℝ)) (lowCoarseS24_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS24_hz6 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B 1 (500847791247890659 / 500000000000000000) (nap x) := by
    convert (lowCoarseS24_hz5 hx hc) using 1 <;>
      norm_num [nap] <;> ring

theorem lowCoarseS24_hz7 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B 0 (1 / 64000000) (x^2) := bsq (lowCoarseS24_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS24_hz8 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B 0 (1 / 32000000) ((2 : ℝ) * (x^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS24_hz7 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS24_hz9 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B (31999999 / 32000000) 1 ((1 : ℝ) - ((2 : ℝ) * (x^2))) := bsub (bpoint (1 : ℝ)) (lowCoarseS24_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS24_hz10 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B (999999984374999877 / 1000000000000000000) 1 (√((1 : ℝ) - ((2 : ℝ) * (x^2)))) := bsqrt (lowCoarseS24_hz9 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS24_hz11 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B (998304401879218559 / 1000000000000000000) 1 ((√((1 : ℝ) - ((2 : ℝ) * (x^2)))) - ((√(184 : ℝ)) * x)) := bsub (lowCoarseS24_hz10 hx hc) (lowCoarseS24_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS24_hz12 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B (998304401879218559 / 1000000000000000000) 1 (nam x) := by
    convert (lowCoarseS24_hz11 hx hc) using 1 <;>
      norm_num [nam] <;> ring

theorem lowCoarseS24_hz13 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B (340787885684049643 / 500000000000000000) (340787885684051451 / 500000000000000000) (kdot ((27 / 50))) := by
    constructor
    · apply bkdot_lower (q := (68316965625002639 / 125000000000000000)) (a := (50017960869748799 / 100000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (546535725000021111 / 1000000000000000000)) (a := (500179608697482311 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS24_hz14 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B (729 / 2500) (729 / 2500) (((27 / 50) : ℝ)^2) := bsq (bpoint ((27 / 50) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS24_hz15 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B (1771 / 2500) (1771 / 2500) ((1 : ℝ) - (((27 / 50) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS24_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS24_hz16 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B (841665016500032511 / 1000000000000000000) (821938492675813 / 976562500000000) (√((1 : ℝ) - (((27 / 50) : ℝ)^2))) := bsqrt (lowCoarseS24_hz15 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS24_hz17 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B (133955147803501823 / 500000000000000000) (267910295607003647 / 1000000000000000000) ((√((1 : ℝ) - (((27 / 50) : ℝ)^2))) / Real.pi) := bdiv (lowCoarseS24_hz16 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS24_hz18 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B (184025458269386807 / 500000000000000000) (23003182283673473 / 62500000000000000) (((27 / 50) : ℝ) * (kdot ((27 / 50)))) := bmul (bpoint ((27 / 50) : ℝ)) (lowCoarseS24_hz13 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS24_hz19 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B (31798060607288863 / 50000000000000000) (127192242429155843 / 200000000000000000) (((√((1 : ℝ) - (((27 / 50) : ℝ)^2))) / Real.pi) + (((27 / 50) : ℝ) * (kdot ((27 / 50))))) := badd (lowCoarseS24_hz17 hx hc) (lowCoarseS24_hz18 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS24_hz20 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B (31798060607288863 / 50000000000000000) (127192242429155843 / 200000000000000000) (kappa ((27 / 50))) := by rw [kappa_eq]; exact (lowCoarseS24_hz19 hx hc)

theorem lowCoarseS24_hz21 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B (27414891770940381 / 40000000000000000) (685372294273511327 / 1000000000000000000) (kdot ((11 / 20))) := by
    constructor
    · apply bkdot_lower (q := (538815906080324703 / 1000000000000000000)) (a := (247108022231538449 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (269407953040162351 / 500000000000000000)) (a := (494216044463074069 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS24_hz22 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B (121 / 400) (121 / 400) (((11 / 20) : ℝ)^2) := bsq (bpoint ((11 / 20) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS24_hz23 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B (279 / 400) (279 / 400) ((1 : ℝ) - (((11 / 20) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS24_hz22 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS24_hz24 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B (104395581803062911 / 125000000000000000) (835164654424503289 / 1000000000000000000) (√((1 : ℝ) - (((11 / 20) : ℝ)^2))) := bsqrt (lowCoarseS24_hz23 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS24_hz25 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B (265841166094588509 / 1000000000000000000) (265841166094588511 / 1000000000000000000) ((√((1 : ℝ) - (((11 / 20) : ℝ)^2))) / Real.pi) := bdiv (lowCoarseS24_hz24 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS24_hz26 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B (188477380925215119 / 500000000000000000) (37695476185043123 / 100000000000000000) (((11 / 20) : ℝ) * (kdot ((11 / 20)))) := bmul (bpoint ((11 / 20) : ℝ)) (lowCoarseS24_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS24_hz27 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B (642795927945018747 / 1000000000000000000) (642795927945019741 / 1000000000000000000) (((√((1 : ℝ) - (((11 / 20) : ℝ)^2))) / Real.pi) + (((11 / 20) : ℝ) * (kdot ((11 / 20))))) := badd (lowCoarseS24_hz25 hx hc) (lowCoarseS24_hz26 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS24_hz28 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B (642795927945018747 / 1000000000000000000) (642795927945019741 / 1000000000000000000) (kappa ((11 / 20))) := by rw [kappa_eq]; exact (lowCoarseS24_hz27 hx hc)

theorem lowCoarseS24_hz29 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B (31798060607288863 / 50000000000000000) (642795927945019741 / 1000000000000000000) (kappa c) := bkappa (lowCoarseS24_hz1 hx hc) (by norm_num) (by norm_num) (lowCoarseS24_hz20 hx hc).1 (lowCoarseS24_hz28 hx hc).2

theorem lowCoarseS24_hz30 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B (357204072054980259 / 1000000000000000000) (18201939392711137 / 50000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (lowCoarseS24_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS24_hz31 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B (357204072054980259 / 500000000000000000) (18201939392711137 / 25000000000000000) ((2 : ℝ) * ((1 : ℝ) - (kappa c))) := bmul (bpoint (2 : ℝ)) (lowCoarseS24_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS24_hz32 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B 0 (1 / 8000000) ((8 : ℝ) * (x^2)) := bmul (bpoint (8 : ℝ)) (lowCoarseS24_hz7 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS24_hz33 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B (357204009554980259 / 500000000000000000) (18201939392711137 / 25000000000000000) (((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2))) := bsub (lowCoarseS24_hz31 hx hc) (lowCoarseS24_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS24_hz34 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B (105653326017656127 / 125000000000000000) (426637309581700051 / 500000000000000000) (√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) := bsqrt (lowCoarseS24_hz33 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS24_hz35 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B (6782329983125268139 / 250000000000000000) (13564659966250536279 / 500000000000000000) ((2 : ℝ) * (√(184 : ℝ))) := bmul (bpoint (2 : ℝ)) (lowCoarseS24_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS24_hz36 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B 0 (678232998312527 / 200000000000000000) (((2 : ℝ) * (√(184 : ℝ))) * x) := bmul (lowCoarseS24_hz35 hx hc) (lowCoarseS24_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS24_hz37 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B (841835443149686381 / 1000000000000000000) (426637309581700051 / 500000000000000000) ((√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) - (((2 : ℝ) * (√(184 : ℝ))) * x)) := bsub (lowCoarseS24_hz34 hx hc) (lowCoarseS24_hz36 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS24_hz38 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B (841835443149686381 / 1000000000000000000) (426637309581700051 / 500000000000000000) (ndm x c) := by
    convert (lowCoarseS24_hz37 hx hc) using 1 <;>
      norm_num [ndm] <;> ring

theorem lowCoarseS24_hz39 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B 1 (1003394039991562637 / 1000000000000000000) ((nap x)^2) := bsq (lowCoarseS24_hz6 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS24_hz40 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B 2 (1003394039991562637 / 500000000000000000) ((2 : ℝ) * ((nap x)^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS24_hz39 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS24_hz41 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B (14173738266860577 / 20000000000000000) (728077575708445481 / 1000000000000000000) ((ndm x c)^2) := bsq (lowCoarseS24_hz38 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS24_hz42 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B (1271922424291554519 / 1000000000000000000) (162262645830012053 / 125000000000000000) (((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) := bsub (lowCoarseS24_hz40 hx hc) (lowCoarseS24_hz41 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS24_hz43 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B (199322335762284863 / 200000000000000000) 1 ((nam x)^2) := bsq (lowCoarseS24_hz12 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS24_hz44 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B (199322335762284863 / 100000000000000000) 2 ((2 : ℝ) * ((nam x)^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS24_hz43 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS24_hz45 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B (635961212145777259 / 1000000000000000000) (325628626033219251 / 500000000000000000) ((((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) / ((2 : ℝ) * ((nam x)^2))) := bdiv (lowCoarseS24_hz42 hx hc) (lowCoarseS24_hz44 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS24_hz46 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B (635961212145777259 / 1000000000000000000) (325628626033219251 / 500000000000000000) (nc1 x c) := by
    convert (lowCoarseS24_hz45 hx hc) using 1 <;>
      norm_num [nc1] <;> ring

theorem lowCoarseS24_hz47 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B (340787885684049643 / 500000000000000000) (685372294273511327 / 1000000000000000000) (kdot c) := bkdot (lowCoarseS24_hz1 hx hc) (lowCoarseS24_hz13 hx hc).1 (lowCoarseS24_hz21 hx hc).2

theorem lowCoarseS24_hz48 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B (359698089685115431 / 500000000000000000) (719396179370230867 / 1000000000000000000) (kdot ((635961212145777259 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (235861650270449373 / 500000000000000000)) (a := (88154290145971079 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (94344660108179749 / 200000000000000000)) (a := (440771450729855389 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS24_hz49 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B (145151622771015311 / 200000000000000000) (362879056927538279 / 500000000000000000) (kdot ((325628626033219251 / 500000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (229781588792427043 / 500000000000000000)) (a := (215389073704874999 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (91912635516970817 / 200000000000000000)) (a := (86155629481949999 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS24_hz50 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B (359698089685115431 / 500000000000000000) (362879056927538279 / 500000000000000000) (kdot (nc1 x c)) := bkdot (lowCoarseS24_hz46 hx hc) (lowCoarseS24_hz48 hx hc).1 (lowCoarseS24_hz49 hx hc).2

theorem lowCoarseS24_hz51 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B (729 / 2500) (121 / 400) (c^2) := bsq (lowCoarseS24_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS24_hz52 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B (279 / 400) (1771 / 2500) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS24_hz51 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS24_hz53 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B (104395581803062911 / 125000000000000000) (821938492675813 / 976562500000000) (√((1 : ℝ) - (c^2))) := bsqrt (lowCoarseS24_hz52 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS24_hz54 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B (284613996779376451 / 500000000000000000) (11537077667367601 / 20000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (lowCoarseS24_hz53 hx hc) (lowCoarseS24_hz47 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS24_hz55 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B (284613996779376451 / 500000000000000000) (11537077667367601 / 20000000000000000) (npa c) := by
    convert (lowCoarseS24_hz54 hx hc) using 1 <;>
      norm_num [npa] <;> ring

theorem lowCoarseS24_hz56 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B (265841166094588509 / 1000000000000000000) (267910295607003647 / 1000000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (lowCoarseS24_hz53 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS24_hz57 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B (184025458269386807 / 500000000000000000) (37695476185043123 / 100000000000000000) (c * (kdot c)) := bmul (lowCoarseS24_hz1 hx hc) (lowCoarseS24_hz47 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS24_hz58 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B (-111113595755842721 / 1000000000000000000) (-100140620931769967 / 1000000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (lowCoarseS24_hz56 hx hc) (lowCoarseS24_hz57 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS24_hz59 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B (-111113595755842721 / 1000000000000000000) (-100140620931769967 / 1000000000000000000) (npp c) := by
    convert (lowCoarseS24_hz58 hx hc) using 1 <;>
      norm_num [npp] <;> ring

theorem lowCoarseS24_hz60 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B 0 (23 / 4000) ((46 : ℝ) * x) := bmul (bpoint (46 : ℝ)) (lowCoarseS24_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS24_hz61 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B (9591663046625439083 / 1000000000000000000) (2399353261656359771 / 250000000000000000) ((√(92 : ℝ)) + ((46 : ℝ) * x)) := badd (lowCoarseS24_hz3 hx hc) (lowCoarseS24_hz60 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS24_hz62 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B (28774989139876317249 / 250000000000000000) (7198059784969079313 / 62500000000000000) ((12 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (bpoint (12 : ℝ)) (lowCoarseS24_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS24_hz63 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B 0 (14396119569938159 / 1000000000000000000) (((12 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS24_hz62 hx hc) (lowCoarseS24_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS24_hz64 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B 0 (14396119569938159 / 1000000000000000000) (nr1 x) := by
    convert (lowCoarseS24_hz63 hx hc) using 1 <;>
      norm_num [nr1] <;> ring

theorem lowCoarseS24_hz65 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B (9591663046625439083 / 125000000000000000) (2399353261656359771 / 31250000000000000) ((8 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (bpoint (8 : ℝ)) (lowCoarseS24_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS24_hz66 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B 0 (59983831541409 / 6250000000000000) (((8 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS24_hz65 hx hc) (lowCoarseS24_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS24_hz67 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B 0 (59983831541409 / 6250000000000000) (nrpp x) := by
    convert (lowCoarseS24_hz66 hx hc) using 1 <;>
      norm_num [nrpp] <;> ring

theorem lowCoarseS24_hz68 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B 0 (847791247890659 / 500000000000000000) (ne0 x) := by
    convert (lowCoarseS24_hz4 hx hc) using 1 <;>
      norm_num [ne0] <;> ring

theorem lowCoarseS24_hz69 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B (284613996779376451 / 500000000000000000) (591250002938318209 / 1000000000000000000) ((npa c) + (nr1 x)) := badd (lowCoarseS24_hz55 hx hc) (lowCoarseS24_hz64 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS24_hz70 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B (284613996779376451 / 500000000000000000) (592254228094500107 / 1000000000000000000) (((npa c) + (nr1 x)) / (nam x)) := bdiv (lowCoarseS24_hz69 hx hc) (lowCoarseS24_hz12 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS24_hz71 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B (284613996779376451 / 500000000000000000) (23757992423611257 / 40000000000000000) ((((npa c) + (nr1 x)) / (nam x)) + (ne0 x)) := badd (lowCoarseS24_hz70 hx hc) (lowCoarseS24_hz68 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS24_hz72 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B (284613996779376451 / 500000000000000000) (23757992423611257 / 40000000000000000) (nlam x c) := by
    convert (lowCoarseS24_hz71 hx hc) using 1 <;>
      norm_num [nlam] <;> ring

theorem lowCoarseS24_hz73 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS24_hz74 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B 0 (59947894041409 / 100000000000000000) ((√(23 : ℝ)) * x) := bmul (lowCoarseS24_hz73 hx hc) (lowCoarseS24_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS24_hz75 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B (1 / 2) (50059947894041409 / 100000000000000000) (((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)) := badd (bpoint ((1 / 2) : ℝ)) (lowCoarseS24_hz74 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS24_hz76 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B (176776695296636881 / 250000000000000000) (353765274914177413 / 500000000000000000) (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) := bsqrt (lowCoarseS24_hz75 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS24_hz77 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B 0 (59947894041409 / 50000000000000000) ((√(92 : ℝ)) * x) := bmul (lowCoarseS24_hz3 hx hc) (lowCoarseS24_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS24_hz78 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B (176776695296636881 / 250000000000000000) (354364753854591503 / 500000000000000000) ((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x)) := badd (lowCoarseS24_hz76 hx hc) (lowCoarseS24_hz77 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS24_hz79 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B (499999999999999999 / 1000000000000000000) (251148757548850447 / 500000000000000000) (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2) := bsq (lowCoarseS24_hz78 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS24_hz80 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B (499999999999999999 / 125000000000000000) (251148757548850447 / 62500000000000000) ((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) := bmul (bpoint (8 : ℝ)) (lowCoarseS24_hz79 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS24_hz81 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B (7673330437300351251 / 200000000000000000) (1928302689874485209 / 50000000000000000) (((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (lowCoarseS24_hz80 hx hc) (lowCoarseS24_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS24_hz82 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B 0 (2410378362343107 / 500000000000000000) ((((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS24_hz81 hx hc) (lowCoarseS24_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS24_hz83 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B 0 (2410378362343107 / 500000000000000000) (nrs x) := by
    convert (lowCoarseS24_hz82 hx hc) using 1 <;>
      norm_num [nrs] <;> ring

theorem lowCoarseS24_hz84 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B (-111113595755842721 / 1000000000000000000) (-90543207885144527 / 1000000000000000000) ((npp c) + (nrpp x)) := badd (lowCoarseS24_hz59 hx hc) (lowCoarseS24_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS24_hz85 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B (-80641593679415853 / 1000000000000000000) (-45271603942572263 / 1000000000000000000) (if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) := bweaken (bfirst (lowCoarseS24_hz84 hx hc) (lowCoarseS24_hz50 hx hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem lowCoarseS24_hz86 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B (64804101730184727 / 200000000000000000) (352776377500231181 / 1000000000000000000) ((nlam x c)^2) := bsq (lowCoarseS24_hz72 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS24_hz87 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B (101111665838481577 / 250000000000000000) (424136008369128617 / 1000000000000000000) ((nc1 x c)^2) := bsq (lowCoarseS24_hz46 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS24_hz88 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B (575863991630871383 / 1000000000000000000) (148888334161518423 / 250000000000000000) ((1 : ℝ) - ((nc1 x c)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS24_hz87 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS24_hz89 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B (379428514884843421 / 500000000000000000) (385860511275147749 / 500000000000000000) (√((1 : ℝ) - ((nc1 x c)^2))) := bsqrt (lowCoarseS24_hz88 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS24_hz90 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B (238401966984941921 / 100000000000000000) (2424433095064811501 / 1000000000000000000) (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))) := bmul pi_mem (lowCoarseS24_hz89 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS24_hz91 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B (133647948178277821 / 1000000000000000000) (73987723751145359 / 500000000000000000) (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2))))) := bdiv (lowCoarseS24_hz86 hx hc) (lowCoarseS24_hz90 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS24_hz92 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B (3312897156178873 / 62500000000000000) (20540768711943691 / 200000000000000000) ((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) := badd (lowCoarseS24_hz85 hx hc) (lowCoarseS24_hz91 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS24_hz93 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B 0 (2875000000001 / 1000000000000000000) ((ne0 x)^2) := bsq (lowCoarseS24_hz68 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS24_hz94 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B (3312897156178873 / 62500000000000000) (12838339819964807 / 125000000000000000) (((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) + ((ne0 x)^2)) := badd (lowCoarseS24_hz92 hx hc) (lowCoarseS24_hz93 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS24_hz95 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B (3312897156178873 / 62500000000000000) (10752747528440467 / 100000000000000000) ((((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) + ((ne0 x)^2)) + (nrs x)) := badd (lowCoarseS24_hz94 hx hc) (lowCoarseS24_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS24_hz96 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B (3312897156178873 / 62500000000000000) (10752747528440467 / 100000000000000000) (nu x c) := by
    convert (lowCoarseS24_hz95 hx hc) using 1 <;>
      norm_num [nu] <;> ring

theorem lowCoarseS24_hz97 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B (-120711008802468161 / 1000000000000000000) (-100140620931769967 / 1000000000000000000) ((npp c) - (nrpp x)) := bsub (lowCoarseS24_hz59 hx hc) (lowCoarseS24_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS24_hz98 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B (-120711008802468161 / 1000000000000000000) (-100140620931769967 / 1000000000000000000) (min ((npp c) - (nrpp x)) (0 : ℝ)) := bweaken (bmin (lowCoarseS24_hz97 hx hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem lowCoarseS24_hz99 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B (-87606994070022837 / 1000000000000000000) (-36020390049038941 / 500000000000000000) ((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) := bmul (lowCoarseS24_hz50 hx hc) (lowCoarseS24_hz98 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS24_hz100 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B (-43804934535011419 / 500000000000000000) (-36020390049038941 / 500000000000000000) (((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) - ((ne0 x)^2)) := bsub (lowCoarseS24_hz99 hx hc) (lowCoarseS24_hz93 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS24_hz101 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B (-23107656448677263 / 250000000000000000) (-36020390049038941 / 500000000000000000) ((((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) - ((ne0 x)^2)) - (nrs x)) := bsub (lowCoarseS24_hz100 hx hc) (lowCoarseS24_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS24_hz102 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B (-23107656448677263 / 250000000000000000) (-36020390049038941 / 500000000000000000) (nl x c) := by
    convert (lowCoarseS24_hz101 hx hc) using 1 <;>
      norm_num [nl] <;> ring

theorem lowCoarseS24_hz103 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B 0 (10752747528440467 / 100000000000000000) |(nu x c)| := bweaken (babs (lowCoarseS24_hz96 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS24_hz104 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B 0 (23107656448677263 / 250000000000000000) |(nl x c)| := bweaken (babs (lowCoarseS24_hz102 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS24_hz105 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B 0 (10752747528440467 / 100000000000000000) (max |(nu x c)| |(nl x c)|) := bweaken (bmax (lowCoarseS24_hz103 hx hc) (lowCoarseS24_hz104 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS24_hz106 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) : B 0 (10752747528440467 / 100000000000000000) (ns x c) := by
    convert (lowCoarseS24_hz105 hx hc) using 1 <;>
      norm_num [ns] <;> ring

theorem lowCoarseS24 {x c : ℝ}
    (hx : B 0 (1/8000) x) (hc : B (27 / 50) (11 / 20) c) :
    0 < nam x ∧ 0 ≤ ndm x c ∧ ndm x c ^ 2 ≤ 2 * nap x ^ 2 ∧ nc1 x c < 1 ∧
    0 ≤ npa c - nr1 x ∧ ne0 x ≤ (npa c - nr1 x) / nap x ∧ ns x c ≤ (1 / 5) := by
  refine ⟨lt_of_lt_of_le (by norm_num) (lowCoarseS24_hz12 hx hc).1,
    le_trans (by norm_num) (lowCoarseS24_hz38 hx hc).1, ?_,
    lt_of_le_of_lt (lowCoarseS24_hz46 hx hc).2 (by norm_num), ?_, ?_, (lowCoarseS24_hz106 hx hc).2.trans (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (lowCoarseS24_hz38 hx hc).1) (lowCoarseS24_hz38 hx hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) (lowCoarseS24_hz6 hx hc).1 2
    nlinarith only [h1,h2]
  · linarith only [(lowCoarseS24_hz55 hx hc).1,(lowCoarseS24_hz64 hx hc).2]
  · have hap : 0 < nap x := lt_of_lt_of_le (by norm_num) (lowCoarseS24_hz6 hx hc).1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul (lowCoarseS24_hz68 hx hc).2 (lowCoarseS24_hz6 hx hc).2 (le_trans (by norm_num) (lowCoarseS24_hz6 hx hc).1) (by norm_num)
    linarith only [h,(lowCoarseS24_hz55 hx hc).1,(lowCoarseS24_hz64 hx hc).2]

theorem lowCoarseS25_hz0 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B 0 (1 / 8000) x := hx

theorem lowCoarseS25_hz1 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B (11 / 20) (14 / 25) c := hc

theorem lowCoarseS25_hz2 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B (6782329983125268139 / 500000000000000000) (13564659966250536279 / 1000000000000000000) (√(184 : ℝ)) := bsqrt (bpoint (184 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS25_hz3 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS25_hz4 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B 0 (847791247890659 / 500000000000000000) ((√(184 : ℝ)) * x) := bmul (lowCoarseS25_hz2 hx hc) (lowCoarseS25_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS25_hz5 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B 1 (500847791247890659 / 500000000000000000) ((1 : ℝ) + ((√(184 : ℝ)) * x)) := badd (bpoint (1 : ℝ)) (lowCoarseS25_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS25_hz6 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B 1 (500847791247890659 / 500000000000000000) (nap x) := by
    convert (lowCoarseS25_hz5 hx hc) using 1 <;>
      norm_num [nap] <;> ring

theorem lowCoarseS25_hz7 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B 0 (1 / 64000000) (x^2) := bsq (lowCoarseS25_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS25_hz8 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B 0 (1 / 32000000) ((2 : ℝ) * (x^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS25_hz7 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS25_hz9 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B (31999999 / 32000000) 1 ((1 : ℝ) - ((2 : ℝ) * (x^2))) := bsub (bpoint (1 : ℝ)) (lowCoarseS25_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS25_hz10 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B (999999984374999877 / 1000000000000000000) 1 (√((1 : ℝ) - ((2 : ℝ) * (x^2)))) := bsqrt (lowCoarseS25_hz9 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS25_hz11 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B (998304401879218559 / 1000000000000000000) 1 ((√((1 : ℝ) - ((2 : ℝ) * (x^2)))) - ((√(184 : ℝ)) * x)) := bsub (lowCoarseS25_hz10 hx hc) (lowCoarseS25_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS25_hz12 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B (998304401879218559 / 1000000000000000000) 1 (nam x) := by
    convert (lowCoarseS25_hz11 hx hc) using 1 <;>
      norm_num [nam] <;> ring

theorem lowCoarseS25_hz13 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B (27414891770940381 / 40000000000000000) (685372294273511327 / 1000000000000000000) (kdot ((11 / 20))) := by
    constructor
    · apply bkdot_lower (q := (538815906080324703 / 1000000000000000000)) (a := (247108022231538449 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (269407953040162351 / 500000000000000000)) (a := (494216044463074069 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS25_hz14 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B (121 / 400) (121 / 400) (((11 / 20) : ℝ)^2) := bsq (bpoint ((11 / 20) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS25_hz15 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B (279 / 400) (279 / 400) ((1 : ℝ) - (((11 / 20) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS25_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS25_hz16 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B (104395581803062911 / 125000000000000000) (835164654424503289 / 1000000000000000000) (√((1 : ℝ) - (((11 / 20) : ℝ)^2))) := bsqrt (lowCoarseS25_hz15 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS25_hz17 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B (265841166094588509 / 1000000000000000000) (265841166094588511 / 1000000000000000000) ((√((1 : ℝ) - (((11 / 20) : ℝ)^2))) / Real.pi) := bdiv (lowCoarseS25_hz16 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS25_hz18 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B (188477380925215119 / 500000000000000000) (37695476185043123 / 100000000000000000) (((11 / 20) : ℝ) * (kdot ((11 / 20)))) := bmul (bpoint ((11 / 20) : ℝ)) (lowCoarseS25_hz13 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS25_hz19 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B (642795927945018747 / 1000000000000000000) (642795927945019741 / 1000000000000000000) (((√((1 : ℝ) - (((11 / 20) : ℝ)^2))) / Real.pi) + (((11 / 20) : ℝ) * (kdot ((11 / 20))))) := badd (lowCoarseS25_hz17 hx hc) (lowCoarseS25_hz18 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS25_hz20 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B (642795927945018747 / 1000000000000000000) (642795927945019741 / 1000000000000000000) (kappa ((11 / 20))) := by rw [kappa_eq]; exact (lowCoarseS25_hz19 hx hc)

theorem lowCoarseS25_hz21 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B (34459943817379969 / 50000000000000000) (689198876347600269 / 1000000000000000000) (kdot ((14 / 25))) := by
    constructor
    · apply bkdot_lower (q := (531085004543794337 / 1000000000000000000)) (a := (488205263396917357 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (16596406391993573 / 31250000000000000)) (a := (244102631698457981 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS25_hz22 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B (196 / 625) (196 / 625) (((14 / 25) : ℝ)^2) := bsq (bpoint ((14 / 25) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS25_hz23 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B (429 / 625) (429 / 625) ((1 : ℝ) - (((14 / 25) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS25_hz22 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS25_hz24 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B (165698521417663833 / 200000000000000000) (414246303544159583 / 500000000000000000) (√((1 : ℝ) - (((14 / 25) : ℝ)^2))) := bsqrt (lowCoarseS25_hz23 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS25_hz25 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B (263717387466394877 / 1000000000000000000) (263717387466394879 / 1000000000000000000) ((√((1 : ℝ) - (((14 / 25) : ℝ)^2))) / Real.pi) := bdiv (lowCoarseS25_hz24 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS25_hz26 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B (96487842688663913 / 250000000000000000) (385951370754656151 / 1000000000000000000) (((14 / 25) : ℝ) * (kdot ((14 / 25)))) := bmul (bpoint ((14 / 25) : ℝ)) (lowCoarseS25_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS25_hz27 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B (649668758221050529 / 1000000000000000000) (64966875822105103 / 100000000000000000) (((√((1 : ℝ) - (((14 / 25) : ℝ)^2))) / Real.pi) + (((14 / 25) : ℝ) * (kdot ((14 / 25))))) := badd (lowCoarseS25_hz25 hx hc) (lowCoarseS25_hz26 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS25_hz28 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B (649668758221050529 / 1000000000000000000) (64966875822105103 / 100000000000000000) (kappa ((14 / 25))) := by rw [kappa_eq]; exact (lowCoarseS25_hz27 hx hc)

theorem lowCoarseS25_hz29 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B (642795927945018747 / 1000000000000000000) (64966875822105103 / 100000000000000000) (kappa c) := bkappa (lowCoarseS25_hz1 hx hc) (by norm_num) (by norm_num) (lowCoarseS25_hz20 hx hc).1 (lowCoarseS25_hz28 hx hc).2

theorem lowCoarseS25_hz30 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B (35033124177894897 / 100000000000000000) (357204072054981253 / 1000000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (lowCoarseS25_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS25_hz31 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B (35033124177894897 / 50000000000000000) (357204072054981253 / 500000000000000000) ((2 : ℝ) * ((1 : ℝ) - (kappa c))) := bmul (bpoint (2 : ℝ)) (lowCoarseS25_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS25_hz32 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B 0 (1 / 8000000) ((8 : ℝ) * (x^2)) := bmul (bpoint (8 : ℝ)) (lowCoarseS25_hz7 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS25_hz33 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B (35033117927894897 / 50000000000000000) (357204072054981253 / 500000000000000000) (((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2))) := bsub (lowCoarseS25_hz31 hx hc) (lowCoarseS25_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS25_hz34 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B (837055767889988283 / 1000000000000000000) (169045336417182773 / 200000000000000000) (√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) := bsqrt (lowCoarseS25_hz33 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS25_hz35 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B (6782329983125268139 / 250000000000000000) (13564659966250536279 / 500000000000000000) ((2 : ℝ) * (√(184 : ℝ))) := bmul (bpoint (2 : ℝ)) (lowCoarseS25_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS25_hz36 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B 0 (678232998312527 / 200000000000000000) (((2 : ℝ) * (√(184 : ℝ))) * x) := bmul (lowCoarseS25_hz35 hx hc) (lowCoarseS25_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS25_hz37 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B (52104037681151603 / 62500000000000000) (169045336417182773 / 200000000000000000) ((√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) - (((2 : ℝ) * (√(184 : ℝ))) * x)) := bsub (lowCoarseS25_hz34 hx hc) (lowCoarseS25_hz36 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS25_hz38 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B (52104037681151603 / 62500000000000000) (169045336417182773 / 200000000000000000) (ndm x c) := by
    convert (lowCoarseS25_hz37 hx hc) using 1 <;>
      norm_num [ndm] <;> ring

theorem lowCoarseS25_hz39 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B 1 (1003394039991562637 / 1000000000000000000) ((nap x)^2) := bsq (lowCoarseS25_hz6 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS25_hz40 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B 2 (1003394039991562637 / 500000000000000000) ((2 : ℝ) * ((nap x)^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS25_hz39 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS25_hz41 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B (27799866805031589 / 40000000000000000) (714408144109962507 / 1000000000000000000) ((ndm x c)^2) := bsq (lowCoarseS25_hz38 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS25_hz42 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B (1285591855890037493 / 1000000000000000000) (1311791409857335549 / 1000000000000000000) (((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) := bsub (lowCoarseS25_hz40 hx hc) (lowCoarseS25_hz41 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS25_hz43 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B (199322335762284863 / 200000000000000000) 1 ((nam x)^2) := bsq (lowCoarseS25_hz12 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS25_hz44 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B (199322335762284863 / 100000000000000000) 2 ((2 : ℝ) * ((nam x)^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS25_hz43 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS25_hz45 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B (321397963972509373 / 500000000000000000) (658125645999753801 / 1000000000000000000) ((((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) / ((2 : ℝ) * ((nam x)^2))) := bdiv (lowCoarseS25_hz42 hx hc) (lowCoarseS25_hz44 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS25_hz46 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B (321397963972509373 / 500000000000000000) (658125645999753801 / 1000000000000000000) (nc1 x c) := by
    convert (lowCoarseS25_hz45 hx hc) using 1 <;>
      norm_num [nc1] <;> ring

theorem lowCoarseS25_hz47 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B (27414891770940381 / 40000000000000000) (689198876347600269 / 1000000000000000000) (kdot c) := bkdot (lowCoarseS25_hz1 hx hc) (lowCoarseS25_hz13 hx hc).1 (lowCoarseS25_hz21 hx hc).2

theorem lowCoarseS25_hz48 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B (18055641966859641 / 25000000000000000) (722225678674385643 / 1000000000000000000) (kdot ((321397963972509373 / 500000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (116575262052273549 / 250000000000000000)) (a := (87265376723244071 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (93260209641818839 / 200000000000000000)) (a := (436326883616220351 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS25_hz49 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B (728650444918483399 / 1000000000000000000) (728650444918483401 / 1000000000000000000) (kdot ((658125645999753801 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (227035906406727971 / 500000000000000000)) (a := (426234884399475751 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (454071812813455941 / 1000000000000000000)) (a := (426234884399475749 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS25_hz50 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B (18055641966859641 / 25000000000000000) (728650444918483401 / 1000000000000000000) (kdot (nc1 x c)) := bkdot (lowCoarseS25_hz46 hx hc) (lowCoarseS25_hz48 hx hc).1 (lowCoarseS25_hz49 hx hc).2

theorem lowCoarseS25_hz51 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B (121 / 400) (196 / 625) (c^2) := bsq (lowCoarseS25_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS25_hz52 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B (429 / 625) (279 / 400) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS25_hz51 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS25_hz53 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B (165698521417663833 / 200000000000000000) (835164654424503289 / 1000000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (lowCoarseS25_hz52 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS25_hz54 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B (283912939454381293 / 500000000000000000) (575594541394599553 / 1000000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (lowCoarseS25_hz53 hx hc) (lowCoarseS25_hz47 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS25_hz55 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B (283912939454381293 / 500000000000000000) (575594541394599553 / 1000000000000000000) (npa c) := by
    convert (lowCoarseS25_hz54 hx hc) using 1 <;>
      norm_num [npa] <;> ring

theorem lowCoarseS25_hz56 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B (263717387466394877 / 1000000000000000000) (265841166094588511 / 1000000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (lowCoarseS25_hz53 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS25_hz57 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B (188477380925215119 / 500000000000000000) (385951370754656151 / 1000000000000000000) (c * (kdot c)) := bmul (lowCoarseS25_hz1 hx hc) (lowCoarseS25_hz47 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS25_hz58 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B (-61116991644130637 / 500000000000000000) (-111113595755841727 / 1000000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (lowCoarseS25_hz56 hx hc) (lowCoarseS25_hz57 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS25_hz59 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B (-61116991644130637 / 500000000000000000) (-111113595755841727 / 1000000000000000000) (npp c) := by
    convert (lowCoarseS25_hz58 hx hc) using 1 <;>
      norm_num [npp] <;> ring

theorem lowCoarseS25_hz60 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B 0 (23 / 4000) ((46 : ℝ) * x) := bmul (bpoint (46 : ℝ)) (lowCoarseS25_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS25_hz61 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B (9591663046625439083 / 1000000000000000000) (2399353261656359771 / 250000000000000000) ((√(92 : ℝ)) + ((46 : ℝ) * x)) := badd (lowCoarseS25_hz3 hx hc) (lowCoarseS25_hz60 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS25_hz62 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B (28774989139876317249 / 250000000000000000) (7198059784969079313 / 62500000000000000) ((12 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (bpoint (12 : ℝ)) (lowCoarseS25_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS25_hz63 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B 0 (14396119569938159 / 1000000000000000000) (((12 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS25_hz62 hx hc) (lowCoarseS25_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS25_hz64 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B 0 (14396119569938159 / 1000000000000000000) (nr1 x) := by
    convert (lowCoarseS25_hz63 hx hc) using 1 <;>
      norm_num [nr1] <;> ring

theorem lowCoarseS25_hz65 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B (9591663046625439083 / 125000000000000000) (2399353261656359771 / 31250000000000000) ((8 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (bpoint (8 : ℝ)) (lowCoarseS25_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS25_hz66 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B 0 (59983831541409 / 6250000000000000) (((8 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS25_hz65 hx hc) (lowCoarseS25_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS25_hz67 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B 0 (59983831541409 / 6250000000000000) (nrpp x) := by
    convert (lowCoarseS25_hz66 hx hc) using 1 <;>
      norm_num [nrpp] <;> ring

theorem lowCoarseS25_hz68 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B 0 (847791247890659 / 500000000000000000) (ne0 x) := by
    convert (lowCoarseS25_hz4 hx hc) using 1 <;>
      norm_num [ne0] <;> ring

theorem lowCoarseS25_hz69 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B (283912939454381293 / 500000000000000000) (36874416310283607 / 62500000000000000) ((npa c) + (nr1 x)) := badd (lowCoarseS25_hz55 hx hc) (lowCoarseS25_hz64 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS25_hz70 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B (283912939454381293 / 500000000000000000) (295496373578005453 / 500000000000000000) (((npa c) + (nr1 x)) / (nam x)) := bdiv (lowCoarseS25_hz69 hx hc) (lowCoarseS25_hz12 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS25_hz71 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B (283912939454381293 / 500000000000000000) (18521510301618507 / 31250000000000000) ((((npa c) + (nr1 x)) / (nam x)) + (ne0 x)) := badd (lowCoarseS25_hz70 hx hc) (lowCoarseS25_hz68 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS25_hz72 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B (283912939454381293 / 500000000000000000) (18521510301618507 / 31250000000000000) (nlam x c) := by
    convert (lowCoarseS25_hz71 hx hc) using 1 <;>
      norm_num [nlam] <;> ring

theorem lowCoarseS25_hz73 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS25_hz74 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B 0 (59947894041409 / 100000000000000000) ((√(23 : ℝ)) * x) := bmul (lowCoarseS25_hz73 hx hc) (lowCoarseS25_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS25_hz75 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B (1 / 2) (50059947894041409 / 100000000000000000) (((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)) := badd (bpoint ((1 / 2) : ℝ)) (lowCoarseS25_hz74 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS25_hz76 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B (176776695296636881 / 250000000000000000) (353765274914177413 / 500000000000000000) (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) := bsqrt (lowCoarseS25_hz75 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS25_hz77 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B 0 (59947894041409 / 50000000000000000) ((√(92 : ℝ)) * x) := bmul (lowCoarseS25_hz3 hx hc) (lowCoarseS25_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS25_hz78 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B (176776695296636881 / 250000000000000000) (354364753854591503 / 500000000000000000) ((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x)) := badd (lowCoarseS25_hz76 hx hc) (lowCoarseS25_hz77 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS25_hz79 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B (499999999999999999 / 1000000000000000000) (251148757548850447 / 500000000000000000) (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2) := bsq (lowCoarseS25_hz78 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS25_hz80 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B (499999999999999999 / 125000000000000000) (251148757548850447 / 62500000000000000) ((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) := bmul (bpoint (8 : ℝ)) (lowCoarseS25_hz79 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS25_hz81 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B (7673330437300351251 / 200000000000000000) (1928302689874485209 / 50000000000000000) (((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (lowCoarseS25_hz80 hx hc) (lowCoarseS25_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS25_hz82 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B 0 (2410378362343107 / 500000000000000000) ((((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS25_hz81 hx hc) (lowCoarseS25_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS25_hz83 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B 0 (2410378362343107 / 500000000000000000) (nrs x) := by
    convert (lowCoarseS25_hz82 hx hc) using 1 <;>
      norm_num [nrs] <;> ring

theorem lowCoarseS25_hz84 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B (-61116991644130637 / 500000000000000000) (-101516182709216287 / 1000000000000000000) ((npp c) + (nrpp x)) := badd (lowCoarseS25_hz59 hx hc) (lowCoarseS25_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS25_hz85 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B (-44532923153575021 / 500000000000000000) (-50758091354608143 / 1000000000000000000) (if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) := bweaken (bfirst (lowCoarseS25_hz84 hx hc) (lowCoarseS25_hz50 hx hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem lowCoarseS25_hz86 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B (322426228758508711 / 1000000000000000000) (35127945610543153 / 100000000000000000) ((nlam x c)^2) := bsq (lowCoarseS25_hz72 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS25_hz87 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B (413186604982697731 / 1000000000000000000) (433129365922593257 / 1000000000000000000) ((nc1 x c)^2) := bsq (lowCoarseS25_hz46 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS25_hz88 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B (566870634077406743 / 1000000000000000000) (586813395017302269 / 1000000000000000000) ((1 : ℝ) - ((nc1 x c)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS25_hz87 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS25_hz89 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B (376454058975795459 / 500000000000000000) (383018731597196911 / 500000000000000000) (√((1 : ℝ) - ((nc1 x c)^2))) := bsqrt (lowCoarseS25_hz88 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS25_hz90 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B (1182665306092417777 / 500000000000000000) (2406577666746069259 / 1000000000000000000) (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))) := bmul pi_mem (lowCoarseS25_hz89 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS25_hz91 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B (133977071762018311 / 1000000000000000000) (74255889281574409 / 500000000000000000) (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2))))) := bdiv (lowCoarseS25_hz86 hx hc) (lowCoarseS25_hz90 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS25_hz92 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B (44911225454868269 / 1000000000000000000) (3910147488341627 / 40000000000000000) ((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) := badd (lowCoarseS25_hz85 hx hc) (lowCoarseS25_hz91 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS25_hz93 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B 0 (2875000000001 / 1000000000000000000) ((ne0 x)^2) := bsq (lowCoarseS25_hz68 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS25_hz94 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B (44911225454868269 / 1000000000000000000) (24439140552135169 / 250000000000000000) (((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) + ((ne0 x)^2)) := badd (lowCoarseS25_hz92 hx hc) (lowCoarseS25_hz93 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS25_hz95 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B (44911225454868269 / 1000000000000000000) (10257731893322689 / 100000000000000000) ((((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) + ((ne0 x)^2)) + (nrs x)) := badd (lowCoarseS25_hz94 hx hc) (lowCoarseS25_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS25_hz96 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B (44911225454868269 / 1000000000000000000) (10257731893322689 / 100000000000000000) (nu x c) := by
    convert (lowCoarseS25_hz95 hx hc) using 1 <;>
      norm_num [nu] <;> ring

theorem lowCoarseS25_hz97 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B (-65915698167443357 / 500000000000000000) (-111113595755841727 / 1000000000000000000) ((npp c) - (nrpp x)) := bsub (lowCoarseS25_hz59 hx hc) (lowCoarseS25_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS25_hz98 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B (-65915698167443357 / 500000000000000000) (-111113595755841727 / 1000000000000000000) (min ((npp c) - (nrpp x)) (0 : ℝ)) := bweaken (bmin (lowCoarseS25_hz97 hx hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem lowCoarseS25_hz99 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B (-96059005593640127 / 1000000000000000000) (-80249092104714127 / 1000000000000000000) ((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) := bmul (lowCoarseS25_hz50 hx hc) (lowCoarseS25_hz98 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS25_hz100 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B (-1500966884275627 / 15625000000000000) (-80249092104714127 / 1000000000000000000) (((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) - ((ne0 x)^2)) := bsub (lowCoarseS25_hz99 hx hc) (lowCoarseS25_hz93 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS25_hz101 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B (-50441318659163171 / 500000000000000000) (-80249092104714127 / 1000000000000000000) ((((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) - ((ne0 x)^2)) - (nrs x)) := bsub (lowCoarseS25_hz100 hx hc) (lowCoarseS25_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS25_hz102 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B (-50441318659163171 / 500000000000000000) (-80249092104714127 / 1000000000000000000) (nl x c) := by
    convert (lowCoarseS25_hz101 hx hc) using 1 <;>
      norm_num [nl] <;> ring

theorem lowCoarseS25_hz103 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B 0 (10257731893322689 / 100000000000000000) |(nu x c)| := bweaken (babs (lowCoarseS25_hz96 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS25_hz104 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B 0 (50441318659163171 / 500000000000000000) |(nl x c)| := bweaken (babs (lowCoarseS25_hz102 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS25_hz105 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B 0 (10257731893322689 / 100000000000000000) (max |(nu x c)| |(nl x c)|) := bweaken (bmax (lowCoarseS25_hz103 hx hc) (lowCoarseS25_hz104 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS25_hz106 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) : B 0 (10257731893322689 / 100000000000000000) (ns x c) := by
    convert (lowCoarseS25_hz105 hx hc) using 1 <;>
      norm_num [ns] <;> ring

theorem lowCoarseS25 {x c : ℝ}
    (hx : B 0 (1/8000) x) (hc : B (11 / 20) (14 / 25) c) :
    0 < nam x ∧ 0 ≤ ndm x c ∧ ndm x c ^ 2 ≤ 2 * nap x ^ 2 ∧ nc1 x c < 1 ∧
    0 ≤ npa c - nr1 x ∧ ne0 x ≤ (npa c - nr1 x) / nap x ∧ ns x c ≤ (1 / 5) := by
  refine ⟨lt_of_lt_of_le (by norm_num) (lowCoarseS25_hz12 hx hc).1,
    le_trans (by norm_num) (lowCoarseS25_hz38 hx hc).1, ?_,
    lt_of_le_of_lt (lowCoarseS25_hz46 hx hc).2 (by norm_num), ?_, ?_, (lowCoarseS25_hz106 hx hc).2.trans (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (lowCoarseS25_hz38 hx hc).1) (lowCoarseS25_hz38 hx hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) (lowCoarseS25_hz6 hx hc).1 2
    nlinarith only [h1,h2]
  · linarith only [(lowCoarseS25_hz55 hx hc).1,(lowCoarseS25_hz64 hx hc).2]
  · have hap : 0 < nap x := lt_of_lt_of_le (by norm_num) (lowCoarseS25_hz6 hx hc).1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul (lowCoarseS25_hz68 hx hc).2 (lowCoarseS25_hz6 hx hc).2 (le_trans (by norm_num) (lowCoarseS25_hz6 hx hc).1) (by norm_num)
    linarith only [h,(lowCoarseS25_hz55 hx hc).1,(lowCoarseS25_hz64 hx hc).2]

theorem lowCoarseS26_hz0 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B 0 (1 / 8000) x := hx

theorem lowCoarseS26_hz1 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B (14 / 25) (57 / 100) c := hc

theorem lowCoarseS26_hz2 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B (6782329983125268139 / 500000000000000000) (13564659966250536279 / 1000000000000000000) (√(184 : ℝ)) := bsqrt (bpoint (184 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS26_hz3 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS26_hz4 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B 0 (847791247890659 / 500000000000000000) ((√(184 : ℝ)) * x) := bmul (lowCoarseS26_hz2 hx hc) (lowCoarseS26_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS26_hz5 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B 1 (500847791247890659 / 500000000000000000) ((1 : ℝ) + ((√(184 : ℝ)) * x)) := badd (bpoint (1 : ℝ)) (lowCoarseS26_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS26_hz6 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B 1 (500847791247890659 / 500000000000000000) (nap x) := by
    convert (lowCoarseS26_hz5 hx hc) using 1 <;>
      norm_num [nap] <;> ring

theorem lowCoarseS26_hz7 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B 0 (1 / 64000000) (x^2) := bsq (lowCoarseS26_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS26_hz8 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B 0 (1 / 32000000) ((2 : ℝ) * (x^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS26_hz7 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS26_hz9 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B (31999999 / 32000000) 1 ((1 : ℝ) - ((2 : ℝ) * (x^2))) := bsub (bpoint (1 : ℝ)) (lowCoarseS26_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS26_hz10 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B (999999984374999877 / 1000000000000000000) 1 (√((1 : ℝ) - ((2 : ℝ) * (x^2)))) := bsqrt (lowCoarseS26_hz9 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS26_hz11 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B (998304401879218559 / 1000000000000000000) 1 ((√((1 : ℝ) - ((2 : ℝ) * (x^2)))) - ((√(184 : ℝ)) * x)) := bsub (lowCoarseS26_hz10 hx hc) (lowCoarseS26_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS26_hz12 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B (998304401879218559 / 1000000000000000000) 1 (nam x) := by
    convert (lowCoarseS26_hz11 hx hc) using 1 <;>
      norm_num [nam] <;> ring

theorem lowCoarseS26_hz13 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B (34459943817379969 / 50000000000000000) (689198876347600269 / 1000000000000000000) (kdot ((14 / 25))) := by
    constructor
    · apply bkdot_lower (q := (531085004543794337 / 1000000000000000000)) (a := (488205263396917357 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (16596406391993573 / 31250000000000000)) (a := (244102631698457981 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS26_hz14 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B (196 / 625) (196 / 625) (((14 / 25) : ℝ)^2) := bsq (bpoint ((14 / 25) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS26_hz15 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B (429 / 625) (429 / 625) ((1 : ℝ) - (((14 / 25) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS26_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS26_hz16 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B (165698521417663833 / 200000000000000000) (414246303544159583 / 500000000000000000) (√((1 : ℝ) - (((14 / 25) : ℝ)^2))) := bsqrt (lowCoarseS26_hz15 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS26_hz17 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B (263717387466394877 / 1000000000000000000) (263717387466394879 / 1000000000000000000) ((√((1 : ℝ) - (((14 / 25) : ℝ)^2))) / Real.pi) := bdiv (lowCoarseS26_hz16 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS26_hz18 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B (96487842688663913 / 250000000000000000) (385951370754656151 / 1000000000000000000) (((14 / 25) : ℝ) * (kdot ((14 / 25)))) := bmul (bpoint ((14 / 25) : ℝ)) (lowCoarseS26_hz13 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS26_hz19 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B (649668758221050529 / 1000000000000000000) (64966875822105103 / 100000000000000000) (((√((1 : ℝ) - (((14 / 25) : ℝ)^2))) / Real.pi) + (((14 / 25) : ℝ) * (kdot ((14 / 25))))) := badd (lowCoarseS26_hz17 hx hc) (lowCoarseS26_hz18 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS26_hz20 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B (649668758221050529 / 1000000000000000000) (64966875822105103 / 100000000000000000) (kappa ((14 / 25))) := by rw [kappa_eq]; exact (lowCoarseS26_hz19 hx hc)

theorem lowCoarseS26_hz21 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B (173264202435670071 / 250000000000000000) (346528404871340359 / 500000000000000000) (kdot ((57 / 100))) := by
    constructor
    · apply bkdot_lower (q := (10466811363896291 / 20000000000000000)) (a := (120536308947726227 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (523340568194814549 / 1000000000000000000)) (a := (120536308947726057 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS26_hz22 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B (3249 / 10000) (3249 / 10000) (((57 / 100) : ℝ)^2) := bsq (bpoint ((57 / 100) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS26_hz23 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B (6751 / 10000) (6751 / 10000) ((1 : ℝ) - (((57 / 100) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS26_hz22 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS26_hz24 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B (410822346032929421 / 500000000000000000) (821644692065858843 / 1000000000000000000) (√((1 : ℝ) - (((57 / 100) : ℝ)^2))) := bsqrt (lowCoarseS26_hz23 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS26_hz25 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B (130768814207499631 / 500000000000000000) (261537628414999263 / 1000000000000000000) ((√((1 : ℝ) - (((57 / 100) : ℝ)^2))) / Real.pi) := bdiv (lowCoarseS26_hz24 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS26_hz26 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B (395042381553327761 / 1000000000000000000) (39504238155332801 / 100000000000000000) (((57 / 100) : ℝ) * (kdot ((57 / 100)))) := bmul (bpoint ((57 / 100) : ℝ)) (lowCoarseS26_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS26_hz27 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B (656580009968327023 / 1000000000000000000) (656580009968327273 / 1000000000000000000) (((√((1 : ℝ) - (((57 / 100) : ℝ)^2))) / Real.pi) + (((57 / 100) : ℝ) * (kdot ((57 / 100))))) := badd (lowCoarseS26_hz25 hx hc) (lowCoarseS26_hz26 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS26_hz28 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B (656580009968327023 / 1000000000000000000) (656580009968327273 / 1000000000000000000) (kappa ((57 / 100))) := by rw [kappa_eq]; exact (lowCoarseS26_hz27 hx hc)

theorem lowCoarseS26_hz29 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B (649668758221050529 / 1000000000000000000) (656580009968327273 / 1000000000000000000) (kappa c) := bkappa (lowCoarseS26_hz1 hx hc) (by norm_num) (by norm_num) (lowCoarseS26_hz20 hx hc).1 (lowCoarseS26_hz28 hx hc).2

theorem lowCoarseS26_hz30 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B (343419990031672727 / 1000000000000000000) (350331241778949471 / 1000000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (lowCoarseS26_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS26_hz31 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B (343419990031672727 / 500000000000000000) (350331241778949471 / 500000000000000000) ((2 : ℝ) * ((1 : ℝ) - (kappa c))) := bmul (bpoint (2 : ℝ)) (lowCoarseS26_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS26_hz32 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B 0 (1 / 8000000) ((8 : ℝ) * (x^2)) := bmul (bpoint (8 : ℝ)) (lowCoarseS26_hz7 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS26_hz33 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B (343419927531672727 / 500000000000000000) (350331241778949471 / 500000000000000000) (((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2))) := bsub (lowCoarseS26_hz31 hx hc) (lowCoarseS26_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS26_hz34 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B (165751603921451747 / 200000000000000000) (837055842556456291 / 1000000000000000000) (√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) := bsqrt (lowCoarseS26_hz33 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS26_hz35 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B (6782329983125268139 / 250000000000000000) (13564659966250536279 / 500000000000000000) ((2 : ℝ) * (√(184 : ℝ))) := bmul (bpoint (2 : ℝ)) (lowCoarseS26_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS26_hz36 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B 0 (678232998312527 / 200000000000000000) (((2 : ℝ) * (√(184 : ℝ))) * x) := bmul (lowCoarseS26_hz35 hx hc) (lowCoarseS26_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS26_hz37 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B (8253668546156961 / 10000000000000000) (837055842556456291 / 1000000000000000000) ((√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) - (((2 : ℝ) * (√(184 : ℝ))) * x)) := bsub (lowCoarseS26_hz34 hx hc) (lowCoarseS26_hz36 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS26_hz38 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B (8253668546156961 / 10000000000000000) (837055842556456291 / 1000000000000000000) (ndm x c) := by
    convert (lowCoarseS26_hz37 hx hc) using 1 <;>
      norm_num [ndm] <;> ring

theorem lowCoarseS26_hz39 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B 1 (1003394039991562637 / 1000000000000000000) ((nap x)^2) := bsq (lowCoarseS26_hz6 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS26_hz40 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B 2 (1003394039991562637 / 500000000000000000) ((2 : ℝ) * ((nap x)^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS26_hz39 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS26_hz41 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B (340615222349103811 / 500000000000000000) (700662483557898943 / 1000000000000000000) ((ndm x c)^2) := bsq (lowCoarseS26_hz38 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS26_hz42 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B (1299337516442101057 / 1000000000000000000) (331389408821229413 / 250000000000000000) (((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) := bsub (lowCoarseS26_hz40 hx hc) (lowCoarseS26_hz41 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS26_hz43 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B (199322335762284863 / 200000000000000000) 1 ((nam x)^2) := bsq (lowCoarseS26_hz12 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS26_hz44 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B (199322335762284863 / 100000000000000000) 2 ((2 : ℝ) * ((nam x)^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS26_hz43 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS26_hz45 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B (20302148694407829 / 31250000000000000) (665032160201955371 / 1000000000000000000) ((((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) / ((2 : ℝ) * ((nam x)^2))) := bdiv (lowCoarseS26_hz42 hx hc) (lowCoarseS26_hz44 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS26_hz46 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B (20302148694407829 / 31250000000000000) (665032160201955371 / 1000000000000000000) (nc1 x c) := by
    convert (lowCoarseS26_hz45 hx hc) using 1 <;>
      norm_num [nc1] <;> ring

theorem lowCoarseS26_hz47 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B (34459943817379969 / 50000000000000000) (346528404871340359 / 500000000000000000) (kdot c) := bkdot (lowCoarseS26_hz1 hx hc) (lowCoarseS26_hz13 hx hc).1 (lowCoarseS26_hz21 hx hc).2

theorem lowCoarseS26_hz48 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B (725092401762400821 / 1000000000000000000) (90636550220300103 / 125000000000000000) (kdot ((20302148694407829 / 31250000000000000))) := by
    constructor
    · apply bkdot_lower (q := (460830334785135697 / 1000000000000000000)) (a := (86364769103925597 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (28801895924070981 / 62500000000000000)) (a := (215911922759813991 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS26_hz49 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B (182895545393567361 / 250000000000000000) (731582181574269447 / 1000000000000000000) (kdot ((665032160201955371 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (448528705796726627 / 1000000000000000000)) (a := (421629723229437077 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (224264352898363313 / 500000000000000000)) (a := (210814861614718537 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS26_hz50 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B (725092401762400821 / 1000000000000000000) (731582181574269447 / 1000000000000000000) (kdot (nc1 x c)) := bkdot (lowCoarseS26_hz46 hx hc) (lowCoarseS26_hz48 hx hc).1 (lowCoarseS26_hz49 hx hc).2

theorem lowCoarseS26_hz51 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B (196 / 625) (3249 / 10000) (c^2) := bsq (lowCoarseS26_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS26_hz52 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B (6751 / 10000) (429 / 625) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS26_hz51 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS26_hz53 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B (410822346032929421 / 500000000000000000) (414246303544159583 / 500000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (lowCoarseS26_hz52 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS26_hz54 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B (566276598528759217 / 1000000000000000000) (574192443164026747 / 1000000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (lowCoarseS26_hz53 hx hc) (lowCoarseS26_hz47 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS26_hz55 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B (566276598528759217 / 1000000000000000000) (574192443164026747 / 1000000000000000000) (npa c) := by
    convert (lowCoarseS26_hz54 hx hc) using 1 <;>
      norm_num [npa] <;> ring

theorem lowCoarseS26_hz56 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B (130768814207499631 / 500000000000000000) (263717387466394879 / 1000000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (lowCoarseS26_hz53 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS26_hz57 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B (96487842688663913 / 250000000000000000) (39504238155332801 / 100000000000000000) (c * (kdot c)) := bmul (lowCoarseS26_hz1 hx hc) (lowCoarseS26_hz47 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS26_hz58 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B (-33376188284582187 / 250000000000000000) (-122233983288260773 / 1000000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (lowCoarseS26_hz56 hx hc) (lowCoarseS26_hz57 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS26_hz59 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B (-33376188284582187 / 250000000000000000) (-122233983288260773 / 1000000000000000000) (npp c) := by
    convert (lowCoarseS26_hz58 hx hc) using 1 <;>
      norm_num [npp] <;> ring

theorem lowCoarseS26_hz60 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B 0 (23 / 4000) ((46 : ℝ) * x) := bmul (bpoint (46 : ℝ)) (lowCoarseS26_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS26_hz61 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B (9591663046625439083 / 1000000000000000000) (2399353261656359771 / 250000000000000000) ((√(92 : ℝ)) + ((46 : ℝ) * x)) := badd (lowCoarseS26_hz3 hx hc) (lowCoarseS26_hz60 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS26_hz62 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B (28774989139876317249 / 250000000000000000) (7198059784969079313 / 62500000000000000) ((12 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (bpoint (12 : ℝ)) (lowCoarseS26_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS26_hz63 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B 0 (14396119569938159 / 1000000000000000000) (((12 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS26_hz62 hx hc) (lowCoarseS26_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS26_hz64 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B 0 (14396119569938159 / 1000000000000000000) (nr1 x) := by
    convert (lowCoarseS26_hz63 hx hc) using 1 <;>
      norm_num [nr1] <;> ring

theorem lowCoarseS26_hz65 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B (9591663046625439083 / 125000000000000000) (2399353261656359771 / 31250000000000000) ((8 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (bpoint (8 : ℝ)) (lowCoarseS26_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS26_hz66 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B 0 (59983831541409 / 6250000000000000) (((8 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS26_hz65 hx hc) (lowCoarseS26_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS26_hz67 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B 0 (59983831541409 / 6250000000000000) (nrpp x) := by
    convert (lowCoarseS26_hz66 hx hc) using 1 <;>
      norm_num [nrpp] <;> ring

theorem lowCoarseS26_hz68 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B 0 (847791247890659 / 500000000000000000) (ne0 x) := by
    convert (lowCoarseS26_hz4 hx hc) using 1 <;>
      norm_num [ne0] <;> ring

theorem lowCoarseS26_hz69 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B (566276598528759217 / 1000000000000000000) (294294281366982453 / 500000000000000000) ((npa c) + (nr1 x)) := badd (lowCoarseS26_hz55 hx hc) (lowCoarseS26_hz64 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS26_hz70 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B (566276598528759217 / 1000000000000000000) (589588267492359737 / 1000000000000000000) (((npa c) + (nr1 x)) / (nam x)) := bdiv (lowCoarseS26_hz69 hx hc) (lowCoarseS26_hz12 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS26_hz71 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B (566276598528759217 / 1000000000000000000) (118256769997628211 / 200000000000000000) ((((npa c) + (nr1 x)) / (nam x)) + (ne0 x)) := badd (lowCoarseS26_hz70 hx hc) (lowCoarseS26_hz68 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS26_hz72 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B (566276598528759217 / 1000000000000000000) (118256769997628211 / 200000000000000000) (nlam x c) := by
    convert (lowCoarseS26_hz71 hx hc) using 1 <;>
      norm_num [nlam] <;> ring

theorem lowCoarseS26_hz73 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS26_hz74 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B 0 (59947894041409 / 100000000000000000) ((√(23 : ℝ)) * x) := bmul (lowCoarseS26_hz73 hx hc) (lowCoarseS26_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS26_hz75 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B (1 / 2) (50059947894041409 / 100000000000000000) (((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)) := badd (bpoint ((1 / 2) : ℝ)) (lowCoarseS26_hz74 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS26_hz76 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B (176776695296636881 / 250000000000000000) (353765274914177413 / 500000000000000000) (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) := bsqrt (lowCoarseS26_hz75 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS26_hz77 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B 0 (59947894041409 / 50000000000000000) ((√(92 : ℝ)) * x) := bmul (lowCoarseS26_hz3 hx hc) (lowCoarseS26_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS26_hz78 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B (176776695296636881 / 250000000000000000) (354364753854591503 / 500000000000000000) ((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x)) := badd (lowCoarseS26_hz76 hx hc) (lowCoarseS26_hz77 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS26_hz79 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B (499999999999999999 / 1000000000000000000) (251148757548850447 / 500000000000000000) (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2) := bsq (lowCoarseS26_hz78 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS26_hz80 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B (499999999999999999 / 125000000000000000) (251148757548850447 / 62500000000000000) ((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) := bmul (bpoint (8 : ℝ)) (lowCoarseS26_hz79 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS26_hz81 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B (7673330437300351251 / 200000000000000000) (1928302689874485209 / 50000000000000000) (((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (lowCoarseS26_hz80 hx hc) (lowCoarseS26_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS26_hz82 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B 0 (2410378362343107 / 500000000000000000) ((((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS26_hz81 hx hc) (lowCoarseS26_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS26_hz83 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B 0 (2410378362343107 / 500000000000000000) (nrs x) := by
    convert (lowCoarseS26_hz82 hx hc) using 1 <;>
      norm_num [nrs] <;> ring

theorem lowCoarseS26_hz84 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B (-33376188284582187 / 250000000000000000) (-112636570241635333 / 1000000000000000000) ((npp c) + (nrpp x)) := badd (lowCoarseS26_hz59 hx hc) (lowCoarseS26_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS26_hz85 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B (-97669698551472841 / 1000000000000000000) (-28159142560408833 / 500000000000000000) (if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) := bweaken (bfirst (lowCoarseS26_hz84 hx hc) (lowCoarseS26_hz50 hx hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem lowCoarseS26_hz86 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B (64133837208260309 / 200000000000000000) (69923318251359699 / 200000000000000000) ((nlam x c)^2) := bsq (lowCoarseS26_hz72 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS26_hz87 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B (26379343463030113 / 62500000000000000) (221133887051439617 / 500000000000000000) ((nc1 x c)^2) := bsq (lowCoarseS26_hz46 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS26_hz88 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B (278866112948560383 / 500000000000000000) (36120656536969887 / 62500000000000000) ((1 : ℝ) - ((nc1 x c)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS26_hz87 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS26_hz89 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B (186703679981327759 / 250000000000000000) (760217406135585791 / 1000000000000000000) (√((1 : ℝ) - ((nc1 x c)^2))) := bsqrt (lowCoarseS26_hz88 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS26_hz90 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B (2346187637710076131 / 1000000000000000000) (2388293418246644529 / 1000000000000000000) (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))) := bmul pi_mem (lowCoarseS26_hz89 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS26_hz91 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B (134267081084500691 / 1000000000000000000) (74507380747694791 / 500000000000000000) (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2))))) := bdiv (lowCoarseS26_hz86 hx hc) (lowCoarseS26_hz90 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS26_hz92 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B (731947650660557 / 20000000000000000) (23174119093642979 / 250000000000000000) ((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) := badd (lowCoarseS26_hz85 hx hc) (lowCoarseS26_hz91 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS26_hz93 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B 0 (2875000000001 / 1000000000000000000) ((ne0 x)^2) := bsq (lowCoarseS26_hz68 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS26_hz94 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B (731947650660557 / 20000000000000000) (92699351374571917 / 1000000000000000000) (((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) + ((ne0 x)^2)) := badd (lowCoarseS26_hz92 hx hc) (lowCoarseS26_hz93 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS26_hz95 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B (731947650660557 / 20000000000000000) (97520108099258131 / 1000000000000000000) ((((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) + ((ne0 x)^2)) + (nrs x)) := badd (lowCoarseS26_hz94 hx hc) (lowCoarseS26_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS26_hz96 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B (731947650660557 / 20000000000000000) (97520108099258131 / 1000000000000000000) (nu x c) := by
    convert (lowCoarseS26_hz95 hx hc) using 1 <;>
      norm_num [nu] <;> ring

theorem lowCoarseS26_hz97 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B (-35775541546238547 / 250000000000000000) (-122233983288260773 / 1000000000000000000) ((npp c) - (nrpp x)) := bsub (lowCoarseS26_hz59 hx hc) (lowCoarseS26_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS26_hz98 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B (-35775541546238547 / 250000000000000000) (-122233983288260773 / 1000000000000000000) (min ((npp c) - (nrpp x)) (0 : ℝ)) := bweaken (bmin (lowCoarseS26_hz97 hx hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem lowCoarseS26_hz99 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B (-104690994925592437 / 1000000000000000000) (-11078866564933771 / 125000000000000000) ((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) := bmul (lowCoarseS26_hz50 hx hc) (lowCoarseS26_hz98 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS26_hz100 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B (-52346934962796219 / 500000000000000000) (-11078866564933771 / 125000000000000000) (((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) - ((ne0 x)^2)) := bsub (lowCoarseS26_hz99 hx hc) (lowCoarseS26_hz93 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS26_hz101 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B (-27378656662569663 / 250000000000000000) (-11078866564933771 / 125000000000000000) ((((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) - ((ne0 x)^2)) - (nrs x)) := bsub (lowCoarseS26_hz100 hx hc) (lowCoarseS26_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS26_hz102 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B (-27378656662569663 / 250000000000000000) (-11078866564933771 / 125000000000000000) (nl x c) := by
    convert (lowCoarseS26_hz101 hx hc) using 1 <;>
      norm_num [nl] <;> ring

theorem lowCoarseS26_hz103 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B 0 (97520108099258131 / 1000000000000000000) |(nu x c)| := bweaken (babs (lowCoarseS26_hz96 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS26_hz104 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B 0 (27378656662569663 / 250000000000000000) |(nl x c)| := bweaken (babs (lowCoarseS26_hz102 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS26_hz105 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B 0 (27378656662569663 / 250000000000000000) (max |(nu x c)| |(nl x c)|) := bweaken (bmax (lowCoarseS26_hz103 hx hc) (lowCoarseS26_hz104 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS26_hz106 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) : B 0 (27378656662569663 / 250000000000000000) (ns x c) := by
    convert (lowCoarseS26_hz105 hx hc) using 1 <;>
      norm_num [ns] <;> ring

theorem lowCoarseS26 {x c : ℝ}
    (hx : B 0 (1/8000) x) (hc : B (14 / 25) (57 / 100) c) :
    0 < nam x ∧ 0 ≤ ndm x c ∧ ndm x c ^ 2 ≤ 2 * nap x ^ 2 ∧ nc1 x c < 1 ∧
    0 ≤ npa c - nr1 x ∧ ne0 x ≤ (npa c - nr1 x) / nap x ∧ ns x c ≤ (1 / 5) := by
  refine ⟨lt_of_lt_of_le (by norm_num) (lowCoarseS26_hz12 hx hc).1,
    le_trans (by norm_num) (lowCoarseS26_hz38 hx hc).1, ?_,
    lt_of_le_of_lt (lowCoarseS26_hz46 hx hc).2 (by norm_num), ?_, ?_, (lowCoarseS26_hz106 hx hc).2.trans (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (lowCoarseS26_hz38 hx hc).1) (lowCoarseS26_hz38 hx hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) (lowCoarseS26_hz6 hx hc).1 2
    nlinarith only [h1,h2]
  · linarith only [(lowCoarseS26_hz55 hx hc).1,(lowCoarseS26_hz64 hx hc).2]
  · have hap : 0 < nap x := lt_of_lt_of_le (by norm_num) (lowCoarseS26_hz6 hx hc).1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul (lowCoarseS26_hz68 hx hc).2 (lowCoarseS26_hz6 hx hc).2 (le_trans (by norm_num) (lowCoarseS26_hz6 hx hc).1) (by norm_num)
    linarith only [h,(lowCoarseS26_hz55 hx hc).1,(lowCoarseS26_hz64 hx hc).2]

theorem lowCoarseS27_hz0 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B 0 (1 / 8000) x := hx

theorem lowCoarseS27_hz1 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B (57 / 100) (29 / 50) c := hc

theorem lowCoarseS27_hz2 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B (6782329983125268139 / 500000000000000000) (13564659966250536279 / 1000000000000000000) (√(184 : ℝ)) := bsqrt (bpoint (184 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS27_hz3 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS27_hz4 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B 0 (847791247890659 / 500000000000000000) ((√(184 : ℝ)) * x) := bmul (lowCoarseS27_hz2 hx hc) (lowCoarseS27_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS27_hz5 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B 1 (500847791247890659 / 500000000000000000) ((1 : ℝ) + ((√(184 : ℝ)) * x)) := badd (bpoint (1 : ℝ)) (lowCoarseS27_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS27_hz6 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B 1 (500847791247890659 / 500000000000000000) (nap x) := by
    convert (lowCoarseS27_hz5 hx hc) using 1 <;>
      norm_num [nap] <;> ring

theorem lowCoarseS27_hz7 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B 0 (1 / 64000000) (x^2) := bsq (lowCoarseS27_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS27_hz8 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B 0 (1 / 32000000) ((2 : ℝ) * (x^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS27_hz7 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS27_hz9 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B (31999999 / 32000000) 1 ((1 : ℝ) - ((2 : ℝ) * (x^2))) := bsub (bpoint (1 : ℝ)) (lowCoarseS27_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS27_hz10 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B (999999984374999877 / 1000000000000000000) 1 (√((1 : ℝ) - ((2 : ℝ) * (x^2)))) := bsqrt (lowCoarseS27_hz9 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS27_hz11 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B (998304401879218559 / 1000000000000000000) 1 ((√((1 : ℝ) - ((2 : ℝ) * (x^2)))) - ((√(184 : ℝ)) * x)) := bsub (lowCoarseS27_hz10 hx hc) (lowCoarseS27_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS27_hz12 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B (998304401879218559 / 1000000000000000000) 1 (nam x) := by
    convert (lowCoarseS27_hz11 hx hc) using 1 <;>
      norm_num [nam] <;> ring

theorem lowCoarseS27_hz13 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B (173264202435670071 / 250000000000000000) (346528404871340359 / 500000000000000000) (kdot ((57 / 100))) := by
    constructor
    · apply bkdot_lower (q := (10466811363896291 / 20000000000000000)) (a := (120536308947726227 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (523340568194814549 / 1000000000000000000)) (a := (120536308947726057 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS27_hz14 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B (3249 / 10000) (3249 / 10000) (((57 / 100) : ℝ)^2) := bsq (bpoint ((57 / 100) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS27_hz15 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B (6751 / 10000) (6751 / 10000) ((1 : ℝ) - (((57 / 100) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS27_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS27_hz16 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B (410822346032929421 / 500000000000000000) (821644692065858843 / 1000000000000000000) (√((1 : ℝ) - (((57 / 100) : ℝ)^2))) := bsqrt (lowCoarseS27_hz15 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS27_hz17 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B (130768814207499631 / 500000000000000000) (261537628414999263 / 1000000000000000000) ((√((1 : ℝ) - (((57 / 100) : ℝ)^2))) / Real.pi) := bdiv (lowCoarseS27_hz16 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS27_hz18 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B (395042381553327761 / 1000000000000000000) (39504238155332801 / 100000000000000000) (((57 / 100) : ℝ) * (kdot ((57 / 100)))) := bmul (bpoint ((57 / 100) : ℝ)) (lowCoarseS27_hz13 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS27_hz19 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B (656580009968327023 / 1000000000000000000) (656580009968327273 / 1000000000000000000) (((√((1 : ℝ) - (((57 / 100) : ℝ)^2))) / Real.pi) + (((57 / 100) : ℝ) * (kdot ((57 / 100))))) := badd (lowCoarseS27_hz17 hx hc) (lowCoarseS27_hz18 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS27_hz20 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B (656580009968327023 / 1000000000000000000) (656580009968327273 / 1000000000000000000) (kappa ((57 / 100))) := by rw [kappa_eq]; exact (lowCoarseS27_hz19 hx hc)

theorem lowCoarseS27_hz21 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B (2722451012134883 / 3906250000000000) (696947459106530257 / 1000000000000000000) (kdot ((29 / 50))) := by
    constructor
    · apply bkdot_lower (q := (515580046947248127 / 1000000000000000000)) (a := (238016909030661399 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (257790023473624063 / 500000000000000000)) (a := (47603381806132247 / 100000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS27_hz22 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B (841 / 2500) (841 / 2500) (((29 / 50) : ℝ)^2) := bsq (bpoint ((29 / 50) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS27_hz23 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B (1659 / 2500) (1659 / 2500) ((1 : ℝ) - (((29 / 50) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS27_hz22 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS27_hz24 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B (20365411854416301 / 25000000000000000) (814616474176652041 / 1000000000000000000) (√((1 : ℝ) - (((29 / 50) : ℝ)^2))) := bsqrt (lowCoarseS27_hz23 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS27_hz25 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B (259300477178610963 / 1000000000000000000) (64825119294652741 / 250000000000000000) ((√((1 : ℝ) - (((29 / 50) : ℝ)^2))) / Real.pi) := bdiv (lowCoarseS27_hz24 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS27_hz26 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B (404229526281787427 / 1000000000000000000) (8084590525635751 / 20000000000000000) (((29 / 50) : ℝ) * (kdot ((29 / 50)))) := bmul (bpoint ((29 / 50) : ℝ)) (lowCoarseS27_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS27_hz27 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B (66353000346039839 / 100000000000000000) (331765001730199257 / 500000000000000000) (((√((1 : ℝ) - (((29 / 50) : ℝ)^2))) / Real.pi) + (((29 / 50) : ℝ) * (kdot ((29 / 50))))) := badd (lowCoarseS27_hz25 hx hc) (lowCoarseS27_hz26 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS27_hz28 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B (66353000346039839 / 100000000000000000) (331765001730199257 / 500000000000000000) (kappa ((29 / 50))) := by rw [kappa_eq]; exact (lowCoarseS27_hz27 hx hc)

theorem lowCoarseS27_hz29 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B (656580009968327023 / 1000000000000000000) (331765001730199257 / 500000000000000000) (kappa c) := bkappa (lowCoarseS27_hz1 hx hc) (by norm_num) (by norm_num) (lowCoarseS27_hz20 hx hc).1 (lowCoarseS27_hz28 hx hc).2

theorem lowCoarseS27_hz30 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B (168234998269800743 / 500000000000000000) (343419990031672977 / 1000000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (lowCoarseS27_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS27_hz31 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B (168234998269800743 / 250000000000000000) (343419990031672977 / 500000000000000000) ((2 : ℝ) * ((1 : ℝ) - (kappa c))) := bmul (bpoint (2 : ℝ)) (lowCoarseS27_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS27_hz32 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B 0 (1 / 8000000) ((8 : ℝ) * (x^2)) := bmul (bpoint (8 : ℝ)) (lowCoarseS27_hz7 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS27_hz33 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B (168234967019800743 / 250000000000000000) (343419990031672977 / 500000000000000000) (((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2))) := bsub (lowCoarseS27_hz31 hx hc) (lowCoarseS27_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS27_hz34 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B (410164560901841863 / 500000000000000000) (41437904751065357 / 50000000000000000) (√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) := bsqrt (lowCoarseS27_hz33 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS27_hz35 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B (6782329983125268139 / 250000000000000000) (13564659966250536279 / 500000000000000000) ((2 : ℝ) * (√(184 : ℝ))) := bmul (bpoint (2 : ℝ)) (lowCoarseS27_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS27_hz36 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B 0 (678232998312527 / 200000000000000000) (((2 : ℝ) * (√(184 : ℝ))) * x) := bmul (lowCoarseS27_hz35 hx hc) (lowCoarseS27_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS27_hz37 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B (816937956812121091 / 1000000000000000000) (41437904751065357 / 50000000000000000) ((√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) - (((2 : ℝ) * (√(184 : ℝ))) * x)) := bsub (lowCoarseS27_hz34 hx hc) (lowCoarseS27_hz36 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS27_hz38 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B (816937956812121091 / 1000000000000000000) (41437904751065357 / 50000000000000000) (ndm x c) := by
    convert (lowCoarseS27_hz37 hx hc) using 1 <;>
      norm_num [ndm] <;> ring

theorem lowCoarseS27_hz39 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B 1 (1003394039991562637 / 1000000000000000000) ((nap x)^2) := bsq (lowCoarseS27_hz6 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS27_hz40 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B 2 (1003394039991562637 / 500000000000000000) ((2 : ℝ) * ((nap x)^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS27_hz39 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS27_hz41 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B (41711726580022689 / 62500000000000000) (137367996012669191 / 200000000000000000) ((ndm x c)^2) := bsq (lowCoarseS27_hz38 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS27_hz42 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B (262632003987330809 / 200000000000000000) (5357601818811049 / 4000000000000000) (((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) := bsub (lowCoarseS27_hz40 hx hc) (lowCoarseS27_hz41 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS27_hz43 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B (199322335762284863 / 200000000000000000) 1 ((nam x)^2) := bsq (lowCoarseS27_hz12 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS27_hz44 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B (199322335762284863 / 100000000000000000) 2 ((2 : ℝ) * ((nam x)^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS27_hz43 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS27_hz45 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B (328290004984163511 / 500000000000000000) (671977101602980179 / 1000000000000000000) ((((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) / ((2 : ℝ) * ((nam x)^2))) := bdiv (lowCoarseS27_hz42 hx hc) (lowCoarseS27_hz44 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS27_hz46 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B (328290004984163511 / 500000000000000000) (671977101602980179 / 1000000000000000000) (nc1 x c) := by
    convert (lowCoarseS27_hz45 hx hc) using 1 <;>
      norm_num [nc1] <;> ring

theorem lowCoarseS27_hz47 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B (173264202435670071 / 250000000000000000) (696947459106530257 / 1000000000000000000) (kdot c) := bkdot (lowCoarseS27_hz1 hx hc) (lowCoarseS27_hz13 hx hc).1 (lowCoarseS27_hz21 hx hc).2

theorem lowCoarseS27_hz48 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B (3639987875832687 / 5000000000000000) (363998787583268701 / 500000000000000000) (kdot ((328290004984163511 / 500000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (91061871800953527 / 200000000000000000)) (a := (427260409807708021 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (227654679502383817 / 500000000000000000)) (a := (427260409807708019 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS27_hz49 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B (73455468028618057 / 100000000000000000) (734554680286180573 / 1000000000000000000) (kdot ((671977101602980179 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (442931858035237627 / 1000000000000000000)) (a := (208480266585682259 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (221465929017618813 / 500000000000000000)) (a := (104240133292841129 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS27_hz50 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B (3639987875832687 / 5000000000000000) (734554680286180573 / 1000000000000000000) (kdot (nc1 x c)) := bkdot (lowCoarseS27_hz46 hx hc) (lowCoarseS27_hz48 hx hc).1 (lowCoarseS27_hz49 hx hc).2

theorem lowCoarseS27_hz51 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B (3249 / 10000) (841 / 2500) (c^2) := bsq (lowCoarseS27_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS27_hz52 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B (1659 / 2500) (6751 / 10000) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS27_hz51 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS27_hz53 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B (20365411854416301 / 25000000000000000) (821644692065858843 / 1000000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (lowCoarseS27_hz52 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS27_hz54 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B (564575494756700959 / 1000000000000000000) (286321590211833901 / 500000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (lowCoarseS27_hz53 hx hc) (lowCoarseS27_hz47 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS27_hz55 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B (564575494756700959 / 1000000000000000000) (286321590211833901 / 500000000000000000) (npa c) := by
    convert (lowCoarseS27_hz54 hx hc) using 1 <;>
      norm_num [npa] <;> ring

theorem lowCoarseS27_hz56 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B (259300477178610963 / 1000000000000000000) (261537628414999263 / 1000000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (lowCoarseS27_hz53 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS27_hz57 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B (395042381553327761 / 1000000000000000000) (8084590525635751 / 20000000000000000) (c * (kdot c)) := bmul (lowCoarseS27_hz1 hx hc) (lowCoarseS27_hz47 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS27_hz58 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B (-144929049103176587 / 1000000000000000000) (-66752376569164249 / 500000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (lowCoarseS27_hz56 hx hc) (lowCoarseS27_hz57 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS27_hz59 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B (-144929049103176587 / 1000000000000000000) (-66752376569164249 / 500000000000000000) (npp c) := by
    convert (lowCoarseS27_hz58 hx hc) using 1 <;>
      norm_num [npp] <;> ring

theorem lowCoarseS27_hz60 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B 0 (23 / 4000) ((46 : ℝ) * x) := bmul (bpoint (46 : ℝ)) (lowCoarseS27_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS27_hz61 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B (9591663046625439083 / 1000000000000000000) (2399353261656359771 / 250000000000000000) ((√(92 : ℝ)) + ((46 : ℝ) * x)) := badd (lowCoarseS27_hz3 hx hc) (lowCoarseS27_hz60 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS27_hz62 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B (28774989139876317249 / 250000000000000000) (7198059784969079313 / 62500000000000000) ((12 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (bpoint (12 : ℝ)) (lowCoarseS27_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS27_hz63 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B 0 (14396119569938159 / 1000000000000000000) (((12 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS27_hz62 hx hc) (lowCoarseS27_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS27_hz64 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B 0 (14396119569938159 / 1000000000000000000) (nr1 x) := by
    convert (lowCoarseS27_hz63 hx hc) using 1 <;>
      norm_num [nr1] <;> ring

theorem lowCoarseS27_hz65 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B (9591663046625439083 / 125000000000000000) (2399353261656359771 / 31250000000000000) ((8 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (bpoint (8 : ℝ)) (lowCoarseS27_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS27_hz66 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B 0 (59983831541409 / 6250000000000000) (((8 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS27_hz65 hx hc) (lowCoarseS27_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS27_hz67 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B 0 (59983831541409 / 6250000000000000) (nrpp x) := by
    convert (lowCoarseS27_hz66 hx hc) using 1 <;>
      norm_num [nrpp] <;> ring

theorem lowCoarseS27_hz68 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B 0 (847791247890659 / 500000000000000000) (ne0 x) := by
    convert (lowCoarseS27_hz4 hx hc) using 1 <;>
      norm_num [ne0] <;> ring

theorem lowCoarseS27_hz69 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B (564575494756700959 / 1000000000000000000) (587039299993605961 / 1000000000000000000) ((npa c) + (nr1 x)) := badd (lowCoarseS27_hz55 hx hc) (lowCoarseS27_hz64 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS27_hz70 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B (564575494756700959 / 1000000000000000000) (588036373363231791 / 1000000000000000000) (((npa c) + (nr1 x)) / (nam x)) := bdiv (lowCoarseS27_hz69 hx hc) (lowCoarseS27_hz12 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS27_hz71 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B (564575494756700959 / 1000000000000000000) (589731955859013109 / 1000000000000000000) ((((npa c) + (nr1 x)) / (nam x)) + (ne0 x)) := badd (lowCoarseS27_hz70 hx hc) (lowCoarseS27_hz68 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS27_hz72 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B (564575494756700959 / 1000000000000000000) (589731955859013109 / 1000000000000000000) (nlam x c) := by
    convert (lowCoarseS27_hz71 hx hc) using 1 <;>
      norm_num [nlam] <;> ring

theorem lowCoarseS27_hz73 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS27_hz74 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B 0 (59947894041409 / 100000000000000000) ((√(23 : ℝ)) * x) := bmul (lowCoarseS27_hz73 hx hc) (lowCoarseS27_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS27_hz75 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B (1 / 2) (50059947894041409 / 100000000000000000) (((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)) := badd (bpoint ((1 / 2) : ℝ)) (lowCoarseS27_hz74 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS27_hz76 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B (176776695296636881 / 250000000000000000) (353765274914177413 / 500000000000000000) (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) := bsqrt (lowCoarseS27_hz75 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS27_hz77 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B 0 (59947894041409 / 50000000000000000) ((√(92 : ℝ)) * x) := bmul (lowCoarseS27_hz3 hx hc) (lowCoarseS27_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS27_hz78 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B (176776695296636881 / 250000000000000000) (354364753854591503 / 500000000000000000) ((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x)) := badd (lowCoarseS27_hz76 hx hc) (lowCoarseS27_hz77 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS27_hz79 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B (499999999999999999 / 1000000000000000000) (251148757548850447 / 500000000000000000) (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2) := bsq (lowCoarseS27_hz78 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS27_hz80 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B (499999999999999999 / 125000000000000000) (251148757548850447 / 62500000000000000) ((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) := bmul (bpoint (8 : ℝ)) (lowCoarseS27_hz79 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS27_hz81 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B (7673330437300351251 / 200000000000000000) (1928302689874485209 / 50000000000000000) (((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (lowCoarseS27_hz80 hx hc) (lowCoarseS27_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS27_hz82 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B 0 (2410378362343107 / 500000000000000000) ((((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS27_hz81 hx hc) (lowCoarseS27_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS27_hz83 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B 0 (2410378362343107 / 500000000000000000) (nrs x) := by
    convert (lowCoarseS27_hz82 hx hc) using 1 <;>
      norm_num [nrs] <;> ring

theorem lowCoarseS27_hz84 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B (-144929049103176587 / 1000000000000000000) (-61953670045851529 / 500000000000000000) ((npp c) + (nrpp x)) := badd (lowCoarseS27_hz59 hx hc) (lowCoarseS27_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS27_hz85 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B (-26614577832041011 / 250000000000000000) (-61953670045851529 / 1000000000000000000) (if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) := bweaken (bfirst (lowCoarseS27_hz84 hx hc) (lowCoarseS27_hz50 hx hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem lowCoarseS27_hz86 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B (39843186159971709 / 125000000000000000) (347783779761296987 / 1000000000000000000) ((nlam x c)^2) := bsq (lowCoarseS27_hz72 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS27_hz87 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B (431097309490008411 / 1000000000000000000) (451553225078741947 / 1000000000000000000) ((nc1 x c)^2) := bsq (lowCoarseS27_hz46 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS27_hz88 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B (548446774921258053 / 1000000000000000000) (568902690509991589 / 1000000000000000000) ((1 : ℝ) - ((nc1 x c)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS27_hz87 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS27_hz89 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B (740571924205379293 / 1000000000000000000) (188564095619697639 / 250000000000000000) (√((1 : ℝ) - ((nc1 x c)^2))) := bsqrt (lowCoarseS27_hz88 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS27_hz90 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B (2326575316538476763 / 1000000000000000000) (1184783155059290827 / 500000000000000000) (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))) := bmul pi_mem (lowCoarseS27_hz89 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS27_hz91 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B (134516382984792899 / 1000000000000000000) (9342696142509163 / 62500000000000000) (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2))))) := bdiv (lowCoarseS27_hz86 hx hc) (lowCoarseS27_hz90 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS27_hz92 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B (5611614331325771 / 200000000000000000) (87529468234295079 / 1000000000000000000) ((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) := badd (lowCoarseS27_hz85 hx hc) (lowCoarseS27_hz91 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS27_hz93 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B 0 (2875000000001 / 1000000000000000000) ((ne0 x)^2) := bsq (lowCoarseS27_hz68 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS27_hz94 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B (5611614331325771 / 200000000000000000) (2188308580857377 / 25000000000000000) (((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) + ((ne0 x)^2)) := badd (lowCoarseS27_hz92 hx hc) (lowCoarseS27_hz93 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS27_hz95 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B (5611614331325771 / 200000000000000000) (46176549979490647 / 500000000000000000) ((((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) + ((ne0 x)^2)) + (nrs x)) := badd (lowCoarseS27_hz94 hx hc) (lowCoarseS27_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS27_hz96 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B (5611614331325771 / 200000000000000000) (46176549979490647 / 500000000000000000) (nu x c) := by
    convert (lowCoarseS27_hz95 hx hc) using 1 <;>
      norm_num [nu] <;> ring

theorem lowCoarseS27_hz97 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B (-154526462149802027 / 1000000000000000000) (-66752376569164249 / 500000000000000000) ((npp c) - (nrpp x)) := bsub (lowCoarseS27_hz59 hx hc) (lowCoarseS27_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS27_hz98 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B (-154526462149802027 / 1000000000000000000) (-66752376569164249 / 500000000000000000) (min ((npp c) - (nrpp x)) (0 : ℝ)) := bweaken (bmin (lowCoarseS27_hz97 hx hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem lowCoarseS27_hz99 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B (-28377034000050603 / 250000000000000000) (-1214889206973879 / 12500000000000000) ((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) := bmul (lowCoarseS27_hz50 hx hc) (lowCoarseS27_hz98 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS27_hz100 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B (-113511011000202413 / 1000000000000000000) (-1214889206973879 / 12500000000000000) (((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) - ((ne0 x)^2)) := bsub (lowCoarseS27_hz99 hx hc) (lowCoarseS27_hz93 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS27_hz101 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B (-118331767724888627 / 1000000000000000000) (-1214889206973879 / 12500000000000000) ((((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) - ((ne0 x)^2)) - (nrs x)) := bsub (lowCoarseS27_hz100 hx hc) (lowCoarseS27_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS27_hz102 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B (-118331767724888627 / 1000000000000000000) (-1214889206973879 / 12500000000000000) (nl x c) := by
    convert (lowCoarseS27_hz101 hx hc) using 1 <;>
      norm_num [nl] <;> ring

theorem lowCoarseS27_hz103 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B 0 (46176549979490647 / 500000000000000000) |(nu x c)| := bweaken (babs (lowCoarseS27_hz96 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS27_hz104 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B 0 (118331767724888627 / 1000000000000000000) |(nl x c)| := bweaken (babs (lowCoarseS27_hz102 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS27_hz105 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B 0 (118331767724888627 / 1000000000000000000) (max |(nu x c)| |(nl x c)|) := bweaken (bmax (lowCoarseS27_hz103 hx hc) (lowCoarseS27_hz104 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS27_hz106 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) : B 0 (118331767724888627 / 1000000000000000000) (ns x c) := by
    convert (lowCoarseS27_hz105 hx hc) using 1 <;>
      norm_num [ns] <;> ring

theorem lowCoarseS27 {x c : ℝ}
    (hx : B 0 (1/8000) x) (hc : B (57 / 100) (29 / 50) c) :
    0 < nam x ∧ 0 ≤ ndm x c ∧ ndm x c ^ 2 ≤ 2 * nap x ^ 2 ∧ nc1 x c < 1 ∧
    0 ≤ npa c - nr1 x ∧ ne0 x ≤ (npa c - nr1 x) / nap x ∧ ns x c ≤ (1 / 5) := by
  refine ⟨lt_of_lt_of_le (by norm_num) (lowCoarseS27_hz12 hx hc).1,
    le_trans (by norm_num) (lowCoarseS27_hz38 hx hc).1, ?_,
    lt_of_le_of_lt (lowCoarseS27_hz46 hx hc).2 (by norm_num), ?_, ?_, (lowCoarseS27_hz106 hx hc).2.trans (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (lowCoarseS27_hz38 hx hc).1) (lowCoarseS27_hz38 hx hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) (lowCoarseS27_hz6 hx hc).1 2
    nlinarith only [h1,h2]
  · linarith only [(lowCoarseS27_hz55 hx hc).1,(lowCoarseS27_hz64 hx hc).2]
  · have hap : 0 < nap x := lt_of_lt_of_le (by norm_num) (lowCoarseS27_hz6 hx hc).1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul (lowCoarseS27_hz68 hx hc).2 (lowCoarseS27_hz6 hx hc).2 (le_trans (by norm_num) (lowCoarseS27_hz6 hx hc).1) (by norm_num)
    linarith only [h,(lowCoarseS27_hz55 hx hc).1,(lowCoarseS27_hz64 hx hc).2]

theorem lowCoarseS28_hz0 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B 0 (1 / 8000) x := hx

theorem lowCoarseS28_hz1 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B (29 / 50) (59 / 100) c := hc

theorem lowCoarseS28_hz2 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B (6782329983125268139 / 500000000000000000) (13564659966250536279 / 1000000000000000000) (√(184 : ℝ)) := bsqrt (bpoint (184 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS28_hz3 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS28_hz4 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B 0 (847791247890659 / 500000000000000000) ((√(184 : ℝ)) * x) := bmul (lowCoarseS28_hz2 hx hc) (lowCoarseS28_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS28_hz5 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B 1 (500847791247890659 / 500000000000000000) ((1 : ℝ) + ((√(184 : ℝ)) * x)) := badd (bpoint (1 : ℝ)) (lowCoarseS28_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS28_hz6 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B 1 (500847791247890659 / 500000000000000000) (nap x) := by
    convert (lowCoarseS28_hz5 hx hc) using 1 <;>
      norm_num [nap] <;> ring

theorem lowCoarseS28_hz7 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B 0 (1 / 64000000) (x^2) := bsq (lowCoarseS28_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS28_hz8 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B 0 (1 / 32000000) ((2 : ℝ) * (x^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS28_hz7 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS28_hz9 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B (31999999 / 32000000) 1 ((1 : ℝ) - ((2 : ℝ) * (x^2))) := bsub (bpoint (1 : ℝ)) (lowCoarseS28_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS28_hz10 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B (999999984374999877 / 1000000000000000000) 1 (√((1 : ℝ) - ((2 : ℝ) * (x^2)))) := bsqrt (lowCoarseS28_hz9 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS28_hz11 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B (998304401879218559 / 1000000000000000000) 1 ((√((1 : ℝ) - ((2 : ℝ) * (x^2)))) - ((√(184 : ℝ)) * x)) := bsub (lowCoarseS28_hz10 hx hc) (lowCoarseS28_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS28_hz12 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B (998304401879218559 / 1000000000000000000) 1 (nam x) := by
    convert (lowCoarseS28_hz11 hx hc) using 1 <;>
      norm_num [nam] <;> ring

theorem lowCoarseS28_hz13 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B (2722451012134883 / 3906250000000000) (696947459106530257 / 1000000000000000000) (kdot ((29 / 50))) := by
    constructor
    · apply bkdot_lower (q := (515580046947248127 / 1000000000000000000)) (a := (238016909030661399 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (257790023473624063 / 500000000000000000)) (a := (47603381806132247 / 100000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS28_hz14 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B (841 / 2500) (841 / 2500) (((29 / 50) : ℝ)^2) := bsq (bpoint ((29 / 50) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS28_hz15 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B (1659 / 2500) (1659 / 2500) ((1 : ℝ) - (((29 / 50) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS28_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS28_hz16 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B (20365411854416301 / 25000000000000000) (814616474176652041 / 1000000000000000000) (√((1 : ℝ) - (((29 / 50) : ℝ)^2))) := bsqrt (lowCoarseS28_hz15 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS28_hz17 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B (259300477178610963 / 1000000000000000000) (64825119294652741 / 250000000000000000) ((√((1 : ℝ) - (((29 / 50) : ℝ)^2))) / Real.pi) := bdiv (lowCoarseS28_hz16 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS28_hz18 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B (404229526281787427 / 1000000000000000000) (8084590525635751 / 20000000000000000) (((29 / 50) : ℝ) * (kdot ((29 / 50)))) := bmul (bpoint ((29 / 50) : ℝ)) (lowCoarseS28_hz13 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS28_hz19 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B (66353000346039839 / 100000000000000000) (331765001730199257 / 500000000000000000) (((√((1 : ℝ) - (((29 / 50) : ℝ)^2))) / Real.pi) + (((29 / 50) : ℝ) * (kdot ((29 / 50))))) := badd (lowCoarseS28_hz17 hx hc) (lowCoarseS28_hz18 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS28_hz20 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B (66353000346039839 / 100000000000000000) (331765001730199257 / 500000000000000000) (kappa ((29 / 50))) := by rw [kappa_eq]; exact (lowCoarseS28_hz19 hx hc)

theorem lowCoarseS28_hz21 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B (350436133891663427 / 500000000000000000) (140174453556665391 / 200000000000000000) (kdot ((59 / 100))) := by
    constructor
    · apply bkdot_lower (q := (253900391502320151 / 500000000000000000)) (a := (117467185752109409 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (507800783004640301 / 1000000000000000000)) (a := (469868743008437479 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS28_hz22 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B (3481 / 10000) (3481 / 10000) (((59 / 100) : ℝ)^2) := bsq (bpoint ((59 / 100) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS28_hz23 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B (6519 / 10000) (6519 / 10000) ((1 : ℝ) - (((59 / 100) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS28_hz22 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS28_hz24 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B (403701622488689039 / 500000000000000000) (807403244977378079 / 1000000000000000000) (√((1 : ℝ) - (((59 / 100) : ℝ)^2))) := bsqrt (lowCoarseS28_hz23 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS28_hz25 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B (257004435013172473 / 1000000000000000000) (128502217506586237 / 500000000000000000) ((√((1 : ℝ) - (((59 / 100) : ℝ)^2))) / Real.pi) := bdiv (lowCoarseS28_hz24 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS28_hz26 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B (413514637992162843 / 1000000000000000000) (51689329749020363 / 125000000000000000) (((59 / 100) : ℝ) * (kdot ((59 / 100)))) := bmul (bpoint ((59 / 100) : ℝ)) (lowCoarseS28_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS28_hz27 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B (167629768251333829 / 250000000000000000) (335259536502667689 / 500000000000000000) (((√((1 : ℝ) - (((59 / 100) : ℝ)^2))) / Real.pi) + (((59 / 100) : ℝ) * (kdot ((59 / 100))))) := badd (lowCoarseS28_hz25 hx hc) (lowCoarseS28_hz26 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS28_hz28 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B (167629768251333829 / 250000000000000000) (335259536502667689 / 500000000000000000) (kappa ((59 / 100))) := by rw [kappa_eq]; exact (lowCoarseS28_hz27 hx hc)

theorem lowCoarseS28_hz29 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B (66353000346039839 / 100000000000000000) (335259536502667689 / 500000000000000000) (kappa c) := bkappa (lowCoarseS28_hz1 hx hc) (by norm_num) (by norm_num) (lowCoarseS28_hz20 hx hc).1 (lowCoarseS28_hz28 hx hc).2

theorem lowCoarseS28_hz30 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B (164740463497332311 / 500000000000000000) (33646999653960161 / 100000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (lowCoarseS28_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS28_hz31 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B (164740463497332311 / 250000000000000000) (33646999653960161 / 50000000000000000) ((2 : ℝ) * ((1 : ℝ) - (kappa c))) := bmul (bpoint (2 : ℝ)) (lowCoarseS28_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS28_hz32 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B 0 (1 / 8000000) ((8 : ℝ) * (x^2)) := bmul (bpoint (8 : ℝ)) (lowCoarseS28_hz7 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS28_hz33 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B (164740432247332311 / 250000000000000000) (33646999653960161 / 50000000000000000) (((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2))) := bsub (lowCoarseS28_hz31 hx hc) (lowCoarseS28_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS28_hz34 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B (811764577318651693 / 1000000000000000000) (205082299498153183 / 250000000000000000) (√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) := bsqrt (lowCoarseS28_hz33 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS28_hz35 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B (6782329983125268139 / 250000000000000000) (13564659966250536279 / 500000000000000000) ((2 : ℝ) * (√(184 : ℝ))) := bmul (bpoint (2 : ℝ)) (lowCoarseS28_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS28_hz36 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B 0 (678232998312527 / 200000000000000000) (((2 : ℝ) * (√(184 : ℝ))) * x) := bmul (lowCoarseS28_hz35 hx hc) (lowCoarseS28_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS28_hz37 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B (404186706163544529 / 500000000000000000) (205082299498153183 / 250000000000000000) ((√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) - (((2 : ℝ) * (√(184 : ℝ))) * x)) := bsub (lowCoarseS28_hz34 hx hc) (lowCoarseS28_hz36 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS28_hz38 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B (404186706163544529 / 500000000000000000) (205082299498153183 / 250000000000000000) (ndm x c) := by
    convert (lowCoarseS28_hz37 hx hc) using 1 <;>
      norm_num [ndm] <;> ring

theorem lowCoarseS28_hz39 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B 1 (1003394039991562637 / 1000000000000000000) ((nap x)^2) := bsq (lowCoarseS28_hz6 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS28_hz40 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B 2 (1003394039991562637 / 500000000000000000) ((2 : ℝ) * ((nap x)^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS28_hz39 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS28_hz41 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B (653467573757341939 / 1000000000000000000) (672939993079203221 / 1000000000000000000) ((ndm x c)^2) := bsq (lowCoarseS28_hz38 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS28_hz42 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B (1327060006920796779 / 1000000000000000000) (270664101245156667 / 200000000000000000) (((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) := bsub (lowCoarseS28_hz40 hx hc) (lowCoarseS28_hz41 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS28_hz43 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B (199322335762284863 / 200000000000000000) 1 ((nam x)^2) := bsq (lowCoarseS28_hz12 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS28_hz44 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B (199322335762284863 / 100000000000000000) 2 ((2 : ℝ) * ((nam x)^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS28_hz43 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS28_hz45 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B (663530003460398389 / 1000000000000000000) (339480395172514913 / 500000000000000000) ((((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) / ((2 : ℝ) * ((nam x)^2))) := bdiv (lowCoarseS28_hz42 hx hc) (lowCoarseS28_hz44 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS28_hz46 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B (663530003460398389 / 1000000000000000000) (339480395172514913 / 500000000000000000) (nc1 x c) := by
    convert (lowCoarseS28_hz45 hx hc) using 1 <;>
      norm_num [nc1] <;> ring

theorem lowCoarseS28_hz47 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B (2722451012134883 / 3906250000000000) (140174453556665391 / 200000000000000000) (kdot c) := bkdot (lowCoarseS28_hz1 hx hc) (lowCoarseS28_hz13 hx hc).1 (lowCoarseS28_hz21 hx hc).2

theorem lowCoarseS28_hz48 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B (730942499207920659 / 1000000000000000000) (730942499207920661 / 1000000000000000000) (kdot ((663530003460398389 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (449736206928097447 / 1000000000000000000)) (a := (13207329185650413 / 31250000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (224868103464048723 / 500000000000000000)) (a := (211317266970406607 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS28_hz49 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B (737569382292561553 / 1000000000000000000) (184392345573140389 / 250000000000000000) (kdot ((339480395172514913 / 500000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (27329946350021567 / 62500000000000000)) (a := (82445010066672013 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (437279141600345071 / 1000000000000000000)) (a := (412225050333360063 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS28_hz50 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B (730942499207920659 / 1000000000000000000) (184392345573140389 / 250000000000000000) (kdot (nc1 x c)) := bkdot (lowCoarseS28_hz46 hx hc) (lowCoarseS28_hz48 hx hc).1 (lowCoarseS28_hz49 hx hc).2

theorem lowCoarseS28_hz51 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B (841 / 2500) (3481 / 10000) (c^2) := bsq (lowCoarseS28_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS28_hz52 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B (6519 / 10000) (1659 / 2500) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS28_hz51 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS28_hz53 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B (403701622488689039 / 500000000000000000) (814616474176652041 / 1000000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (lowCoarseS28_hz52 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS28_hz54 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B (56271764006135087 / 100000000000000000) (570942095629848117 / 1000000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (lowCoarseS28_hz53 hx hc) (lowCoarseS28_hz47 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS28_hz55 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B (56271764006135087 / 100000000000000000) (570942095629848117 / 1000000000000000000) (npa c) := by
    convert (lowCoarseS28_hz54 hx hc) using 1 <;>
      norm_num [npa] <;> ring

theorem lowCoarseS28_hz56 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B (257004435013172473 / 1000000000000000000) (64825119294652741 / 250000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (lowCoarseS28_hz53 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS28_hz57 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B (404229526281787427 / 1000000000000000000) (51689329749020363 / 125000000000000000) (c * (kdot c)) := bmul (lowCoarseS28_hz1 hx hc) (lowCoarseS28_hz47 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS28_hz58 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B (-156510202978990431 / 1000000000000000000) (-144929049103176463 / 1000000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (lowCoarseS28_hz56 hx hc) (lowCoarseS28_hz57 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS28_hz59 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B (-156510202978990431 / 1000000000000000000) (-144929049103176463 / 1000000000000000000) (npp c) := by
    convert (lowCoarseS28_hz58 hx hc) using 1 <;>
      norm_num [npp] <;> ring

theorem lowCoarseS28_hz60 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B 0 (23 / 4000) ((46 : ℝ) * x) := bmul (bpoint (46 : ℝ)) (lowCoarseS28_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS28_hz61 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B (9591663046625439083 / 1000000000000000000) (2399353261656359771 / 250000000000000000) ((√(92 : ℝ)) + ((46 : ℝ) * x)) := badd (lowCoarseS28_hz3 hx hc) (lowCoarseS28_hz60 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS28_hz62 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B (28774989139876317249 / 250000000000000000) (7198059784969079313 / 62500000000000000) ((12 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (bpoint (12 : ℝ)) (lowCoarseS28_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS28_hz63 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B 0 (14396119569938159 / 1000000000000000000) (((12 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS28_hz62 hx hc) (lowCoarseS28_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS28_hz64 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B 0 (14396119569938159 / 1000000000000000000) (nr1 x) := by
    convert (lowCoarseS28_hz63 hx hc) using 1 <;>
      norm_num [nr1] <;> ring

theorem lowCoarseS28_hz65 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B (9591663046625439083 / 125000000000000000) (2399353261656359771 / 31250000000000000) ((8 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (bpoint (8 : ℝ)) (lowCoarseS28_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS28_hz66 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B 0 (59983831541409 / 6250000000000000) (((8 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS28_hz65 hx hc) (lowCoarseS28_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS28_hz67 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B 0 (59983831541409 / 6250000000000000) (nrpp x) := by
    convert (lowCoarseS28_hz66 hx hc) using 1 <;>
      norm_num [nrpp] <;> ring

theorem lowCoarseS28_hz68 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B 0 (847791247890659 / 500000000000000000) (ne0 x) := by
    convert (lowCoarseS28_hz4 hx hc) using 1 <;>
      norm_num [ne0] <;> ring

theorem lowCoarseS28_hz69 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B (56271764006135087 / 100000000000000000) (146334553799946569 / 250000000000000000) ((npa c) + (nr1 x)) := badd (lowCoarseS28_hz55 hx hc) (lowCoarseS28_hz64 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS28_hz70 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B (56271764006135087 / 100000000000000000) (18322887478569273 / 31250000000000000) (((npa c) + (nr1 x)) / (nam x)) := bdiv (lowCoarseS28_hz69 hx hc) (lowCoarseS28_hz12 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS28_hz71 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B (56271764006135087 / 100000000000000000) (294013990904999027 / 500000000000000000) ((((npa c) + (nr1 x)) / (nam x)) + (ne0 x)) := badd (lowCoarseS28_hz70 hx hc) (lowCoarseS28_hz68 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS28_hz72 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B (56271764006135087 / 100000000000000000) (294013990904999027 / 500000000000000000) (nlam x c) := by
    convert (lowCoarseS28_hz71 hx hc) using 1 <;>
      norm_num [nlam] <;> ring

theorem lowCoarseS28_hz73 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS28_hz74 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B 0 (59947894041409 / 100000000000000000) ((√(23 : ℝ)) * x) := bmul (lowCoarseS28_hz73 hx hc) (lowCoarseS28_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS28_hz75 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B (1 / 2) (50059947894041409 / 100000000000000000) (((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)) := badd (bpoint ((1 / 2) : ℝ)) (lowCoarseS28_hz74 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS28_hz76 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B (176776695296636881 / 250000000000000000) (353765274914177413 / 500000000000000000) (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) := bsqrt (lowCoarseS28_hz75 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS28_hz77 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B 0 (59947894041409 / 50000000000000000) ((√(92 : ℝ)) * x) := bmul (lowCoarseS28_hz3 hx hc) (lowCoarseS28_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS28_hz78 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B (176776695296636881 / 250000000000000000) (354364753854591503 / 500000000000000000) ((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x)) := badd (lowCoarseS28_hz76 hx hc) (lowCoarseS28_hz77 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS28_hz79 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B (499999999999999999 / 1000000000000000000) (251148757548850447 / 500000000000000000) (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2) := bsq (lowCoarseS28_hz78 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS28_hz80 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B (499999999999999999 / 125000000000000000) (251148757548850447 / 62500000000000000) ((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) := bmul (bpoint (8 : ℝ)) (lowCoarseS28_hz79 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS28_hz81 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B (7673330437300351251 / 200000000000000000) (1928302689874485209 / 50000000000000000) (((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (lowCoarseS28_hz80 hx hc) (lowCoarseS28_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS28_hz82 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B 0 (2410378362343107 / 500000000000000000) ((((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS28_hz81 hx hc) (lowCoarseS28_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS28_hz83 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B 0 (2410378362343107 / 500000000000000000) (nrs x) := by
    convert (lowCoarseS28_hz82 hx hc) using 1 <;>
      norm_num [nrs] <;> ring

theorem lowCoarseS28_hz84 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B (-156510202978990431 / 1000000000000000000) (-135331636056551023 / 1000000000000000000) ((npp c) + (nrpp x)) := badd (lowCoarseS28_hz59 hx hc) (lowCoarseS28_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS28_hz85 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B (-577185668668487 / 5000000000000000) (-67665818028275511 / 1000000000000000000) (if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) := bweaken (bfirst (lowCoarseS28_hz84 hx hc) (lowCoarseS28_hz50 hx hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem lowCoarseS28_hz86 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B (316651142436216033 / 1000000000000000000) (345776907391539403 / 1000000000000000000) ((nlam x c)^2) := bsq (lowCoarseS28_hz72 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS28_hz87 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B (220136032746078149 / 500000000000000000) (460987754825947547 / 1000000000000000000) ((nc1 x c)^2) := bsq (lowCoarseS28_hz46 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS28_hz88 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B (539012245174052453 / 1000000000000000000) (279863967253921851 / 500000000000000000) ((1 : ℝ) - ((nc1 x c)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS28_hz87 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS28_hz89 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B (73417453318271157 / 100000000000000000) (93518709233420549 / 125000000000000000) (√((1 : ℝ) - ((nc1 x c)^2))) := bsqrt (lowCoarseS28_hz88 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS28_hz90 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B (46129546397990451 / 20000000000000000) (235038151920731169 / 100000000000000000) (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))) := bmul pi_mem (lowCoarseS28_hz89 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS28_hz91 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B (4210102964249417 / 31250000000000000) (149915589634587233 / 1000000000000000000) (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2))))) := bdiv (lowCoarseS28_hz86 hx hc) (lowCoarseS28_hz90 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS28_hz92 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B (2410770140285493 / 125000000000000000) (41124885803155861 / 500000000000000000) ((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) := badd (lowCoarseS28_hz85 hx hc) (lowCoarseS28_hz91 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS28_hz93 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B 0 (2875000000001 / 1000000000000000000) ((ne0 x)^2) := bsq (lowCoarseS28_hz68 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS28_hz94 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B (2410770140285493 / 125000000000000000) (82252646606311723 / 1000000000000000000) (((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) + ((ne0 x)^2)) := badd (lowCoarseS28_hz92 hx hc) (lowCoarseS28_hz93 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS28_hz95 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B (2410770140285493 / 125000000000000000) (87073403330997937 / 1000000000000000000) ((((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) + ((ne0 x)^2)) + (nrs x)) := badd (lowCoarseS28_hz94 hx hc) (lowCoarseS28_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS28_hz96 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B (2410770140285493 / 125000000000000000) (87073403330997937 / 1000000000000000000) (nu x c) := by
    convert (lowCoarseS28_hz95 hx hc) using 1 <;>
      norm_num [nu] <;> ring

theorem lowCoarseS28_hz97 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B (-166107616025615871 / 1000000000000000000) (-144929049103176463 / 1000000000000000000) ((npp c) - (nrpp x)) := bsub (lowCoarseS28_hz59 hx hc) (lowCoarseS28_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS28_hz98 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B (-166107616025615871 / 1000000000000000000) (-144929049103176463 / 1000000000000000000) (min ((npp c) - (nrpp x)) (0 : ℝ)) := bweaken (bmin (lowCoarseS28_hz97 hx hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem lowCoarseS28_hz99 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B (-122515891746103497 / 1000000000000000000) (-13241850169912907 / 125000000000000000) ((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) := bmul (lowCoarseS28_hz50 hx hc) (lowCoarseS28_hz98 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS28_hz100 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B (-61259383373051749 / 500000000000000000) (-13241850169912907 / 125000000000000000) (((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) - ((ne0 x)^2)) := bsub (lowCoarseS28_hz99 hx hc) (lowCoarseS28_hz93 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS28_hz101 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B (-7958720216924357 / 62500000000000000) (-13241850169912907 / 125000000000000000) ((((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) - ((ne0 x)^2)) - (nrs x)) := bsub (lowCoarseS28_hz100 hx hc) (lowCoarseS28_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS28_hz102 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B (-7958720216924357 / 62500000000000000) (-13241850169912907 / 125000000000000000) (nl x c) := by
    convert (lowCoarseS28_hz101 hx hc) using 1 <;>
      norm_num [nl] <;> ring

theorem lowCoarseS28_hz103 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B 0 (87073403330997937 / 1000000000000000000) |(nu x c)| := bweaken (babs (lowCoarseS28_hz96 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS28_hz104 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B 0 (7958720216924357 / 62500000000000000) |(nl x c)| := bweaken (babs (lowCoarseS28_hz102 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS28_hz105 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B 0 (7958720216924357 / 62500000000000000) (max |(nu x c)| |(nl x c)|) := bweaken (bmax (lowCoarseS28_hz103 hx hc) (lowCoarseS28_hz104 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS28_hz106 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) : B 0 (7958720216924357 / 62500000000000000) (ns x c) := by
    convert (lowCoarseS28_hz105 hx hc) using 1 <;>
      norm_num [ns] <;> ring

theorem lowCoarseS28 {x c : ℝ}
    (hx : B 0 (1/8000) x) (hc : B (29 / 50) (59 / 100) c) :
    0 < nam x ∧ 0 ≤ ndm x c ∧ ndm x c ^ 2 ≤ 2 * nap x ^ 2 ∧ nc1 x c < 1 ∧
    0 ≤ npa c - nr1 x ∧ ne0 x ≤ (npa c - nr1 x) / nap x ∧ ns x c ≤ (1 / 5) := by
  refine ⟨lt_of_lt_of_le (by norm_num) (lowCoarseS28_hz12 hx hc).1,
    le_trans (by norm_num) (lowCoarseS28_hz38 hx hc).1, ?_,
    lt_of_le_of_lt (lowCoarseS28_hz46 hx hc).2 (by norm_num), ?_, ?_, (lowCoarseS28_hz106 hx hc).2.trans (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (lowCoarseS28_hz38 hx hc).1) (lowCoarseS28_hz38 hx hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) (lowCoarseS28_hz6 hx hc).1 2
    nlinarith only [h1,h2]
  · linarith only [(lowCoarseS28_hz55 hx hc).1,(lowCoarseS28_hz64 hx hc).2]
  · have hap : 0 < nap x := lt_of_lt_of_le (by norm_num) (lowCoarseS28_hz6 hx hc).1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul (lowCoarseS28_hz68 hx hc).2 (lowCoarseS28_hz6 hx hc).2 (le_trans (by norm_num) (lowCoarseS28_hz6 hx hc).1) (by norm_num)
    linarith only [h,(lowCoarseS28_hz55 hx hc).1,(lowCoarseS28_hz64 hx hc).2]

theorem lowCoarseS29_hz0 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B 0 (1 / 8000) x := hx

theorem lowCoarseS29_hz1 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B (59 / 100) (3 / 5) c := hc

theorem lowCoarseS29_hz2 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B (6782329983125268139 / 500000000000000000) (13564659966250536279 / 1000000000000000000) (√(184 : ℝ)) := bsqrt (bpoint (184 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS29_hz3 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS29_hz4 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B 0 (847791247890659 / 500000000000000000) ((√(184 : ℝ)) * x) := bmul (lowCoarseS29_hz2 hx hc) (lowCoarseS29_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS29_hz5 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B 1 (500847791247890659 / 500000000000000000) ((1 : ℝ) + ((√(184 : ℝ)) * x)) := badd (bpoint (1 : ℝ)) (lowCoarseS29_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS29_hz6 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B 1 (500847791247890659 / 500000000000000000) (nap x) := by
    convert (lowCoarseS29_hz5 hx hc) using 1 <;>
      norm_num [nap] <;> ring

theorem lowCoarseS29_hz7 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B 0 (1 / 64000000) (x^2) := bsq (lowCoarseS29_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS29_hz8 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B 0 (1 / 32000000) ((2 : ℝ) * (x^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS29_hz7 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS29_hz9 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B (31999999 / 32000000) 1 ((1 : ℝ) - ((2 : ℝ) * (x^2))) := bsub (bpoint (1 : ℝ)) (lowCoarseS29_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS29_hz10 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B (999999984374999877 / 1000000000000000000) 1 (√((1 : ℝ) - ((2 : ℝ) * (x^2)))) := bsqrt (lowCoarseS29_hz9 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS29_hz11 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B (998304401879218559 / 1000000000000000000) 1 ((√((1 : ℝ) - ((2 : ℝ) * (x^2)))) - ((√(184 : ℝ)) * x)) := bsub (lowCoarseS29_hz10 hx hc) (lowCoarseS29_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS29_hz12 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B (998304401879218559 / 1000000000000000000) 1 (nam x) := by
    convert (lowCoarseS29_hz11 hx hc) using 1 <;>
      norm_num [nam] <;> ring

theorem lowCoarseS29_hz13 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B (350436133891663427 / 500000000000000000) (140174453556665391 / 200000000000000000) (kdot ((59 / 100))) := by
    constructor
    · apply bkdot_lower (q := (253900391502320151 / 500000000000000000)) (a := (117467185752109409 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (507800783004640301 / 1000000000000000000)) (a := (469868743008437479 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS29_hz14 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B (3481 / 10000) (3481 / 10000) (((59 / 100) : ℝ)^2) := bsq (bpoint ((59 / 100) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS29_hz15 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B (6519 / 10000) (6519 / 10000) ((1 : ℝ) - (((59 / 100) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS29_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS29_hz16 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B (403701622488689039 / 500000000000000000) (807403244977378079 / 1000000000000000000) (√((1 : ℝ) - (((59 / 100) : ℝ)^2))) := bsqrt (lowCoarseS29_hz15 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS29_hz17 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B (257004435013172473 / 1000000000000000000) (128502217506586237 / 500000000000000000) ((√((1 : ℝ) - (((59 / 100) : ℝ)^2))) / Real.pi) := bdiv (lowCoarseS29_hz16 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS29_hz18 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B (413514637992162843 / 1000000000000000000) (51689329749020363 / 125000000000000000) (((59 / 100) : ℝ) * (kdot ((59 / 100)))) := bmul (bpoint ((59 / 100) : ℝ)) (lowCoarseS29_hz13 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS29_hz19 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B (167629768251333829 / 250000000000000000) (335259536502667689 / 500000000000000000) (((√((1 : ℝ) - (((59 / 100) : ℝ)^2))) / Real.pi) + (((59 / 100) : ℝ) * (kdot ((59 / 100))))) := badd (lowCoarseS29_hz17 hx hc) (lowCoarseS29_hz18 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS29_hz20 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B (167629768251333829 / 250000000000000000) (335259536502667689 / 500000000000000000) (kappa ((59 / 100))) := by rw [kappa_eq]; exact (lowCoarseS29_hz19 hx hc)

theorem lowCoarseS29_hz21 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B (352416382349566723 / 500000000000000000) (352416382349566747 / 500000000000000000) (kdot ((3 / 5))) := by
    constructor
    · apply bkdot_lower (q := (1 / 2)) (a := (115911902250201531 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (1 / 2)) (a := (9272952180016121 / 20000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS29_hz22 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B (9 / 25) (9 / 25) (((3 / 5) : ℝ)^2) := bsq (bpoint ((3 / 5) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS29_hz23 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B (16 / 25) (16 / 25) ((1 : ℝ) - (((3 / 5) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS29_hz22 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS29_hz24 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B (4 / 5) (4 / 5) (√((1 : ℝ) - (((3 / 5) : ℝ)^2))) := bsqrt (lowCoarseS29_hz23 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS29_hz25 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B (254647908947032537 / 1000000000000000000) (127323954473516269 / 500000000000000000) ((√((1 : ℝ) - (((3 / 5) : ℝ)^2))) / Real.pi) := bdiv (lowCoarseS29_hz24 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS29_hz26 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B (422899658819480067 / 1000000000000000000) (422899658819480097 / 1000000000000000000) (((3 / 5) : ℝ) * (kdot ((3 / 5)))) := bmul (bpoint ((3 / 5) : ℝ)) (lowCoarseS29_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS29_hz27 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B (169386891941628151 / 250000000000000000) (135509513553302527 / 200000000000000000) (((√((1 : ℝ) - (((3 / 5) : ℝ)^2))) / Real.pi) + (((3 / 5) : ℝ) * (kdot ((3 / 5))))) := badd (lowCoarseS29_hz25 hx hc) (lowCoarseS29_hz26 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS29_hz28 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B (169386891941628151 / 250000000000000000) (135509513553302527 / 200000000000000000) (kappa ((3 / 5))) := by rw [kappa_eq]; exact (lowCoarseS29_hz27 hx hc)

theorem lowCoarseS29_hz29 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B (167629768251333829 / 250000000000000000) (135509513553302527 / 200000000000000000) (kappa c) := bkappa (lowCoarseS29_hz1 hx hc) (by norm_num) (by norm_num) (lowCoarseS29_hz20 hx hc).1 (lowCoarseS29_hz28 hx hc).2

theorem lowCoarseS29_hz30 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B (64490486446697473 / 200000000000000000) (82370231748666171 / 250000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (lowCoarseS29_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS29_hz31 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B (64490486446697473 / 100000000000000000) (82370231748666171 / 125000000000000000) ((2 : ℝ) * ((1 : ℝ) - (kappa c))) := bmul (bpoint (2 : ℝ)) (lowCoarseS29_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS29_hz32 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B 0 (1 / 8000000) ((8 : ℝ) * (x^2)) := bmul (bpoint (8 : ℝ)) (lowCoarseS29_hz7 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS29_hz33 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B (64490473946697473 / 100000000000000000) (82370231748666171 / 125000000000000000) (((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2))) := bsub (lowCoarseS29_hz31 hx hc) (lowCoarseS29_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS29_hz34 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B (401529805701573893 / 500000000000000000) (50735290894463371 / 62500000000000000) (√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) := bsqrt (lowCoarseS29_hz33 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS29_hz35 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B (6782329983125268139 / 250000000000000000) (13564659966250536279 / 500000000000000000) ((2 : ℝ) * (√(184 : ℝ))) := bmul (bpoint (2 : ℝ)) (lowCoarseS29_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS29_hz36 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B 0 (678232998312527 / 200000000000000000) (((2 : ℝ) * (√(184 : ℝ))) * x) := bmul (lowCoarseS29_hz35 hx hc) (lowCoarseS29_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS29_hz37 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B (799668446411585151 / 1000000000000000000) (50735290894463371 / 62500000000000000) ((√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) - (((2 : ℝ) * (√(184 : ℝ))) * x)) := bsub (lowCoarseS29_hz34 hx hc) (lowCoarseS29_hz36 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS29_hz38 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B (799668446411585151 / 1000000000000000000) (50735290894463371 / 62500000000000000) (ndm x c) := by
    convert (lowCoarseS29_hz37 hx hc) using 1 <;>
      norm_num [ndm] <;> ring

theorem lowCoarseS29_hz39 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B 1 (1003394039991562637 / 1000000000000000000) ((nap x)^2) := bsq (lowCoarseS29_hz6 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS29_hz40 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B 2 (1003394039991562637 / 500000000000000000) ((2 : ℝ) * ((nap x)^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS29_hz39 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS29_hz41 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B (79933703023289779 / 125000000000000000) (658961853989329369 / 1000000000000000000) ((ndm x c)^2) := bsq (lowCoarseS29_hz38 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS29_hz42 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B (1341038146010670631 / 1000000000000000000) (683659227898403521 / 500000000000000000) (((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) := bsub (lowCoarseS29_hz40 hx hc) (lowCoarseS29_hz41 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS29_hz43 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B (199322335762284863 / 200000000000000000) 1 ((nam x)^2) := bsq (lowCoarseS29_hz12 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS29_hz44 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B (199322335762284863 / 100000000000000000) 2 ((2 : ℝ) * ((nam x)^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS29_hz43 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS29_hz45 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B (134103814601067063 / 200000000000000000) (342991780265783611 / 500000000000000000) ((((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) / ((2 : ℝ) * ((nam x)^2))) := bdiv (lowCoarseS29_hz42 hx hc) (lowCoarseS29_hz44 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS29_hz46 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B (134103814601067063 / 200000000000000000) (342991780265783611 / 500000000000000000) (nc1 x c) := by
    convert (lowCoarseS29_hz45 hx hc) using 1 <;>
      norm_num [nc1] <;> ring

theorem lowCoarseS29_hz47 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B (350436133891663427 / 500000000000000000) (352416382349566747 / 500000000000000000) (kdot c) := bkdot (lowCoarseS29_hz1 hx hc) (lowCoarseS29_hz13 hx hc).1 (lowCoarseS29_hz21 hx hc).2

theorem lowCoarseS29_hz48 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B (366964277094220169 / 500000000000000000) (733928554188440341 / 1000000000000000000) (kdot ((134103814601067063 / 200000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (11102721062251427 / 25000000000000000)) (a := (417944049745805297 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (444108842490057079 / 1000000000000000000)) (a := (83588809949161059 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS29_hz49 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B (740627821025054627 / 1000000000000000000) (740627821025054629 / 1000000000000000000) (kdot ((342991780265783611 / 500000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (431568287799015391 / 1000000000000000000)) (a := (203710433003316353 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (43156828779901539 / 100000000000000000)) (a := (1591487757838409 / 3906250000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS29_hz50 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B (366964277094220169 / 500000000000000000) (740627821025054629 / 1000000000000000000) (kdot (nc1 x c)) := bkdot (lowCoarseS29_hz46 hx hc) (lowCoarseS29_hz48 hx hc).1 (lowCoarseS29_hz49 hx hc).2

theorem lowCoarseS29_hz51 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B (3481 / 10000) (9 / 25) (c^2) := bsq (lowCoarseS29_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS29_hz52 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B (16 / 25) (6519 / 10000) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS29_hz51 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS29_hz53 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B (4 / 5) (807403244977378079 / 1000000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (lowCoarseS29_hz52 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS29_hz54 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B (560697814226661483 / 1000000000000000000) (569084261384457161 / 1000000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (lowCoarseS29_hz53 hx hc) (lowCoarseS29_hz47 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS29_hz55 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B (560697814226661483 / 1000000000000000000) (569084261384457161 / 1000000000000000000) (npa c) := by
    convert (lowCoarseS29_hz54 hx hc) using 1 <;>
      norm_num [npa] <;> ring

theorem lowCoarseS29_hz56 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B (254647908947032537 / 1000000000000000000) (128502217506586237 / 500000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (lowCoarseS29_hz53 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS29_hz57 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B (413514637992162843 / 1000000000000000000) (422899658819480097 / 1000000000000000000) (c * (kdot c)) := bmul (lowCoarseS29_hz1 hx hc) (lowCoarseS29_hz47 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS29_hz58 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B (-4206293746811189 / 25000000000000000) (-156510202978990369 / 1000000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (lowCoarseS29_hz56 hx hc) (lowCoarseS29_hz57 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS29_hz59 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B (-4206293746811189 / 25000000000000000) (-156510202978990369 / 1000000000000000000) (npp c) := by
    convert (lowCoarseS29_hz58 hx hc) using 1 <;>
      norm_num [npp] <;> ring

theorem lowCoarseS29_hz60 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B 0 (23 / 4000) ((46 : ℝ) * x) := bmul (bpoint (46 : ℝ)) (lowCoarseS29_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS29_hz61 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B (9591663046625439083 / 1000000000000000000) (2399353261656359771 / 250000000000000000) ((√(92 : ℝ)) + ((46 : ℝ) * x)) := badd (lowCoarseS29_hz3 hx hc) (lowCoarseS29_hz60 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS29_hz62 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B (28774989139876317249 / 250000000000000000) (7198059784969079313 / 62500000000000000) ((12 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (bpoint (12 : ℝ)) (lowCoarseS29_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS29_hz63 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B 0 (14396119569938159 / 1000000000000000000) (((12 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS29_hz62 hx hc) (lowCoarseS29_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS29_hz64 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B 0 (14396119569938159 / 1000000000000000000) (nr1 x) := by
    convert (lowCoarseS29_hz63 hx hc) using 1 <;>
      norm_num [nr1] <;> ring

theorem lowCoarseS29_hz65 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B (9591663046625439083 / 125000000000000000) (2399353261656359771 / 31250000000000000) ((8 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (bpoint (8 : ℝ)) (lowCoarseS29_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS29_hz66 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B 0 (59983831541409 / 6250000000000000) (((8 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS29_hz65 hx hc) (lowCoarseS29_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS29_hz67 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B 0 (59983831541409 / 6250000000000000) (nrpp x) := by
    convert (lowCoarseS29_hz66 hx hc) using 1 <;>
      norm_num [nrpp] <;> ring

theorem lowCoarseS29_hz68 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B 0 (847791247890659 / 500000000000000000) (ne0 x) := by
    convert (lowCoarseS29_hz4 hx hc) using 1 <;>
      norm_num [ne0] <;> ring

theorem lowCoarseS29_hz69 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B (560697814226661483 / 1000000000000000000) (14587009523859883 / 25000000000000000) ((npa c) + (nr1 x)) := badd (lowCoarseS29_hz55 hx hc) (lowCoarseS29_hz64 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS29_hz70 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B (560697814226661483 / 1000000000000000000) (73058926197265809 / 125000000000000000) (((npa c) + (nr1 x)) / (nam x)) := bdiv (lowCoarseS29_hz69 hx hc) (lowCoarseS29_hz12 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS29_hz71 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B (560697814226661483 / 1000000000000000000) (58616699207390779 / 100000000000000000) ((((npa c) + (nr1 x)) / (nam x)) + (ne0 x)) := badd (lowCoarseS29_hz70 hx hc) (lowCoarseS29_hz68 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS29_hz72 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B (560697814226661483 / 1000000000000000000) (58616699207390779 / 100000000000000000) (nlam x c) := by
    convert (lowCoarseS29_hz71 hx hc) using 1 <;>
      norm_num [nlam] <;> ring

theorem lowCoarseS29_hz73 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS29_hz74 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B 0 (59947894041409 / 100000000000000000) ((√(23 : ℝ)) * x) := bmul (lowCoarseS29_hz73 hx hc) (lowCoarseS29_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS29_hz75 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B (1 / 2) (50059947894041409 / 100000000000000000) (((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)) := badd (bpoint ((1 / 2) : ℝ)) (lowCoarseS29_hz74 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS29_hz76 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B (176776695296636881 / 250000000000000000) (353765274914177413 / 500000000000000000) (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) := bsqrt (lowCoarseS29_hz75 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS29_hz77 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B 0 (59947894041409 / 50000000000000000) ((√(92 : ℝ)) * x) := bmul (lowCoarseS29_hz3 hx hc) (lowCoarseS29_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS29_hz78 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B (176776695296636881 / 250000000000000000) (354364753854591503 / 500000000000000000) ((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x)) := badd (lowCoarseS29_hz76 hx hc) (lowCoarseS29_hz77 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS29_hz79 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B (499999999999999999 / 1000000000000000000) (251148757548850447 / 500000000000000000) (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2) := bsq (lowCoarseS29_hz78 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS29_hz80 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B (499999999999999999 / 125000000000000000) (251148757548850447 / 62500000000000000) ((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) := bmul (bpoint (8 : ℝ)) (lowCoarseS29_hz79 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS29_hz81 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B (7673330437300351251 / 200000000000000000) (1928302689874485209 / 50000000000000000) (((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (lowCoarseS29_hz80 hx hc) (lowCoarseS29_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS29_hz82 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B 0 (2410378362343107 / 500000000000000000) ((((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS29_hz81 hx hc) (lowCoarseS29_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS29_hz83 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B 0 (2410378362343107 / 500000000000000000) (nrs x) := by
    convert (lowCoarseS29_hz82 hx hc) using 1 <;>
      norm_num [nrs] <;> ring

theorem lowCoarseS29_hz84 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B (-4206293746811189 / 25000000000000000) (-146912789932364929 / 1000000000000000000) ((npp c) + (nrpp x)) := badd (lowCoarseS29_hz59 hx hc) (lowCoarseS29_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS29_hz85 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B (-2492238537833667 / 20000000000000000) (-1147756171346601 / 15625000000000000) (if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) := bweaken (bfirst (lowCoarseS29_hz84 hx hc) (lowCoarseS29_hz50 hx hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem lowCoarseS29_hz86 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B (19648877429909737 / 62500000000000000) (171795871298486339 / 500000000000000000) ((nlam x c)^2) := bsq (lowCoarseS29_hz72 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS29_hz87 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B (449595827263934189 / 1000000000000000000) (470573445319566351 / 1000000000000000000) ((nc1 x c)^2) := bsq (lowCoarseS29_hz46 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS29_hz88 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B (529426554680433649 / 1000000000000000000) (550404172736065811 / 1000000000000000000) ((1 : ℝ) - ((nc1 x c)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS29_hz87 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS29_hz89 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B (90952129809487011 / 125000000000000000) (5935138334959701 / 8000000000000000) (√((1 : ℝ) - ((nc1 x c)^2))) := bsqrt (lowCoarseS29_hz88 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS29_hz90 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B (2285876342702637077 / 1000000000000000000) (291340421736696159 / 125000000000000000) (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))) := bmul pi_mem (lowCoarseS29_hz89 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS29_hz91 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B (134886036841586937 / 1000000000000000000) (6012429214622123 / 40000000000000000) (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2))))) := bdiv (lowCoarseS29_hz86 hx hc) (lowCoarseS29_hz90 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS29_hz92 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B (10274109949903587 / 1000000000000000000) (76854335399370611 / 1000000000000000000) ((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) := badd (lowCoarseS29_hz85 hx hc) (lowCoarseS29_hz91 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS29_hz93 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B 0 (2875000000001 / 1000000000000000000) ((ne0 x)^2) := bsq (lowCoarseS29_hz68 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS29_hz94 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B (10274109949903587 / 1000000000000000000) (19214302599842653 / 250000000000000000) (((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) + ((ne0 x)^2)) := badd (lowCoarseS29_hz92 hx hc) (lowCoarseS29_hz93 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS29_hz95 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B (10274109949903587 / 1000000000000000000) (40838983562028413 / 500000000000000000) ((((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) + ((ne0 x)^2)) + (nrs x)) := badd (lowCoarseS29_hz94 hx hc) (lowCoarseS29_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS29_hz96 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B (10274109949903587 / 1000000000000000000) (40838983562028413 / 500000000000000000) (nu x c) := by
    convert (lowCoarseS29_hz95 hx hc) using 1 <;>
      norm_num [nu] <;> ring

theorem lowCoarseS29_hz97 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B (-177849162919073 / 1000000000000000) (-156510202978990369 / 1000000000000000000) ((npp c) - (nrpp x)) := bsub (lowCoarseS29_hz59 hx hc) (lowCoarseS29_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS29_hz98 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B (-177849162919073 / 1000000000000000) (-156510202978990369 / 1000000000000000000) (min ((npp c) - (nrpp x)) (0 : ℝ)) := bweaken (bmin (lowCoarseS29_hz97 hx hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem lowCoarseS29_hz99 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B (-131720038003882981 / 1000000000000000000) (-114867306988109729 / 1000000000000000000) ((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) := bmul (lowCoarseS29_hz50 hx hc) (lowCoarseS29_hz98 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS29_hz100 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B (-65861456501941491 / 500000000000000000) (-114867306988109729 / 1000000000000000000) (((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) - ((ne0 x)^2)) := bsub (lowCoarseS29_hz99 hx hc) (lowCoarseS29_hz93 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS29_hz101 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B (-34135917432142299 / 250000000000000000) (-114867306988109729 / 1000000000000000000) ((((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) - ((ne0 x)^2)) - (nrs x)) := bsub (lowCoarseS29_hz100 hx hc) (lowCoarseS29_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS29_hz102 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B (-34135917432142299 / 250000000000000000) (-114867306988109729 / 1000000000000000000) (nl x c) := by
    convert (lowCoarseS29_hz101 hx hc) using 1 <;>
      norm_num [nl] <;> ring

theorem lowCoarseS29_hz103 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B 0 (40838983562028413 / 500000000000000000) |(nu x c)| := bweaken (babs (lowCoarseS29_hz96 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS29_hz104 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B 0 (34135917432142299 / 250000000000000000) |(nl x c)| := bweaken (babs (lowCoarseS29_hz102 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS29_hz105 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B 0 (34135917432142299 / 250000000000000000) (max |(nu x c)| |(nl x c)|) := bweaken (bmax (lowCoarseS29_hz103 hx hc) (lowCoarseS29_hz104 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS29_hz106 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) : B 0 (34135917432142299 / 250000000000000000) (ns x c) := by
    convert (lowCoarseS29_hz105 hx hc) using 1 <;>
      norm_num [ns] <;> ring

theorem lowCoarseS29 {x c : ℝ}
    (hx : B 0 (1/8000) x) (hc : B (59 / 100) (3 / 5) c) :
    0 < nam x ∧ 0 ≤ ndm x c ∧ ndm x c ^ 2 ≤ 2 * nap x ^ 2 ∧ nc1 x c < 1 ∧
    0 ≤ npa c - nr1 x ∧ ne0 x ≤ (npa c - nr1 x) / nap x ∧ ns x c ≤ (1 / 5) := by
  refine ⟨lt_of_lt_of_le (by norm_num) (lowCoarseS29_hz12 hx hc).1,
    le_trans (by norm_num) (lowCoarseS29_hz38 hx hc).1, ?_,
    lt_of_le_of_lt (lowCoarseS29_hz46 hx hc).2 (by norm_num), ?_, ?_, (lowCoarseS29_hz106 hx hc).2.trans (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (lowCoarseS29_hz38 hx hc).1) (lowCoarseS29_hz38 hx hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) (lowCoarseS29_hz6 hx hc).1 2
    nlinarith only [h1,h2]
  · linarith only [(lowCoarseS29_hz55 hx hc).1,(lowCoarseS29_hz64 hx hc).2]
  · have hap : 0 < nap x := lt_of_lt_of_le (by norm_num) (lowCoarseS29_hz6 hx hc).1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul (lowCoarseS29_hz68 hx hc).2 (lowCoarseS29_hz6 hx hc).2 (le_trans (by norm_num) (lowCoarseS29_hz6 hx hc).1) (by norm_num)
    linarith only [h,(lowCoarseS29_hz55 hx hc).1,(lowCoarseS29_hz64 hx hc).2]

theorem lowCoarseS30_hz0 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B 0 (1 / 8000) x := hx

theorem lowCoarseS30_hz1 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B (3 / 5) (61 / 100) c := hc

theorem lowCoarseS30_hz2 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B (6782329983125268139 / 500000000000000000) (13564659966250536279 / 1000000000000000000) (√(184 : ℝ)) := bsqrt (bpoint (184 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS30_hz3 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS30_hz4 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B 0 (847791247890659 / 500000000000000000) ((√(184 : ℝ)) * x) := bmul (lowCoarseS30_hz2 hx hc) (lowCoarseS30_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS30_hz5 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B 1 (500847791247890659 / 500000000000000000) ((1 : ℝ) + ((√(184 : ℝ)) * x)) := badd (bpoint (1 : ℝ)) (lowCoarseS30_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS30_hz6 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B 1 (500847791247890659 / 500000000000000000) (nap x) := by
    convert (lowCoarseS30_hz5 hx hc) using 1 <;>
      norm_num [nap] <;> ring

theorem lowCoarseS30_hz7 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B 0 (1 / 64000000) (x^2) := bsq (lowCoarseS30_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS30_hz8 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B 0 (1 / 32000000) ((2 : ℝ) * (x^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS30_hz7 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS30_hz9 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B (31999999 / 32000000) 1 ((1 : ℝ) - ((2 : ℝ) * (x^2))) := bsub (bpoint (1 : ℝ)) (lowCoarseS30_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS30_hz10 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B (999999984374999877 / 1000000000000000000) 1 (√((1 : ℝ) - ((2 : ℝ) * (x^2)))) := bsqrt (lowCoarseS30_hz9 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS30_hz11 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B (998304401879218559 / 1000000000000000000) 1 ((√((1 : ℝ) - ((2 : ℝ) * (x^2)))) - ((√(184 : ℝ)) * x)) := bsub (lowCoarseS30_hz10 hx hc) (lowCoarseS30_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS30_hz12 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B (998304401879218559 / 1000000000000000000) 1 (nam x) := by
    convert (lowCoarseS30_hz11 hx hc) using 1 <;>
      norm_num [nam] <;> ring

theorem lowCoarseS30_hz13 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B (352416382349566723 / 500000000000000000) (352416382349566747 / 500000000000000000) (kdot ((3 / 5))) := by
    constructor
    · apply bkdot_lower (q := (1 / 2)) (a := (115911902250201531 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (1 / 2)) (a := (9272952180016121 / 20000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS30_hz14 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B (9 / 25) (9 / 25) (((3 / 5) : ℝ)^2) := bsq (bpoint ((3 / 5) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS30_hz15 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B (16 / 25) (16 / 25) ((1 : ℝ) - (((3 / 5) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS30_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS30_hz16 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B (4 / 5) (4 / 5) (√((1 : ℝ) - (((3 / 5) : ℝ)^2))) := bsqrt (lowCoarseS30_hz15 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS30_hz17 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B (254647908947032537 / 1000000000000000000) (127323954473516269 / 500000000000000000) ((√((1 : ℝ) - (((3 / 5) : ℝ)^2))) / Real.pi) := bdiv (lowCoarseS30_hz16 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS30_hz18 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B (422899658819480067 / 1000000000000000000) (422899658819480097 / 1000000000000000000) (((3 / 5) : ℝ) * (kdot ((3 / 5)))) := bmul (bpoint ((3 / 5) : ℝ)) (lowCoarseS30_hz13 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS30_hz19 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B (169386891941628151 / 250000000000000000) (135509513553302527 / 200000000000000000) (((√((1 : ℝ) - (((3 / 5) : ℝ)^2))) / Real.pi) + (((3 / 5) : ℝ) * (kdot ((3 / 5))))) := badd (lowCoarseS30_hz17 hx hc) (lowCoarseS30_hz18 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS30_hz20 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B (169386891941628151 / 250000000000000000) (135509513553302527 / 200000000000000000) (kappa ((3 / 5))) := by rw [kappa_eq]; exact (lowCoarseS30_hz19 hx hc)

theorem lowCoarseS30_hz21 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B (28353222881079303 / 40000000000000000) (708830572026982599 / 1000000000000000000) (kdot ((61 / 100))) := by
    constructor
    · apply bkdot_lower (q := (492174790948013201 / 1000000000000000000)) (a := (457367867934986991 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (1230436977370033 / 2500000000000000)) (a := (114341966983746739 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS30_hz22 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B (3721 / 10000) (3721 / 10000) (((61 / 100) : ℝ)^2) := bsq (bpoint ((61 / 100) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS30_hz23 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B (6279 / 10000) (6279 / 10000) ((1 : ℝ) - (((61 / 100) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS30_hz22 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS30_hz24 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B (792401413426301253 / 1000000000000000000) (396200706713150627 / 500000000000000000) (√((1 : ℝ) - (((61 / 100) : ℝ)^2))) := bsqrt (lowCoarseS30_hz23 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS30_hz25 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B (252229203719600809 / 1000000000000000000) (25222920371960081 / 100000000000000000) ((√((1 : ℝ) - (((61 / 100) : ℝ)^2))) / Real.pi) := bdiv (lowCoarseS30_hz24 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS30_hz26 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B (43238664893645937 / 100000000000000000) (216193324468229693 / 500000000000000000) (((61 / 100) : ℝ) * (kdot ((61 / 100)))) := bmul (bpoint ((61 / 100) : ℝ)) (lowCoarseS30_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS30_hz27 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B (684615852656060179 / 1000000000000000000) (171153963164015049 / 250000000000000000) (((√((1 : ℝ) - (((61 / 100) : ℝ)^2))) / Real.pi) + (((61 / 100) : ℝ) * (kdot ((61 / 100))))) := badd (lowCoarseS30_hz25 hx hc) (lowCoarseS30_hz26 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS30_hz28 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B (684615852656060179 / 1000000000000000000) (171153963164015049 / 250000000000000000) (kappa ((61 / 100))) := by rw [kappa_eq]; exact (lowCoarseS30_hz27 hx hc)

theorem lowCoarseS30_hz29 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B (169386891941628151 / 250000000000000000) (171153963164015049 / 250000000000000000) (kappa c) := bkappa (lowCoarseS30_hz1 hx hc) (by norm_num) (by norm_num) (lowCoarseS30_hz20 hx hc).1 (lowCoarseS30_hz28 hx hc).2

theorem lowCoarseS30_hz30 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B (78846036835984951 / 250000000000000000) (80613108058371849 / 250000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (lowCoarseS30_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS30_hz31 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B (78846036835984951 / 125000000000000000) (80613108058371849 / 125000000000000000) ((2 : ℝ) * ((1 : ℝ) - (kappa c))) := bmul (bpoint (2 : ℝ)) (lowCoarseS30_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS30_hz32 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B 0 (1 / 8000000) ((8 : ℝ) * (x^2)) := bmul (bpoint (8 : ℝ)) (lowCoarseS30_hz7 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS30_hz33 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B (78846021210984951 / 125000000000000000) (80613108058371849 / 125000000000000000) (((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2))) := bsub (lowCoarseS30_hz31 hx hc) (lowCoarseS30_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS30_hz34 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B (158841829464140787 / 200000000000000000) (200764922307623063 / 250000000000000000) (√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) := bsqrt (lowCoarseS30_hz33 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS30_hz35 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B (6782329983125268139 / 250000000000000000) (13564659966250536279 / 500000000000000000) ((2 : ℝ) * (√(184 : ℝ))) := bmul (bpoint (2 : ℝ)) (lowCoarseS30_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS30_hz36 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B 0 (678232998312527 / 200000000000000000) (((2 : ℝ) * (√(184 : ℝ))) * x) := bmul (lowCoarseS30_hz35 hx hc) (lowCoarseS30_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS30_hz37 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B (7908179823291413 / 10000000000000000) (200764922307623063 / 250000000000000000) ((√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) - (((2 : ℝ) * (√(184 : ℝ))) * x)) := bsub (lowCoarseS30_hz34 hx hc) (lowCoarseS30_hz36 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS30_hz38 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B (7908179823291413 / 10000000000000000) (200764922307623063 / 250000000000000000) (ndm x c) := by
    convert (lowCoarseS30_hz37 hx hc) using 1 <;>
      norm_num [ndm] <;> ring

theorem lowCoarseS30_hz39 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B 1 (1003394039991562637 / 1000000000000000000) ((nap x)^2) := bsq (lowCoarseS30_hz6 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS30_hz40 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B 2 (1003394039991562637 / 500000000000000000) ((2 : ℝ) * ((nap x)^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS30_hz39 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS30_hz41 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B (625393081175134041 / 1000000000000000000) (322452432233487397 / 500000000000000000) ((ndm x c)^2) := bsq (lowCoarseS30_hz38 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS30_hz42 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B (677547567766512603 / 500000000000000000) (1381394998807991233 / 1000000000000000000) (((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) := bsub (lowCoarseS30_hz40 hx hc) (lowCoarseS30_hz41 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS30_hz43 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B (199322335762284863 / 200000000000000000) 1 ((nam x)^2) := bsq (lowCoarseS30_hz12 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS30_hz44 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B (199322335762284863 / 100000000000000000) 2 ((2 : ℝ) * ((nam x)^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS30_hz43 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS30_hz45 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B (677547567766512603 / 1000000000000000000) (346522880520391331 / 500000000000000000) ((((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) / ((2 : ℝ) * ((nam x)^2))) := bdiv (lowCoarseS30_hz42 hx hc) (lowCoarseS30_hz44 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS30_hz46 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B (677547567766512603 / 1000000000000000000) (346522880520391331 / 500000000000000000) (nc1 x c) := by
    convert (lowCoarseS30_hz45 hx hc) using 1 <;>
      norm_num [nc1] <;> ring

theorem lowCoarseS30_hz47 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B (352416382349566723 / 500000000000000000) (708830572026982599 / 1000000000000000000) (kdot c) := bkdot (lowCoarseS30_hz1 hx hc) (lowCoarseS30_hz13 hx hc).1 (lowCoarseS30_hz21 hx hc).2

theorem lowCoarseS30_hz48 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B (736957207268925799 / 1000000000000000000) (736957207268925801 / 1000000000000000000) (kdot ((677547567766512603 / 1000000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (438425096995566253 / 1000000000000000000)) (a := (413186652611842687 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (109606274248891563 / 250000000000000000)) (a := (82637330522368537 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS30_hz49 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B (743731630385186111 / 1000000000000000000) (743731630385186113 / 1000000000000000000) (kdot ((346522880520391331 / 500000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (207908630136037 / 488281250000000)) (a := (50318176708083319 / 125000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (17031874980744151 / 40000000000000000)) (a := (8050908273293331 / 20000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS30_hz50 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B (736957207268925799 / 1000000000000000000) (743731630385186113 / 1000000000000000000) (kdot (nc1 x c)) := bkdot (lowCoarseS30_hz46 hx hc) (lowCoarseS30_hz48 hx hc).1 (lowCoarseS30_hz49 hx hc).2

theorem lowCoarseS30_hz51 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B (9 / 25) (3721 / 10000) (c^2) := bsq (lowCoarseS30_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS30_hz52 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B (6279 / 10000) (16 / 25) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS30_hz51 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS30_hz53 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B (792401413426301253 / 1000000000000000000) (4 / 5) (√((1 : ℝ) - (c^2))) := bsqrt (lowCoarseS30_hz52 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS30_hz54 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B (558510478976760953 / 1000000000000000000) (3544152860134913 / 6250000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (lowCoarseS30_hz53 hx hc) (lowCoarseS30_hz47 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS30_hz55 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B (558510478976760953 / 1000000000000000000) (3544152860134913 / 6250000000000000) (npa c) := by
    convert (lowCoarseS30_hz54 hx hc) using 1 <;>
      norm_num [npa] <;> ring

theorem lowCoarseS30_hz56 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B (252229203719600809 / 1000000000000000000) (127323954473516269 / 500000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (lowCoarseS30_hz53 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS30_hz57 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B (422899658819480067 / 1000000000000000000) (216193324468229693 / 500000000000000000) (c * (kdot c)) := bmul (lowCoarseS30_hz1 hx hc) (lowCoarseS30_hz47 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS30_hz58 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B (-180157445216858577 / 1000000000000000000) (-168251749872447529 / 1000000000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (lowCoarseS30_hz56 hx hc) (lowCoarseS30_hz57 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS30_hz59 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B (-180157445216858577 / 1000000000000000000) (-168251749872447529 / 1000000000000000000) (npp c) := by
    convert (lowCoarseS30_hz58 hx hc) using 1 <;>
      norm_num [npp] <;> ring

theorem lowCoarseS30_hz60 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B 0 (23 / 4000) ((46 : ℝ) * x) := bmul (bpoint (46 : ℝ)) (lowCoarseS30_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS30_hz61 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B (9591663046625439083 / 1000000000000000000) (2399353261656359771 / 250000000000000000) ((√(92 : ℝ)) + ((46 : ℝ) * x)) := badd (lowCoarseS30_hz3 hx hc) (lowCoarseS30_hz60 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS30_hz62 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B (28774989139876317249 / 250000000000000000) (7198059784969079313 / 62500000000000000) ((12 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (bpoint (12 : ℝ)) (lowCoarseS30_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS30_hz63 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B 0 (14396119569938159 / 1000000000000000000) (((12 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS30_hz62 hx hc) (lowCoarseS30_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS30_hz64 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B 0 (14396119569938159 / 1000000000000000000) (nr1 x) := by
    convert (lowCoarseS30_hz63 hx hc) using 1 <;>
      norm_num [nr1] <;> ring

theorem lowCoarseS30_hz65 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B (9591663046625439083 / 125000000000000000) (2399353261656359771 / 31250000000000000) ((8 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (bpoint (8 : ℝ)) (lowCoarseS30_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS30_hz66 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B 0 (59983831541409 / 6250000000000000) (((8 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS30_hz65 hx hc) (lowCoarseS30_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS30_hz67 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B 0 (59983831541409 / 6250000000000000) (nrpp x) := by
    convert (lowCoarseS30_hz66 hx hc) using 1 <;>
      norm_num [nrpp] <;> ring

theorem lowCoarseS30_hz68 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B 0 (847791247890659 / 500000000000000000) (ne0 x) := by
    convert (lowCoarseS30_hz4 hx hc) using 1 <;>
      norm_num [ne0] <;> ring

theorem lowCoarseS30_hz69 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B (558510478976760953 / 1000000000000000000) (581460577191524239 / 1000000000000000000) ((npa c) + (nr1 x)) := badd (lowCoarseS30_hz55 hx hc) (lowCoarseS30_hz64 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS30_hz70 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B (558510478976760953 / 1000000000000000000) (291224087611442371 / 500000000000000000) (((npa c) + (nr1 x)) / (nam x)) := bdiv (lowCoarseS30_hz69 hx hc) (lowCoarseS30_hz12 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS30_hz71 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B (558510478976760953 / 1000000000000000000) (29207187885933303 / 50000000000000000) ((((npa c) + (nr1 x)) / (nam x)) + (ne0 x)) := badd (lowCoarseS30_hz70 hx hc) (lowCoarseS30_hz68 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS30_hz72 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B (558510478976760953 / 1000000000000000000) (29207187885933303 / 50000000000000000) (nlam x c) := by
    convert (lowCoarseS30_hz71 hx hc) using 1 <;>
      norm_num [nlam] <;> ring

theorem lowCoarseS30_hz73 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS30_hz74 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B 0 (59947894041409 / 100000000000000000) ((√(23 : ℝ)) * x) := bmul (lowCoarseS30_hz73 hx hc) (lowCoarseS30_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS30_hz75 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B (1 / 2) (50059947894041409 / 100000000000000000) (((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)) := badd (bpoint ((1 / 2) : ℝ)) (lowCoarseS30_hz74 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS30_hz76 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B (176776695296636881 / 250000000000000000) (353765274914177413 / 500000000000000000) (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) := bsqrt (lowCoarseS30_hz75 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS30_hz77 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B 0 (59947894041409 / 50000000000000000) ((√(92 : ℝ)) * x) := bmul (lowCoarseS30_hz3 hx hc) (lowCoarseS30_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS30_hz78 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B (176776695296636881 / 250000000000000000) (354364753854591503 / 500000000000000000) ((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x)) := badd (lowCoarseS30_hz76 hx hc) (lowCoarseS30_hz77 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS30_hz79 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B (499999999999999999 / 1000000000000000000) (251148757548850447 / 500000000000000000) (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2) := bsq (lowCoarseS30_hz78 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS30_hz80 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B (499999999999999999 / 125000000000000000) (251148757548850447 / 62500000000000000) ((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) := bmul (bpoint (8 : ℝ)) (lowCoarseS30_hz79 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS30_hz81 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B (7673330437300351251 / 200000000000000000) (1928302689874485209 / 50000000000000000) (((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (lowCoarseS30_hz80 hx hc) (lowCoarseS30_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS30_hz82 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B 0 (2410378362343107 / 500000000000000000) ((((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS30_hz81 hx hc) (lowCoarseS30_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS30_hz83 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B 0 (2410378362343107 / 500000000000000000) (nrs x) := by
    convert (lowCoarseS30_hz82 hx hc) using 1 <;>
      norm_num [nrs] <;> ring

theorem lowCoarseS30_hz84 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B (-180157445216858577 / 1000000000000000000) (-158654336825822089 / 1000000000000000000) ((npp c) + (nrpp x)) := badd (lowCoarseS30_hz59 hx hc) (lowCoarseS30_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS30_hz85 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B (-1674859880714551 / 12500000000000000) (-19831792103227761 / 250000000000000000) (if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) := bweaken (bfirst (lowCoarseS30_hz84 hx hc) (lowCoarseS30_hz50 hx hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem lowCoarseS30_hz86 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B (155966977563425469 / 500000000000000000) (68244785936336727 / 200000000000000000) ((nlam x c)^2) := bsq (lowCoarseS30_hz72 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS30_hz87 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B (114767676646579247 / 250000000000000000) (60039053362074703 / 125000000000000000) ((nc1 x c)^2) := bsq (lowCoarseS30_hz46 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS30_hz88 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B (64960946637925297 / 125000000000000000) (135232323353420753 / 250000000000000000) ((1 : ℝ) - ((nc1 x c)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS30_hz87 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS30_hz89 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B (360446796734068083 / 500000000000000000) (735478955112709539 / 1000000000000000000) (√((1 : ℝ) - ((nc1 x c)^2))) := bsqrt (lowCoarseS30_hz88 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS30_hz90 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B (452950803451888707 / 200000000000000000) (231057528225198559 / 100000000000000000) (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))) := bmul pi_mem (lowCoarseS30_hz89 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS30_hz91 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B (27000544628247451 / 200000000000000000) (12053368342213 / 80000000000000) (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2))))) := bdiv (lowCoarseS30_hz86 hx hc) (lowCoarseS30_hz90 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS30_hz92 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B (40557307362927 / 40000000000000000) (2229372995773483 / 31250000000000000) ((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) := badd (lowCoarseS30_hz85 hx hc) (lowCoarseS30_hz91 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS30_hz93 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B 0 (2875000000001 / 1000000000000000000) ((ne0 x)^2) := bsq (lowCoarseS30_hz68 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS30_hz94 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B (40557307362927 / 40000000000000000) (71342810864751457 / 1000000000000000000) (((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) + ((ne0 x)^2)) := badd (lowCoarseS30_hz92 hx hc) (lowCoarseS30_hz93 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS30_hz95 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B (40557307362927 / 40000000000000000) (76163567589437671 / 1000000000000000000) ((((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) + ((ne0 x)^2)) + (nrs x)) := badd (lowCoarseS30_hz94 hx hc) (lowCoarseS30_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS30_hz96 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B (40557307362927 / 40000000000000000) (76163567589437671 / 1000000000000000000) (nu x c) := by
    convert (lowCoarseS30_hz95 hx hc) using 1 <;>
      norm_num [nu] <;> ring

theorem lowCoarseS30_hz97 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B (-189754858263484017 / 1000000000000000000) (-168251749872447529 / 1000000000000000000) ((npp c) - (nrpp x)) := bsub (lowCoarseS30_hz59 hx hc) (lowCoarseS30_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS30_hz98 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B (-189754858263484017 / 1000000000000000000) (-168251749872447529 / 1000000000000000000) (min ((npp c) - (nrpp x)) (0 : ℝ)) := bweaken (bmin (lowCoarseS30_hz97 hx hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem lowCoarseS30_hz99 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B (-70563345054905437 / 500000000000000000) (-123994339704108773 / 1000000000000000000) ((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) := bmul (lowCoarseS30_hz50 hx hc) (lowCoarseS30_hz98 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS30_hz100 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B (-1129036520878487 / 8000000000000000) (-123994339704108773 / 1000000000000000000) (((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) - ((ne0 x)^2)) := bsub (lowCoarseS30_hz99 hx hc) (lowCoarseS30_hz93 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS30_hz101 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B (-145950321834497089 / 1000000000000000000) (-123994339704108773 / 1000000000000000000) ((((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) - ((ne0 x)^2)) - (nrs x)) := bsub (lowCoarseS30_hz100 hx hc) (lowCoarseS30_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS30_hz102 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B (-145950321834497089 / 1000000000000000000) (-123994339704108773 / 1000000000000000000) (nl x c) := by
    convert (lowCoarseS30_hz101 hx hc) using 1 <;>
      norm_num [nl] <;> ring

theorem lowCoarseS30_hz103 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B 0 (76163567589437671 / 1000000000000000000) |(nu x c)| := bweaken (babs (lowCoarseS30_hz96 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS30_hz104 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B 0 (145950321834497089 / 1000000000000000000) |(nl x c)| := bweaken (babs (lowCoarseS30_hz102 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS30_hz105 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B 0 (145950321834497089 / 1000000000000000000) (max |(nu x c)| |(nl x c)|) := bweaken (bmax (lowCoarseS30_hz103 hx hc) (lowCoarseS30_hz104 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS30_hz106 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) : B 0 (145950321834497089 / 1000000000000000000) (ns x c) := by
    convert (lowCoarseS30_hz105 hx hc) using 1 <;>
      norm_num [ns] <;> ring

theorem lowCoarseS30 {x c : ℝ}
    (hx : B 0 (1/8000) x) (hc : B (3 / 5) (61 / 100) c) :
    0 < nam x ∧ 0 ≤ ndm x c ∧ ndm x c ^ 2 ≤ 2 * nap x ^ 2 ∧ nc1 x c < 1 ∧
    0 ≤ npa c - nr1 x ∧ ne0 x ≤ (npa c - nr1 x) / nap x ∧ ns x c ≤ (1 / 5) := by
  refine ⟨lt_of_lt_of_le (by norm_num) (lowCoarseS30_hz12 hx hc).1,
    le_trans (by norm_num) (lowCoarseS30_hz38 hx hc).1, ?_,
    lt_of_le_of_lt (lowCoarseS30_hz46 hx hc).2 (by norm_num), ?_, ?_, (lowCoarseS30_hz106 hx hc).2.trans (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (lowCoarseS30_hz38 hx hc).1) (lowCoarseS30_hz38 hx hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) (lowCoarseS30_hz6 hx hc).1 2
    nlinarith only [h1,h2]
  · linarith only [(lowCoarseS30_hz55 hx hc).1,(lowCoarseS30_hz64 hx hc).2]
  · have hap : 0 < nap x := lt_of_lt_of_le (by norm_num) (lowCoarseS30_hz6 hx hc).1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul (lowCoarseS30_hz68 hx hc).2 (lowCoarseS30_hz6 hx hc).2 (le_trans (by norm_num) (lowCoarseS30_hz6 hx hc).1) (by norm_num)
    linarith only [h,(lowCoarseS30_hz55 hx hc).1,(lowCoarseS30_hz64 hx hc).2]

theorem lowCoarseS31_hz0 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B 0 (1 / 8000) x := hx

theorem lowCoarseS31_hz1 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B (61 / 100) (31 / 50) c := hc

theorem lowCoarseS31_hz2 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B (6782329983125268139 / 500000000000000000) (13564659966250536279 / 1000000000000000000) (√(184 : ℝ)) := bsqrt (bpoint (184 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS31_hz3 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B (9591663046625439083 / 1000000000000000000) (2397915761656359771 / 250000000000000000) (√(92 : ℝ)) := bsqrt (bpoint (92 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS31_hz4 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B 0 (847791247890659 / 500000000000000000) ((√(184 : ℝ)) * x) := bmul (lowCoarseS31_hz2 hx hc) (lowCoarseS31_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS31_hz5 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B 1 (500847791247890659 / 500000000000000000) ((1 : ℝ) + ((√(184 : ℝ)) * x)) := badd (bpoint (1 : ℝ)) (lowCoarseS31_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS31_hz6 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B 1 (500847791247890659 / 500000000000000000) (nap x) := by
    convert (lowCoarseS31_hz5 hx hc) using 1 <;>
      norm_num [nap] <;> ring

theorem lowCoarseS31_hz7 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B 0 (1 / 64000000) (x^2) := bsq (lowCoarseS31_hz0 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS31_hz8 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B 0 (1 / 32000000) ((2 : ℝ) * (x^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS31_hz7 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS31_hz9 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B (31999999 / 32000000) 1 ((1 : ℝ) - ((2 : ℝ) * (x^2))) := bsub (bpoint (1 : ℝ)) (lowCoarseS31_hz8 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS31_hz10 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B (999999984374999877 / 1000000000000000000) 1 (√((1 : ℝ) - ((2 : ℝ) * (x^2)))) := bsqrt (lowCoarseS31_hz9 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS31_hz11 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B (998304401879218559 / 1000000000000000000) 1 ((√((1 : ℝ) - ((2 : ℝ) * (x^2)))) - ((√(184 : ℝ)) * x)) := bsub (lowCoarseS31_hz10 hx hc) (lowCoarseS31_hz4 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS31_hz12 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B (998304401879218559 / 1000000000000000000) 1 (nam x) := by
    convert (lowCoarseS31_hz11 hx hc) using 1 <;>
      norm_num [nam] <;> ring

theorem lowCoarseS31_hz13 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B (28353222881079303 / 40000000000000000) (708830572026982599 / 1000000000000000000) (kdot ((61 / 100))) := by
    constructor
    · apply bkdot_lower (q := (492174790948013201 / 1000000000000000000)) (a := (457367867934986991 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (1230436977370033 / 2500000000000000)) (a := (114341966983746739 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS31_hz14 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B (3721 / 10000) (3721 / 10000) (((61 / 100) : ℝ)^2) := bsq (bpoint ((61 / 100) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS31_hz15 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B (6279 / 10000) (6279 / 10000) ((1 : ℝ) - (((61 / 100) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS31_hz14 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS31_hz16 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B (792401413426301253 / 1000000000000000000) (396200706713150627 / 500000000000000000) (√((1 : ℝ) - (((61 / 100) : ℝ)^2))) := bsqrt (lowCoarseS31_hz15 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS31_hz17 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B (252229203719600809 / 1000000000000000000) (25222920371960081 / 100000000000000000) ((√((1 : ℝ) - (((61 / 100) : ℝ)^2))) / Real.pi) := bdiv (lowCoarseS31_hz16 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS31_hz18 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B (43238664893645937 / 100000000000000000) (216193324468229693 / 500000000000000000) (((61 / 100) : ℝ) * (kdot ((61 / 100)))) := bmul (bpoint ((61 / 100) : ℝ)) (lowCoarseS31_hz13 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS31_hz19 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B (684615852656060179 / 1000000000000000000) (171153963164015049 / 250000000000000000) (((√((1 : ℝ) - (((61 / 100) : ℝ)^2))) / Real.pi) + (((61 / 100) : ℝ) * (kdot ((61 / 100))))) := badd (lowCoarseS31_hz17 hx hc) (lowCoarseS31_hz18 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS31_hz20 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B (684615852656060179 / 1000000000000000000) (171153963164015049 / 250000000000000000) (kappa ((61 / 100))) := by rw [kappa_eq]; exact (lowCoarseS31_hz19 hx hc)

theorem lowCoarseS31_hz21 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B (11138553339727929 / 15625000000000000) (712867413742587469 / 1000000000000000000) (kdot ((31 / 50))) := by
    constructor
    · apply bkdot_lower (q := (484322104837852617 / 1000000000000000000)) (a := (90205362359252487 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (60540263104731577 / 125000000000000000)) (a := (451026811796262417 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS31_hz22 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B (961 / 2500) (961 / 2500) (((31 / 50) : ℝ)^2) := bsq (bpoint ((31 / 50) : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS31_hz23 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B (1539 / 2500) (1539 / 2500) ((1 : ℝ) - (((31 / 50) : ℝ)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS31_hz22 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS31_hz24 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B (784601809837321239 / 1000000000000000000) (19615045245933031 / 25000000000000000) (√((1 : ℝ) - (((31 / 50) : ℝ)^2))) := bsqrt (lowCoarseS31_hz23 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS31_hz25 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B (49949302557782779 / 200000000000000000) (31218314098614237 / 125000000000000000) ((√((1 : ℝ) - (((31 / 50) : ℝ)^2))) / Real.pi) := bdiv (lowCoarseS31_hz24 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS31_hz26 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B (220988898260202111 / 500000000000000000) (441977796520404231 / 1000000000000000000) (((31 / 50) : ℝ) * (kdot ((31 / 50)))) := bmul (bpoint ((31 / 50) : ℝ)) (lowCoarseS31_hz21 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS31_hz27 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B (691724309309318117 / 1000000000000000000) (691724309309318127 / 1000000000000000000) (((√((1 : ℝ) - (((31 / 50) : ℝ)^2))) / Real.pi) + (((31 / 50) : ℝ) * (kdot ((31 / 50))))) := badd (lowCoarseS31_hz25 hx hc) (lowCoarseS31_hz26 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS31_hz28 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B (691724309309318117 / 1000000000000000000) (691724309309318127 / 1000000000000000000) (kappa ((31 / 50))) := by rw [kappa_eq]; exact (lowCoarseS31_hz27 hx hc)

theorem lowCoarseS31_hz29 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B (684615852656060179 / 1000000000000000000) (691724309309318127 / 1000000000000000000) (kappa c) := bkappa (lowCoarseS31_hz1 hx hc) (by norm_num) (by norm_num) (lowCoarseS31_hz20 hx hc).1 (lowCoarseS31_hz28 hx hc).2

theorem lowCoarseS31_hz30 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B (308275690690681873 / 1000000000000000000) (315384147343939821 / 1000000000000000000) ((1 : ℝ) - (kappa c)) := bsub (bpoint (1 : ℝ)) (lowCoarseS31_hz29 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS31_hz31 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B (308275690690681873 / 500000000000000000) (315384147343939821 / 500000000000000000) ((2 : ℝ) * ((1 : ℝ) - (kappa c))) := bmul (bpoint (2 : ℝ)) (lowCoarseS31_hz30 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS31_hz32 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B 0 (1 / 8000000) ((8 : ℝ) * (x^2)) := bmul (bpoint (8 : ℝ)) (lowCoarseS31_hz7 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS31_hz33 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B (308275628190681873 / 500000000000000000) (315384147343939821 / 500000000000000000) (((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2))) := bsub (lowCoarseS31_hz31 hx hc) (lowCoarseS31_hz32 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS31_hz34 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B (392603889557071169 / 500000000000000000) (397104613007668183 / 500000000000000000) (√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) := bsqrt (lowCoarseS31_hz33 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS31_hz35 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B (6782329983125268139 / 250000000000000000) (13564659966250536279 / 500000000000000000) ((2 : ℝ) * (√(184 : ℝ))) := bmul (bpoint (2 : ℝ)) (lowCoarseS31_hz2 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS31_hz36 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B 0 (678232998312527 / 200000000000000000) (((2 : ℝ) * (√(184 : ℝ))) * x) := bmul (lowCoarseS31_hz35 hx hc) (lowCoarseS31_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS31_hz37 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B (781816614122579703 / 1000000000000000000) (397104613007668183 / 500000000000000000) ((√(((2 : ℝ) * ((1 : ℝ) - (kappa c))) - ((8 : ℝ) * (x^2)))) - (((2 : ℝ) * (√(184 : ℝ))) * x)) := bsub (lowCoarseS31_hz34 hx hc) (lowCoarseS31_hz36 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS31_hz38 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B (781816614122579703 / 1000000000000000000) (397104613007668183 / 500000000000000000) (ndm x c) := by
    convert (lowCoarseS31_hz37 hx hc) using 1 <;>
      norm_num [ndm] <;> ring

theorem lowCoarseS31_hz39 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B 1 (1003394039991562637 / 1000000000000000000) ((nap x)^2) := bsq (lowCoarseS31_hz6 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS31_hz40 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B 2 (1003394039991562637 / 500000000000000000) ((2 : ℝ) * ((nap x)^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS31_hz39 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS31_hz41 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B (152809304529523673 / 250000000000000000) (630768294687879643 / 1000000000000000000) ((ndm x c)^2) := bsq (lowCoarseS31_hz38 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS31_hz42 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B (1369231705312120357 / 1000000000000000000) (697775430932515291 / 500000000000000000) (((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) := bsub (lowCoarseS31_hz40 hx hc) (lowCoarseS31_hz41 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS31_hz43 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B (199322335762284863 / 200000000000000000) 1 ((nam x)^2) := bsq (lowCoarseS31_hz12 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS31_hz44 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B (199322335762284863 / 100000000000000000) 2 ((2 : ℝ) * ((nam x)^2)) := bmul (bpoint (2 : ℝ)) (lowCoarseS31_hz43 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS31_hz45 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B (342307926328030089 / 500000000000000000) (350073878205347689 / 500000000000000000) ((((2 : ℝ) * ((nap x)^2)) - ((ndm x c)^2)) / ((2 : ℝ) * ((nam x)^2))) := bdiv (lowCoarseS31_hz42 hx hc) (lowCoarseS31_hz44 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS31_hz46 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B (342307926328030089 / 500000000000000000) (350073878205347689 / 500000000000000000) (nc1 x c) := by
    convert (lowCoarseS31_hz45 hx hc) using 1 <;>
      norm_num [nc1] <;> ring

theorem lowCoarseS31_hz47 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B (28353222881079303 / 40000000000000000) (712867413742587469 / 1000000000000000000) (kdot c) := bkdot (lowCoarseS31_hz1 hx hc) (lowCoarseS31_hz13 hx hc).1 (lowCoarseS31_hz21 hx hc).2

theorem lowCoarseS31_hz48 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B (370015010064376663 / 500000000000000000) (46251876258047083 / 62500000000000000) (kdot ((342307926328030089 / 500000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (432682657412560261 / 1000000000000000000)) (a := (204179944729348743 / 500000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (21634132870628013 / 50000000000000000)) (a := (102089972364674371 / 250000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS31_hz49 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B (74688255400311393 / 100000000000000000) (746882554003113933 / 1000000000000000000) (kdot ((350073878205347689 / 500000000000000000))) := by
    constructor
    · apply bkdot_lower (q := (419962312059701591 / 1000000000000000000)) (a := (397595954419614247 / 1000000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]
    · apply bkdot_upper (q := (41996231205970159 / 100000000000000000)) (a := (79519190883922849 / 200000000000000000)) <;>
        norm_num [atanSum, Finset.sum_range_succ]

theorem lowCoarseS31_hz50 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B (370015010064376663 / 500000000000000000) (746882554003113933 / 1000000000000000000) (kdot (nc1 x c)) := bkdot (lowCoarseS31_hz46 hx hc) (lowCoarseS31_hz48 hx hc).1 (lowCoarseS31_hz49 hx hc).2

theorem lowCoarseS31_hz51 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B (3721 / 10000) (961 / 2500) (c^2) := bsq (lowCoarseS31_hz1 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS31_hz52 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B (1539 / 2500) (6279 / 10000) ((1 : ℝ) - (c^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS31_hz51 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS31_hz53 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B (784601809837321239 / 1000000000000000000) (396200706713150627 / 500000000000000000) (√((1 : ℝ) - (c^2))) := bsqrt (lowCoarseS31_hz52 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS31_hz54 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B (556149749680394217 / 1000000000000000000) (282438573117589101 / 500000000000000000) ((√((1 : ℝ) - (c^2))) * (kdot c)) := bmul (lowCoarseS31_hz53 hx hc) (lowCoarseS31_hz47 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS31_hz55 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B (556149749680394217 / 1000000000000000000) (282438573117589101 / 500000000000000000) (npa c) := by
    convert (lowCoarseS31_hz54 hx hc) using 1 <;>
      norm_num [npa] <;> ring

theorem lowCoarseS31_hz56 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B (49949302557782779 / 200000000000000000) (25222920371960081 / 100000000000000000) ((√((1 : ℝ) - (c^2))) / Real.pi) := bdiv (lowCoarseS31_hz53 hx hc) pi_mem (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS31_hz57 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B (43238664893645937 / 100000000000000000) (441977796520404231 / 1000000000000000000) (c * (kdot c)) := bmul (lowCoarseS31_hz1 hx hc) (lowCoarseS31_hz47 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS31_hz58 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B (-6007227616609073 / 31250000000000000) (-562992016302683 / 3125000000000000) (((√((1 : ℝ) - (c^2))) / Real.pi) - (c * (kdot c))) := bsub (lowCoarseS31_hz56 hx hc) (lowCoarseS31_hz57 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS31_hz59 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B (-6007227616609073 / 31250000000000000) (-562992016302683 / 3125000000000000) (npp c) := by
    convert (lowCoarseS31_hz58 hx hc) using 1 <;>
      norm_num [npp] <;> ring

theorem lowCoarseS31_hz60 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B 0 (23 / 4000) ((46 : ℝ) * x) := bmul (bpoint (46 : ℝ)) (lowCoarseS31_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS31_hz61 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B (9591663046625439083 / 1000000000000000000) (2399353261656359771 / 250000000000000000) ((√(92 : ℝ)) + ((46 : ℝ) * x)) := badd (lowCoarseS31_hz3 hx hc) (lowCoarseS31_hz60 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS31_hz62 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B (28774989139876317249 / 250000000000000000) (7198059784969079313 / 62500000000000000) ((12 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (bpoint (12 : ℝ)) (lowCoarseS31_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS31_hz63 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B 0 (14396119569938159 / 1000000000000000000) (((12 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS31_hz62 hx hc) (lowCoarseS31_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS31_hz64 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B 0 (14396119569938159 / 1000000000000000000) (nr1 x) := by
    convert (lowCoarseS31_hz63 hx hc) using 1 <;>
      norm_num [nr1] <;> ring

theorem lowCoarseS31_hz65 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B (9591663046625439083 / 125000000000000000) (2399353261656359771 / 31250000000000000) ((8 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (bpoint (8 : ℝ)) (lowCoarseS31_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS31_hz66 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B 0 (59983831541409 / 6250000000000000) (((8 : ℝ) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS31_hz65 hx hc) (lowCoarseS31_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS31_hz67 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B 0 (59983831541409 / 6250000000000000) (nrpp x) := by
    convert (lowCoarseS31_hz66 hx hc) using 1 <;>
      norm_num [nrpp] <;> ring

theorem lowCoarseS31_hz68 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B 0 (847791247890659 / 500000000000000000) (ne0 x) := by
    convert (lowCoarseS31_hz4 hx hc) using 1 <;>
      norm_num [ne0] <;> ring

theorem lowCoarseS31_hz69 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B (556149749680394217 / 1000000000000000000) (579273265805116361 / 1000000000000000000) ((npa c) + (nr1 x)) := badd (lowCoarseS31_hz55 hx hc) (lowCoarseS31_hz64 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS31_hz70 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B (556149749680394217 / 1000000000000000000) (580257148736083261 / 1000000000000000000) (((npa c) + (nr1 x)) / (nam x)) := bdiv (lowCoarseS31_hz69 hx hc) (lowCoarseS31_hz12 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS31_hz71 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B (556149749680394217 / 1000000000000000000) (581952731231864579 / 1000000000000000000) ((((npa c) + (nr1 x)) / (nam x)) + (ne0 x)) := badd (lowCoarseS31_hz70 hx hc) (lowCoarseS31_hz68 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS31_hz72 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B (556149749680394217 / 1000000000000000000) (581952731231864579 / 1000000000000000000) (nlam x c) := by
    convert (lowCoarseS31_hz71 hx hc) using 1 <;>
      norm_num [nlam] <;> ring

theorem lowCoarseS31_hz73 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B (4795831523312719541 / 1000000000000000000) (2397915761656359771 / 500000000000000000) (√(23 : ℝ)) := bsqrt (bpoint (23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS31_hz74 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B 0 (59947894041409 / 100000000000000000) ((√(23 : ℝ)) * x) := bmul (lowCoarseS31_hz73 hx hc) (lowCoarseS31_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS31_hz75 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B (1 / 2) (50059947894041409 / 100000000000000000) (((1 / 2) : ℝ) + ((√(23 : ℝ)) * x)) := badd (bpoint ((1 / 2) : ℝ)) (lowCoarseS31_hz74 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS31_hz76 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B (176776695296636881 / 250000000000000000) (353765274914177413 / 500000000000000000) (√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) := bsqrt (lowCoarseS31_hz75 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS31_hz77 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B 0 (59947894041409 / 50000000000000000) ((√(92 : ℝ)) * x) := bmul (lowCoarseS31_hz3 hx hc) (lowCoarseS31_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS31_hz78 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B (176776695296636881 / 250000000000000000) (354364753854591503 / 500000000000000000) ((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x)) := badd (lowCoarseS31_hz76 hx hc) (lowCoarseS31_hz77 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS31_hz79 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B (499999999999999999 / 1000000000000000000) (251148757548850447 / 500000000000000000) (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2) := bsq (lowCoarseS31_hz78 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS31_hz80 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B (499999999999999999 / 125000000000000000) (251148757548850447 / 62500000000000000) ((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) := bmul (bpoint (8 : ℝ)) (lowCoarseS31_hz79 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS31_hz81 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B (7673330437300351251 / 200000000000000000) (1928302689874485209 / 50000000000000000) (((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) := bmul (lowCoarseS31_hz80 hx hc) (lowCoarseS31_hz61 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS31_hz82 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B 0 (2410378362343107 / 500000000000000000) ((((8 : ℝ) * (((√(((1 / 2) : ℝ) + ((√(23 : ℝ)) * x))) + ((√(92 : ℝ)) * x))^2)) * ((√(92 : ℝ)) + ((46 : ℝ) * x))) * x) := bmul (lowCoarseS31_hz81 hx hc) (lowCoarseS31_hz0 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS31_hz83 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B 0 (2410378362343107 / 500000000000000000) (nrs x) := by
    convert (lowCoarseS31_hz82 hx hc) using 1 <;>
      norm_num [nrs] <;> ring

theorem lowCoarseS31_hz84 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B (-6007227616609073 / 31250000000000000) (-1066000201063957 / 6250000000000000) ((npp c) + (nrpp x)) := badd (lowCoarseS31_hz59 hx hc) (lowCoarseS31_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS31_hz85 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B (-35893548038168187 / 250000000000000000) (-1066000201063957 / 12500000000000000) (if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) := bweaken (bfirst (lowCoarseS31_hz84 hx hc) (lowCoarseS31_hz50 hx hc) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem lowCoarseS31_hz86 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B (309302544069565147 / 1000000000000000000) (338668981388226811 / 1000000000000000000) ((nlam x c)^2) := bsq (lowCoarseS31_hz72 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS31_hz87 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B (468698865707984299 / 1000000000000000000) (490206880806930431 / 1000000000000000000) ((nc1 x c)^2) := bsq (lowCoarseS31_hz46 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS31_hz88 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B (509793119193069569 / 1000000000000000000) (531301134292015701 / 1000000000000000000) ((1 : ℝ) - ((nc1 x c)^2)) := bsub (bpoint (1 : ℝ)) (lowCoarseS31_hz87 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS31_hz89 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B (713997982625349977 / 1000000000000000000) (36445203192327509 / 50000000000000000) (√((1 : ℝ) - ((nc1 x c)^2))) := bsqrt (lowCoarseS31_hz88 hx hc) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS31_hz90 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B (2243090816893732321 / 1000000000000000000) (1144959826076033827 / 500000000000000000) (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))) := bmul pi_mem (lowCoarseS31_hz89 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS31_hz91 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B (135071352297833881 / 1000000000000000000) (150983178584459179 / 1000000000000000000) (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2))))) := bdiv (lowCoarseS31_hz86 hx hc) (lowCoarseS31_hz90 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS31_hz92 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B (-8502839854838867 / 1000000000000000000) (65703162499342619 / 1000000000000000000) ((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) := badd (lowCoarseS31_hz85 hx hc) (lowCoarseS31_hz91 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS31_hz93 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B 0 (2875000000001 / 1000000000000000000) ((ne0 x)^2) := bsq (lowCoarseS31_hz68 hx hc) (by norm_num) (by norm_num) (by norm_num)

theorem lowCoarseS31_hz94 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B (-8502839854838867 / 1000000000000000000) (3285301874967131 / 50000000000000000) (((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) + ((ne0 x)^2)) := badd (lowCoarseS31_hz92 hx hc) (lowCoarseS31_hz93 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS31_hz95 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B (-8502839854838867 / 1000000000000000000) (35263397112014417 / 500000000000000000) ((((if 0 ≤ ((npp c) + (nrpp x)) then (kdot (nc1 x c)) * ((npp c) + (nrpp x)) else ((npp c) + (nrpp x)) / 2) + (((nlam x c)^2) / (Real.pi * (√((1 : ℝ) - ((nc1 x c)^2)))))) + ((ne0 x)^2)) + (nrs x)) := badd (lowCoarseS31_hz94 hx hc) (lowCoarseS31_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS31_hz96 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B (-8502839854838867 / 1000000000000000000) (35263397112014417 / 500000000000000000) (nu x c) := by
    convert (lowCoarseS31_hz95 hx hc) using 1 <;>
      norm_num [nu] <;> ring

theorem lowCoarseS31_hz97 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B (-3153573387158059 / 15625000000000000) (-562992016302683 / 3125000000000000) ((npp c) - (nrpp x)) := bsub (lowCoarseS31_hz59 hx hc) (lowCoarseS31_hz67 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS31_hz98 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B (-3153573387158059 / 15625000000000000) (-562992016302683 / 3125000000000000) (min ((npp c) - (nrpp x)) (0 : ℝ)) := bweaken (bmin (lowCoarseS31_hz97 hx hc) (bpoint (0 : ℝ))) (by norm_num) (by norm_num)

theorem lowCoarseS31_hz99 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B (-37685583130189791 / 250000000000000000) (-66660958905088307 / 500000000000000000) ((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) := bmul (lowCoarseS31_hz50 hx hc) (lowCoarseS31_hz98 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS31_hz100 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B (-30149041504151833 / 200000000000000000) (-66660958905088307 / 500000000000000000) (((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) - ((ne0 x)^2)) := bsub (lowCoarseS31_hz99 hx hc) (lowCoarseS31_hz93 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS31_hz101 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B (-155565964245445379 / 1000000000000000000) (-66660958905088307 / 500000000000000000) ((((kdot (nc1 x c)) * (min ((npp c) - (nrpp x)) (0 : ℝ))) - ((ne0 x)^2)) - (nrs x)) := bsub (lowCoarseS31_hz100 hx hc) (lowCoarseS31_hz83 hx hc) (by norm_num) (by norm_num)

theorem lowCoarseS31_hz102 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B (-155565964245445379 / 1000000000000000000) (-66660958905088307 / 500000000000000000) (nl x c) := by
    convert (lowCoarseS31_hz101 hx hc) using 1 <;>
      norm_num [nl] <;> ring

theorem lowCoarseS31_hz103 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B 0 (35263397112014417 / 500000000000000000) |(nu x c)| := bweaken (babs (lowCoarseS31_hz96 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS31_hz104 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B 0 (155565964245445379 / 1000000000000000000) |(nl x c)| := bweaken (babs (lowCoarseS31_hz102 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS31_hz105 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B 0 (155565964245445379 / 1000000000000000000) (max |(nu x c)| |(nl x c)|) := bweaken (bmax (lowCoarseS31_hz103 hx hc) (lowCoarseS31_hz104 hx hc)) (by norm_num) (by norm_num)

theorem lowCoarseS31_hz106 {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) : B 0 (155565964245445379 / 1000000000000000000) (ns x c) := by
    convert (lowCoarseS31_hz105 hx hc) using 1 <;>
      norm_num [ns] <;> ring

theorem lowCoarseS31 {x c : ℝ}
    (hx : B 0 (1/8000) x) (hc : B (61 / 100) (31 / 50) c) :
    0 < nam x ∧ 0 ≤ ndm x c ∧ ndm x c ^ 2 ≤ 2 * nap x ^ 2 ∧ nc1 x c < 1 ∧
    0 ≤ npa c - nr1 x ∧ ne0 x ≤ (npa c - nr1 x) / nap x ∧ ns x c ≤ (1 / 5) := by
  refine ⟨lt_of_lt_of_le (by norm_num) (lowCoarseS31_hz12 hx hc).1,
    le_trans (by norm_num) (lowCoarseS31_hz38 hx hc).1, ?_,
    lt_of_le_of_lt (lowCoarseS31_hz46 hx hc).2 (by norm_num), ?_, ?_, (lowCoarseS31_hz106 hx hc).2.trans (by norm_num)⟩
  · have h1 := pow_le_pow_left₀ (le_trans (by norm_num) (lowCoarseS31_hz38 hx hc).1) (lowCoarseS31_hz38 hx hc).2 2
    have h2 := pow_le_pow_left₀ (by norm_num) (lowCoarseS31_hz6 hx hc).1 2
    nlinarith only [h1,h2]
  · linarith only [(lowCoarseS31_hz55 hx hc).1,(lowCoarseS31_hz64 hx hc).2]
  · have hap : 0 < nap x := lt_of_lt_of_le (by norm_num) (lowCoarseS31_hz6 hx hc).1
    rw [le_div_iff₀ hap]
    have h := mul_le_mul (lowCoarseS31_hz68 hx hc).2 (lowCoarseS31_hz6 hx hc).2 (le_trans (by norm_num) (lowCoarseS31_hz6 hx hc).1) (by norm_num)
    linarith only [h,(lowCoarseS31_hz55 hx hc).1,(lowCoarseS31_hz64 hx hc).2]

end BstLean.BlueprintLow
